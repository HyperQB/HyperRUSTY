#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-60}  # Please adjust this timeout value as needed for your environment. Default is 60 second for quick testing; increase as needed for longer runs.


# Detect timeout binary safely (avoid unbound variable errors)
if command -v gtimeout >/dev/null 2>&1; then
  TIMEOUT_BIN="gtimeout"
elif command -v timeout >/dev/null 2>&1; then
  TIMEOUT_BIN="timeout"
else
  TIMEOUT_BIN=""   # fallback: no timeout available
fi

# ---- Paths for results/logs ----
FOLDER="benchmarks/async/"
RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/table6(ahltl)_runtimes.csv"
RAW_CSV="${RESULTS_DIR}/table6(ahltl)_runtimes_long.csv"
MD="${RESULTS_DIR}/table6(ahltl)_runtimes.md"

CARGO_BIN=${CARGO_BIN:-target/release/HyperRUSTY}
if [[ ! -x "$CARGO_BIN" ]]; then
  echo "Building HyperQB (release)…"
  cargo build --release
fi

# Fresh start: recreate logs dir and reset CSV/MD
mkdir -p "$RESULTS_DIR"
# Remove only files inside logs/, then recreate (extra safety)
if [[ -d "$LOG_DIR" ]]; then
  find "$LOG_DIR" -type f -name '*.log' -delete || true
else
  mkdir -p "$LOG_DIR"
fi

# Initialize CSV (once per script run)
# echo "timestamp,case,variant,exit,real_s,user_s,sys_s,max_rss_kb,log" > "$CSV"
echo "Benchmark,Encoding(SMT),Solve(SMT),Total(SMT),Encoding(QBF),Solve(QBF),Total(QBF)" > "$CSV"
echo "Benchmark,Variant,Encoding,Solving,Total" > "$RAW_CSV"

fmt_time() {
    local v="${1:-NA}"

    case "$v" in
        "" )
            printf "NA"
            ;;
        NA|TO|MO|ERR )
            printf "%s" "$v"
            ;;
        *[!0-9.eE+-]* )
            printf "%s" "$v"
            ;;
        * )
            awk -v x="$v" 'BEGIN { printf "%.3f", x }'
            ;;
    esac
}

is_ge_timeout() {
    local value="${1:-0}"
    awk -v x="$value" -v t="$TIMEOUT_SEC" '
      BEGIN {
        if (x + 0 >= t + 0) exit 0
        exit 1
      }
    '
}

# ---- Timing helper ----
time_run() {
    local case_name="$1"; shift
    local variant="$1"; shift

    local stamp log_base log_file tmp
    stamp="$(date -Iseconds)"
    log_base="${case_name// /_}_${variant// /_}"
    log_file="${LOG_DIR}/${log_base}.log"
    tmp="$(mktemp)"

    local cmd="$*"
    local exit_code=0

    # Run with/without timeout, capture output to log and preserve exit code
    set +e
    if [[ -n "${TIMEOUT_BIN:-}" ]]; then
        "$TIMEOUT_BIN" "$TIMEOUT_SEC" bash -c \
          "gtime -f '%e,%U,%S,%M' -o '$tmp' bash -c \"$cmd\"" \
          2>&1 | tee -a "$log_file"
        exit_code=${PIPESTATUS[0]}
    else
        gtime -f "%e,%U,%S,%M" -o "$tmp" bash -c "$cmd" \
          2>&1 | tee -a "$log_file"
        exit_code=${PIPESTATUS[0]}
    fi
    set -e

    # Parse timing (may be empty if killed early)
    IFS=, read -r real_s user_s sys_s max_rss_kb < "$tmp" || true
    if [[ -z "${real_s:-}" ]]; then
        real_s=0.0
        user_s=0.0
        sys_s=0.0
        max_rss_kb=0
    fi
    rm -f "$tmp"

    # Determine status from log.
    local status="ERROR"

    real_s=${real_s:-0.0}
    case "$real_s" in
        ''|*[!0-9.eE+-]*) real_s=0.0 ;;
    esac

    if [[ -n "${TIMEOUT_BIN:-}" && $exit_code -eq 124 ]]; then
        echo "[TIMEOUT] $case_name ($variant) exceeded ${TIMEOUT_SEC}s." | tee -a "$log_file"
        real_s="${TIMEOUT_SEC}"
        status="TIMEOUT"

    elif grep -qi '\[TIMEOUT\]' "$log_file"; then
        real_s="${TIMEOUT_SEC}"
        status="TIMEOUT"

    elif [[ -n "${TIMEOUT_BIN:-}" && $exit_code -eq 137 ]]; then
        echo "[KILLED]  $case_name ($variant) was killed by SIGKILL (exit 137, likely out-of-memory)." | tee -a "$log_file"
        status="MEMOUT"

    elif grep -qiE '\[KILLED\]|out-of-memory|out of memory|SIGKILL|exit 137|Killed' "$log_file"; then
        status="MEMOUT"

    elif is_ge_timeout "$real_s"; then
        real_s="${TIMEOUT_SEC}"
        status="TIMEOUT"

    elif grep -qiE '(^|[ =])ERROR([ =]|$)|Unexpected exit code|=========== ERROR ===========' "$log_file"; then
        status="ERROR"

    else
        if grep -qiwo 'UNSAT' "$log_file"; then
            status="UNSAT"
        elif grep -qiwo 'SAT' "$log_file"; then
            status="SAT"
        elif grep -qiwo 'UNKNOWN' "$log_file"; then
            status="UNKNOWN"
        elif [[ $exit_code -ne 0 ]]; then
            status="ERROR"
        else
            status="ERROR"
        fi
    fi

    # execution finished.
    # Extract benchmark-reported timing values from the log.

    local model_creation_s encoding_time_s smt_solve_s qbf_solve_s
    local encoding_s solving_s total_s forced_cell

    forced_cell=""

    if [[ "$status" == "TIMEOUT" ]]; then
        forced_cell="TO"
    elif [[ "$status" == "MEMOUT" ]]; then
        forced_cell="MO"
    elif [[ "$status" == "ERROR" ]]; then
        forced_cell="ERR"
    fi

    model_creation_s="$(
      awk -F': *' '
        /^Model Creation Time:/ { v = $2 }
        END { if (v != "") print v }
      ' "$log_file"
    )"

    encoding_time_s="$(
      awk -F': *' '
        /^Encoding Time:/ { v = $2 }
        END { if (v != "") print v }
      ' "$log_file"
    )"

    smt_solve_s="$(
      awk -F': *' '
        /^Solve Time:/ { v = $2 }
        END { if (v != "") print v }
      ' "$log_file"
    )"

    qbf_solve_s="$(
      awk -F': *' '
        /^QBF Build & Solving Time:/ {
          split($2, a, " ")
          v = a[1]
        }
        END { if (v != "") print v }
      ' "$log_file"
    )"

    if [[ -n "$forced_cell" ]]; then
        encoding_s="$forced_cell"
        solving_s="$forced_cell"
        total_s="$forced_cell"
    else
        total_s="$(fmt_time "$real_s")"

        case "$variant" in
          SMT|smt)
            if [[ -n "${model_creation_s:-}" && -n "${encoding_time_s:-}" ]]; then
                encoding_s="$(
                  awk -v m="$model_creation_s" -v e="$encoding_time_s" \
                    'BEGIN { printf "%.3f", m + e }'
                )"
            else
                encoding_s="NA"
            fi

            if [[ -n "${smt_solve_s:-}" ]]; then
                solving_s="$(fmt_time "$smt_solve_s")"
            else
                solving_s="NA"
            fi
            ;;

          QBF|qbf)
            if [[ -n "${model_creation_s:-}" ]]; then
                encoding_s="$(fmt_time "$model_creation_s")"
            else
                encoding_s="NA"
            fi

            if [[ -n "${qbf_solve_s:-}" ]]; then
                solving_s="$(fmt_time "$qbf_solve_s")"
            else
                solving_s="NA"
            fi
            ;;

          *)
            encoding_s="NA"
            solving_s="NA"
            ;;
        esac
    fi

    printf "%s,%s,%s,%s,%s\n" \
        "$case_name" "$variant" "$encoding_s" "$solving_s" "$total_s" >> "$RAW_CSV"
    # Append one row to CSV (full info)
    # printf "%s,%s,%s,%s,%s,%.3f,%.3f,%.3f,%s,%s\n" \
    # "$stamp" "$case_name" "$variant" "$status" "$exit_code" \
    # "$real_s" "$user_s" "$sys_s" "$max_rss_kb" "$log_file" >> "$CSV"

}

# ---- Pretty-print table (plain + markdown) ----
render_tables() {
  echo
  echo "=== Table 6 runtimes (A-HLTL cases) ==="

  awk -F, '
    BEGIN {
      OFS = ","
      print "Benchmark","Encoding(SMT)","Solve(SMT)","Total(SMT)","Encoding(QBF)","Solve(QBF)","Total(QBF)"
    }

    NR == 1 { next }

    {
      benchmark = $1
      variant = toupper($2)

      if (!(benchmark in seen)) {
        seen[benchmark] = 1
        order[++n] = benchmark
      }

      if (variant == "SMT") {
        enc_smt[benchmark] = $3
        solve_smt[benchmark] = $4
        total_smt[benchmark] = $5
      } else if (variant == "QBF") {
        enc_qbf[benchmark] = $3
        solve_qbf[benchmark] = $4
        total_qbf[benchmark] = $5
      }
    }

    END {
      for (i = 1; i <= n; i++) {
        b = order[i]

        print b, \
          (enc_smt[b]   == "" ? "NA" : enc_smt[b]), \
          (solve_smt[b] == "" ? "NA" : solve_smt[b]), \
          (total_smt[b] == "" ? "NA" : total_smt[b]), \
          (enc_qbf[b]   == "" ? "NA" : enc_qbf[b]), \
          (solve_qbf[b] == "" ? "NA" : solve_qbf[b]), \
          (total_qbf[b] == "" ? "NA" : total_qbf[b])
      }
    }
  ' "$RAW_CSV" > "$CSV"

  column -s, -t < "$CSV" | sed '1s/^/**/;1s/$/**/' | column -t

  {
    echo "| Benchmark | Encoding(SMT) | Solve(SMT) | Total(SMT) | Encoding(QBF) | Solve(QBF) | Total(QBF) |"
    echo "|-----------|--------------:|-----------:|-----------:|--------------:|-----------:|-----------:|"
    tail -n +2 "$CSV" | awk -F, \
      '{printf "| %s | %s | %s | %s | %s | %s | %s |\n",$1,$2,$3,$4,$5,$6,$7}'
  } > "$MD"

  printf "\nMarkdown table written to: $MD"
}


# --------------------------
# ---- Case definitions ----
# --------------------------


case_acdb() {
    local case_name="ACDB"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_acdb/acdb.smv \
               ${FOLDER}1_acdb/acdb.smv \
               -f ${FOLDER}1_acdb/acdb.hq \
               -k 11 -m 22 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_acdb/acdb.smv \
               ${FOLDER}1_acdb/acdb.smv \
               -f ${FOLDER}1_acdb/acdb.hq \
               -k 11 -m 22 -s hpes -q"
            ;;
        *)
            echo "Usage: case_acdb <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_acdb_ndet() {
    local case_name="ACDB_NDET"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_acdb/acdb_ndet.smv \
               ${FOLDER}1_acdb/acdb_ndet.smv \
               -f ${FOLDER}1_acdb/acdb_ndet.hq \
               -k 8 -m 16 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_acdb/acdb_ndet.smv \
               ${FOLDER}1_acdb/acdb_ndet.smv \
               -f ${FOLDER}1_acdb/acdb_ndet.hq \
               -k 8 -m 16 -s hpes -q"
            ;;
        *)
            echo "Usage: case_acdb_ndet <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_concleak() {
    local case_name="CONC_LEAK"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}2_concleaks/concleaks.smv \
               ${FOLDER}2_concleaks/concleaks.smv \
               -f ${FOLDER}2_concleaks/od.hq \
               -k 11 -m 22 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}2_concleaks/concleaks.smv \
               ${FOLDER}2_concleaks/concleaks.smv \
               -f ${FOLDER}2_concleaks/od.hq \
               -k 11 -m 22 -s hpes -q"
            ;;
        *)
            echo "Usage: case_concleak <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_concleak_ndet() {
    local case_name="CONC_LEAK_NDET"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}2_concleaks/concleaks_ndet.smv \
               ${FOLDER}2_concleaks/concleaks_ndet.smv \
               -f ${FOLDER}2_concleaks/od.hq \
               -k 18 -m 36 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}2_concleaks/concleaks_ndet.smv \
               ${FOLDER}2_concleaks/concleaks_ndet.smv \
               -f ${FOLDER}2_concleaks/od.hq \
               -k 18 -m 36 -s hpes -q"
            ;;
        *)
            echo "Usage: case_concleak_ndet <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_specexec_v1() {
    local case_name="specexec_V1"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v1_nse.smv \
               ${FOLDER}3_speculative/flattened/v1_se.smv \
               -f ${FOLDER}3_speculative/flattened/v1.hq \
               -k 6 -m 12 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v1_nse.smv \
               ${FOLDER}3_speculative/flattened/v1_se.smv \
               -f ${FOLDER}3_speculative/flattened/v1.hq \
               -k 6 -m 12 -s hpes -q"
            ;;
        *)
            echo "Usage: case_specexec_v1 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_specexec_v2() {
    local case_name="specexec_V2"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v2_nse.smv \
               ${FOLDER}3_speculative/flattened/v2_se.smv \
               -f ${FOLDER}3_speculative/flattened/v2.hq \
               -k 6 -m 12 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v2_nse.smv \
               ${FOLDER}3_speculative/flattened/v2_se.smv \
               -f ${FOLDER}3_speculative/flattened/v2.hq \
               -k 6 -m 12 -s hpes -q"
            ;;
        *)
            echo "Usage: case_specexec_v2 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_specexec_v3() {
    local case_name="specexec_V3"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v3_nse.smv \
               ${FOLDER}3_speculative/flattened/v3_se.smv \
               -f ${FOLDER}3_speculative/flattened/v3.hq \
               -k 6 -m 12 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v3_nse.smv \
               ${FOLDER}3_speculative/flattened/v3_se.smv \
               -f ${FOLDER}3_speculative/flattened/v3.hq \
               -k 6 -m 12 -s hpes -q"
            ;;
        *)
            echo "Usage: case_specexec_v3 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_specexec_v4() {
    local case_name="specexec_V4"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v4_nse.smv \
               ${FOLDER}3_speculative/flattened/v4_se.smv \
               -f ${FOLDER}3_speculative/flattened/v4.hq \
               -k 6 -m 12 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v4_nse.smv \
               ${FOLDER}3_speculative/flattened/v4_se.smv \
               -f ${FOLDER}3_speculative/flattened/v4.hq \
               -k 6 -m 12 -s hpes -q"
            ;;
        *)
            echo "Usage: case_specexec_v4 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_specexec_v5() {
    local case_name="specexec_V5"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v5_nse.smv \
               ${FOLDER}3_speculative/flattened/v5_se.smv \
               -f ${FOLDER}3_speculative/flattened/v5.hq \
               -k 6 -m 12 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v5_nse.smv \
               ${FOLDER}3_speculative/flattened/v5_se.smv \
               -f ${FOLDER}3_speculative/flattened/v5.hq \
               -k 6 -m 12 -s hpes -q"
            ;;
        *)
            echo "Usage: case_specexec_v5 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_specexec_v6() {
    local case_name="specexec_V6"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v6_nse.smv \
               ${FOLDER}3_speculative/flattened/v6_se.smv \
               -f ${FOLDER}3_speculative/flattened/v6.hq \
               -k 6 -m 12 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v6_nse.smv \
               ${FOLDER}3_speculative/flattened/v6_se.smv \
               -f ${FOLDER}3_speculative/flattened/v6.hq \
               -k 6 -m 12 -s hpes -q"
            ;;
        *)
            echo "Usage: case_specexec_v6 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_specexec_v7() {
    local case_name="specexec_V7"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v7_nse.smv \
               ${FOLDER}3_speculative/flattened/v7_se.smv \
               -f ${FOLDER}3_speculative/flattened/v7.hq \
               -k 6 -m 12 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_speculative/flattened/v7_nse.smv \
               ${FOLDER}3_speculative/flattened/v7_se.smv \
               -f ${FOLDER}3_speculative/flattened/v7.hq \
               -k 6 -m 12 -s hpes -q"
            ;;
        *)
            echo "Usage: case_specexec_v7 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_dbe() {
    local case_name="OPT_DBE"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/dbe/DBE_source.smv \
               ${FOLDER}4_optimization/original/dbe/DBE_target.smv \
               -f ${FOLDER}4_optimization/original/dbe/DBE.hq \
               -k 4 -m 8 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/dbe/DBE_source.smv \
               ${FOLDER}4_optimization/original/dbe/DBE_target.smv \
               -f ${FOLDER}4_optimization/original/dbe/DBE.hq \
               -k 4 -m 8 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_dbe <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_dbe_ndet() {
    local case_name="OPT_DBE_NDET"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/dbe/DBE_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/dbe/DBE_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/dbe/DBE.hq \
               -k 13 -m 26 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/dbe/DBE_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/dbe/DBE_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/dbe/DBE.hq \
               -k 13 -m 26 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_dbe_ndet <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_dbe_ndet_buggy() {
    local case_name="OPT_DBE_NDET_BUG"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/dbe/DBE_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/dbe/DBE_target_wrong_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/dbe/DBE2.hq \
               -k 13 -m 26 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/dbe/DBE_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/dbe/DBE_target_wrong_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/dbe/DBE2.hq \
               -k 13 -m 26 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_dbe_ndet_buggy <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_lp() {
    local case_name="OPT_LP"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/lp/LP_source.smv \
               ${FOLDER}4_optimization/original/lp/LP_target.smv \
               -f ${FOLDER}4_optimization/original/lp/LP.hq \
               -k 22 -m 44 -s hpes"
            ;;
        # Note: the bound is smaller to accomodate bit-blasting in QBF mode
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/lp/LP_source.smv \
               ${FOLDER}4_optimization/original/lp/LP_target.smv \
               -f ${FOLDER}4_optimization/original/lp/LP.hq \
               -k 14 -m 28 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_lp <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_lp_ndet() {
    local case_name="OPT_LP_NDET"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/lp/LP_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/lp/LP.hq \
               -k 17 -m 34 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/lp/LP_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/lp/LP.hq \
               -k 17 -m 34 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_lp_ndet <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_lp_loop() {
    local case_name="OPT_LP_LOOP"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_loops/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_loops/lp/LP_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_loops/lp/LP.hq \
               -k 35 -m 70 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_loops/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_loops/lp/LP_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_loops/lp/LP.hq \
               -k 35 -m 70 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_lp_loop <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_lp_buggy() {
    local case_name="OPT_LP_BUG"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_bugs/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_bugs/lp/LP_target_wrong_ndet.smv \
               -f ${FOLDER}4_optimization/with_bugs/lp/LP.hq \
               -k 17 -m 34 -s hpes"
            ;;
        # Note: the bound is smaller to accomodate bit-blasting in QBF mode
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_bugs/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_bugs/lp/LP_target_wrong_ndet.smv \
               -f ${FOLDER}4_optimization/with_bugs/lp/LP.hq \
               -k 16 -m 32 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_lp_buggy <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_eflp() {
    local case_name="OPT_EFLP"
    local mode="$1"

    # Note: the bound is larger to accomodate the modification in the model for EFLP
    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/eflp/EFLP_source.smv \
               ${FOLDER}4_optimization/original/eflp/EFLP_target.smv \
               -f ${FOLDER}4_optimization/original/eflp/EFLP.hq \
               -k 36 -m 72 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/eflp/EFLP_source.smv \
               ${FOLDER}4_optimization/original/eflp/EFLP_target.smv \
               -f ${FOLDER}4_optimization/original/eflp/EFLP.hq \
               -k 36 -m 72 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_eflp <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_opt_eflp_ndet() {
    local case_name="OPT_EFLP_NDET"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/eflp/EFLP_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/eflp/EFLP_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/eflp/EFLP.hq \
               -k 22 -m 44 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_ndet/eflp/EFLP_source_ndet.smv \
               ${FOLDER}4_optimization/with_ndet/eflp/EFLP_target_ndet.smv \
               -f ${FOLDER}4_optimization/with_ndet/eflp/EFLP.hq \
               -k 22 -m 44 -s hpes -q"
            ;;
        *)
            echo "Usage: case_opt_eflp_ndet <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_cache() {
    local case_name="CACHE"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_cache/cache_flattened.smv \
               ${FOLDER}5_cache/cache_flattened.smv \
               -f ${FOLDER}5_cache/odnd.hq \
               -k 13 -m 26 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_cache/cache_flattened.smv \
               ${FOLDER}5_cache/cache_flattened.smv \
               -f ${FOLDER}5_cache/odnd2.hq \
               -k 13 -m 26 -s hpes -q"
            ;;
        *)
            echo "Usage: case_cache <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

# ------------
# MAIN DRIVER
# ------------

# Register the cases available for -compare
CASES=(
    acdb
    acdb_ndet
    concleak
    concleak_ndet
    specexec_v1
    specexec_v2
    specexec_v3
    specexec_v4
    specexec_v5
    specexec_v6
    specexec_v7
    opt_dbe
    opt_dbe_ndet
    opt_dbe_ndet_buggy
    opt_lp
    opt_lp_ndet
    opt_lp_loop
    opt_lp_buggy
    opt_eflp
    opt_eflp_ndet
    cache
)

usage() {
  cat <<EOF
Usage: $0 [mode]
  -list                    List cases available
  -all <mode>              Run all cases with the chosen mode (smt|qbf)
  -light <mode>            Run lightweight cases with the chosen mode (smt|qbf)
  -heavy <mode>            Run heavy cases with the chosen mode (smt|qbf)
  -compare all             Run all CASES with all modes (smt|qbf)
  -compare light           Run lightweight cases with all modes
  -compare heavy           Run heavy cases with all modes
  -compare <case_name>     Run only the specified case with all modes
  -case <case_name> <mode>      Run a single case function with one of the modes (smt|qbf)
EOF
  exit 1
}

LIGHT_CASES=()
for case_fn in "${CASES[@]}"; do
  case "$case_fn" in
    concleak_ndet|opt_lp|opt_lp_ndet|opt_lp_loop|opt_lp_buggy|opt_eflp|opt_eflp_ndet|cache) ;;
    *) LIGHT_CASES+=("$case_fn");;
  esac
done

HEAVY_CASES=()
for case_fn in "${CASES[@]}"; do
  is_light=0
  for light_case in "${LIGHT_CASES[@]}"; do
    if [[ "$case_fn" == "$light_case" ]]; then
      is_light=1
      break
    fi
  done
  if (( ! is_light )); then
    HEAVY_CASES+=("$case_fn")
  fi
done
unset is_light

list_cases() {
  printf "Available cases:\n"
  for c in "${CASES[@]}"; do echo "  $c"; done
}

run_matrix() {
  local modes=("$@")
  for c in "${CASES[@]}"; do
    local fn="case_${c}"
    for m in "${modes[@]}"; do
      "$fn" "$m"
    done
  done
  render_tables
}

run_single_case_matrix() {
  local case_name="$1"; shift
  local modes=("$@")
  fn="case_${case_name}"
  if declare -f "$fn" >/dev/null 2>&1; then
    for m in "${modes[@]}"; do
      "$fn" "$m"
    done
    render_tables
  else
    echo "(!) Unknown case function: $case_name"
    list_cases
    exit 1
  fi
}

run_light_compare_matrix() {
  local modes=()
  local extra_args=()
  local parsing_modes=1
  for arg in "$@"; do
    if (( parsing_modes )); then
      if [[ "$arg" == "--" ]]; then
        parsing_modes=0
      else
        modes+=("$arg")
      fi
    else
      extra_args+=("$arg")
    fi
  done
  for c in "${LIGHT_CASES[@]}"; do
    local fn="case_${c}"
    if ! declare -f "$fn" >/dev/null 2>&1; then
      echo "(!) Missing case function: $fn"
      exit 1
    fi
    for m in "${modes[@]}"; do
      if (( ${#extra_args[@]} )); then
        "$fn" "$m" "${extra_args[@]}"
      else
        "$fn" "$m"
      fi
    done
  done
  render_tables
}

run_light_mode() {
  local mode="${1:-}"
  shift
  local extra_args=("$@")
  for c in "${LIGHT_CASES[@]}"; do
    local fn="case_${c}"
    if ! declare -f "$fn" >/dev/null 2>&1; then
      echo "(!) Missing case function: $fn"
      exit 1
    fi
    if (( ${#extra_args[@]} )); then
      "$fn" "$mode" "${extra_args[@]}"
    else
      "$fn" "$mode"
    fi
  done
  render_tables
}

run_heavy_compare_matrix() {
  local modes=()
  local extra_args=()
  local parsing_modes=1
  for arg in "$@"; do
    if (( parsing_modes )); then
      if [[ "$arg" == "--" ]]; then
        parsing_modes=0
      else
        modes+=("$arg")
      fi
    else
      extra_args+=("$arg")
    fi
  done
  for c in "${HEAVY_CASES[@]}"; do
    local fn="case_${c}"
    if ! declare -f "$fn" >/dev/null 2>&1; then
      echo "(!) Missing case function: $fn"
      exit 1
    fi
    for m in "${modes[@]}"; do
      if (( ${#extra_args[@]} )); then
        "$fn" "$m" "${extra_args[@]}"
      else
        "$fn" "$m"
      fi
    done
  done
  render_tables
}

run_heavy_mode() {
  local mode="${1:-}"
  shift
  local extra_args=("$@")
  for c in "${HEAVY_CASES[@]}"; do
    local fn="case_${c}"
    if ! declare -f "$fn" >/dev/null 2>&1; then
      echo "(!) Missing case function: $fn"
      exit 1
    fi
    if (( ${#extra_args[@]} )); then
      "$fn" "$mode" "${extra_args[@]}"
    else
      "$fn" "$mode"
    fi
  done
  render_tables
}

case "${1:-}" in
  -compare)
    shift
    compare_target="${1:-}"
    if [[ -z "$compare_target" ]]; then
      echo "(!) The '-compare' option requires an argument."
      echo "   Usage: $0 -compare [all|light|heavy|<case_name>]"
      echo
      list_cases
      exit 1
    fi
    shift
    case "$compare_target" in
      all)
          run_matrix smt qbf
        ;;
      light)
          run_light_compare_matrix smt qbf
        ;;
      heavy)
          run_heavy_compare_matrix smt qbf
        ;;
      *)
          run_single_case_matrix "$compare_target" smt qbf
        ;;
    esac
    ;;

  -all)
    shift
    if [[ -z "${1:-}" ]]; then
      echo "(!) The '-all' option requires an argument."
      echo "   Usage: $0 -all [smt|qbf]"
      exit 1
    elif [[ "$1" == "smt" ]]; then
      run_matrix smt
    else
      run_matrix qbf
    fi
    ;;

  -light)
    shift
    mode_raw="${1:-}"
    [[ -z "$mode_raw" ]] && usage
    mode="$(printf '%s' "$mode_raw" | tr '[:upper:]' '[:lower:]')"
    case "$mode" in
      smt|qbf) ;;
      *)
        echo "(!) Unknown mode for -light: $mode_raw"
        exit 1
        ;;
    esac
    shift
    if (( $# )); then
      run_light_mode "$mode" "$@"
    else
      run_light_mode "$mode"
    fi
    ;;

  -heavy)
    shift
    mode_raw="${1:-}"
    [[ -z "$mode_raw" ]] && usage
    mode="$(printf '%s' "$mode_raw" | tr '[:upper:]' '[:lower:]')"
    case "$mode" in
      smt|qbf) ;;
      *)
        echo "(!) Unknown mode for -heavy: $mode_raw"
        exit 1
        ;;
    esac
    shift
    if (( $# )); then
      run_heavy_mode "$mode" "$@"
    else
      run_heavy_mode "$mode"
    fi
    ;;

  -case)
    shift
    func="${1:-}"; mode="${2:-}"
    [[ -z "$func" || -z "$mode" ]] && usage
    shift 2
    extra_case_args=("$@")
    fn="case_${func}"
    if declare -f "$fn" >/dev/null 2>&1; then
      if (( ${#extra_case_args[@]} )); then
        "$fn" "$mode" -- "${extra_case_args[@]}"
      else
        "$fn" "$mode"
      fi
      render_tables
    else
      echo "Unknown case: $func"
      list_cases
      exit 1
    fi
    ;;

  -list)
    list_cases
    ;;

  *)
    usage
    ;;
esac
