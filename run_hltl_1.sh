#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-1800}  # Please adjust this timeout value as needed for your environment. Default is 60 second for quick testing, but you may want to increase it for more complex cases.


# ---- Paths for results/logs ----
FOLDER="benchmarks/sync/"
RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/table1(hltl_1)_runtimes.csv"
MD="${RESULTS_DIR}/table1(hltl_1)_runtimes.md"
RAW_CSV="${RESULTS_DIR}/table1(hltl_cav26)_runtimes_long.csv"

# 0 = verification-only table
# 1 = verification+witness table
WITNESS_TABLE=0

CARGO_BIN=${CARGO_BIN:-target/release/HyperRUSTY}
if [[ ! -x "$CARGO_BIN" ]]; then
  echo "Building HyperQB (release)…"
  cargo build --release
fi

# Detect timeout binary safely (avoid unbound variable errors)
if command -v gtimeout >/dev/null 2>&1; then
  TIMEOUT_BIN="gtimeout"
elif command -v timeout >/dev/null 2>&1; then
  TIMEOUT_BIN="timeout"
else
  TIMEOUT_BIN=""   # fallback: no timeout available
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
echo "Benchmark,Variant,Encoding,Solving,Total" > "$RAW_CSV"
: > "$CSV"

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

set_table_mode_from_args() {
    WITNESS_TABLE=0

    for arg in "$@"; do
        if [[ "$arg" == "give_witness" ]]; then
            WITNESS_TABLE=1
            return
        fi
    done
}

# ---- Timing helper ----
time_run() {
    local case_name="$1"; shift
    local variant="$1"; shift

    # Only run/record variants needed for the selected table.
    if (( WITNESS_TABLE )); then
        case "$variant" in
            SMT_witness|QBF|AH_witness) ;;
            *) return 0 ;;
        esac
    else
        case "$variant" in
            SMT|QBF|AH) ;;
            *) return 0 ;;
        esac
    fi

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
    # Extract benchmark-reported timings from the log.
    local model_creation_s encoding_time_s smt_solve_s qbf_solve_s
    local encoding_s solving_s total_s forced_cell

    forced_cell=""

    if [[ "$status" == "TIMEOUT" ]]; then
        forced_cell="TO"
    elif [[ "$status" == "ERROR" ]]; then
        forced_cell="ERR"
    elif [[ "$status" == "MEMOUT" ]]; then
        forced_cell="MO"
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
        case "$variant" in
          SMT|SMT_witness|QBF)
            encoding_s="$forced_cell"
            solving_s="$forced_cell"
            total_s="$forced_cell"
            ;;
          AH|AH_witness)
            encoding_s=""
            solving_s=""
            total_s="$forced_cell"
            ;;
          *)
            encoding_s="$forced_cell"
            solving_s="$forced_cell"
            total_s="$forced_cell"
            ;;
        esac
    else
        total_s="$(fmt_time "$real_s")"

        case "$variant" in
          SMT|SMT_witness)
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

          QBF)
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

          AH|AH_witness)
            encoding_s=""
            solving_s=""
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
  echo "=== Table 1 runtimes (TACAS'21 cases) ==="

  if (( WITNESS_TABLE )); then
    awk -F, '
      BEGIN {
        OFS = ","
        print "Benchmark", \
              "SMT_Enc","SMT_Solve","SMT_Total", \
              "QBF_Enc","QBF_Solve","QBF_Total", \
              "AH_Total"
      }

      NR == 1 { next }

      {
        b = $1
        v = toupper($2)

        if (!(b in seen)) {
          seen[b] = 1
          order[++n] = b
        }

        if (v == "SMT_WITNESS") {
          smt_enc[b] = $3
          smt_solve[b] = $4
          smt_total[b] = $5
        } else if (v == "QBF") {
          qbf_enc[b] = $3
          qbf_solve[b] = $4
          qbf_total[b] = $5
        } else if (v == "AH_WITNESS") {
          ah_total[b] = $5
        }
      }

      function cell(x) {
        return x == "" ? "NA" : x
      }

      END {
        for (i = 1; i <= n; i++) {
          b = order[i]
          print b, \
                cell(smt_enc[b]), cell(smt_solve[b]), cell(smt_total[b]), \
                cell(qbf_enc[b]), cell(qbf_solve[b]), cell(qbf_total[b]), \
                cell(ah_total[b])
        }
      }
    ' "$RAW_CSV" > "$CSV"

    column -s, -t < "$CSV" | sed '1s/^/**/;1s/$/**/' | column -t

    {
      cat <<'EOF'
<table>
<thead>
<tr>
  <th rowspan="3">Benchmark</th>
  <th colspan="7">Verification + Witness</th>
</tr>
<tr>
  <th colspan="3">HQ2.0<sub>SMT</sub></th>
  <th colspan="3">HQ2.0<sub>QBF</sub></th>
  <th>AH</th>
</tr>
<tr>
  <th>Enc.</th>
  <th>Solve</th>
  <th>Total</th>
  <th>Enc.</th>
  <th>Solve</th>
  <th>Total</th>
  <th>Total</th>
</tr>
</thead>
<tbody>
EOF

      tail -n +2 "$CSV" | awk -F, '
        {
          printf "<tr>"
          for (i = 1; i <= NF; i++) {
            if (i == 1) printf "<td>%s</td>", $i
            else        printf "<td align=\"right\">%s</td>", $i
          }
          printf "</tr>\n"
        }
      '

      cat <<'EOF'
</tbody>
</table>
EOF
    } > "$MD"

  else
    awk -F, '
      BEGIN {
        OFS = ","
        print "Benchmark", \
              "SMT_Enc","SMT_Solve","SMT_Total", \
              "QBF_Enc","QBF_Solve","QBF_Total", \
              "AH_Total"
      }

      NR == 1 { next }

      {
        b = $1
        v = toupper($2)

        if (!(b in seen)) {
          seen[b] = 1
          order[++n] = b
        }

        if (v == "SMT") {
          smt_enc[b] = $3
          smt_solve[b] = $4
          smt_total[b] = $5
        } else if (v == "QBF") {
          qbf_enc[b] = $3
          qbf_solve[b] = $4
          qbf_total[b] = $5
        } else if (v == "AH") {
          ah_total[b] = $5
        }
      }

      function cell(x) {
        return x == "" ? "NA" : x
      }

      END {
        for (i = 1; i <= n; i++) {
          b = order[i]
          print b, \
                cell(smt_enc[b]), cell(smt_solve[b]), cell(smt_total[b]), \
                cell(qbf_enc[b]), cell(qbf_solve[b]), cell(qbf_total[b]), \
                cell(ah_total[b])
        }
      }
    ' "$RAW_CSV" > "$CSV"

    column -s, -t < "$CSV" | sed '1s/^/**/;1s/$/**/' | column -t

    {
      cat <<'EOF'
<table>
<thead>
<tr>
  <th rowspan="3">Benchmark</th>
  <th colspan="7">Verification Only</th>
</tr>
<tr>
  <th colspan="3">HQ2.0<sub>SMT</sub></th>
  <th colspan="3">HQ2.0<sub>QBF</sub></th>
  <th>AH</th>
</tr>
<tr>
  <th>Enc.</th>
  <th>Solve</th>
  <th>Total</th>
  <th>Enc.</th>
  <th>Solve</th>
  <th>Total</th>
  <th>Total</th>
</tr>
</thead>
<tbody>
EOF

      tail -n +2 "$CSV" | awk -F, '
        {
          printf "<tr>"
          for (i = 1; i <= NF; i++) {
            if (i == 1) printf "<td>%s</td>", $i
            else        printf "<td align=\"right\">%s</td>", $i
          }
          printf "</tr>\n"
        }
      '

      cat <<'EOF'
</tbody>
</table>
EOF
    } > "$MD"
  fi

  printf "\nMarkdown table written to: $MD"
}


# --------------------------
# ---- Case definitions ----
# --------------------------

case_bakery3() {
    local case_name="Bakery3"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery3.smv \
               ${FOLDER}1_bakery/bakery3.smv \
               -f ${FOLDER}1_bakery/symmetry3.hq \
               -k 10 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}1_bakery/bakery3.smv \
                   ${FOLDER}1_bakery/bakery3.smv \
                   -f ${FOLDER}1_bakery/symmetry3.hq \
                   -k 10 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery3.smv \
               ${FOLDER}AH_formulas/1.1.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}1_bakery/bakery3.smv \
                   ${FOLDER}AH_formulas/1.1.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery3.smv \
               ${FOLDER}1_bakery/bakery3.smv \
               -f ${FOLDER}1_bakery/symmetry3.hq \
               -k 10 -s hpes -q"
            ;;
        *)
            echo "Usage: case_bakery3 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}

case_bakery7() {
    local case_name="Bakery7"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery7.smv \
               ${FOLDER}1_bakery/bakery7.smv \
               -f ${FOLDER}1_bakery/symmetry7.hq \
               -k 10 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}1_bakery/bakery7.smv \
                   ${FOLDER}1_bakery/bakery7.smv \
                   -f ${FOLDER}1_bakery/symmetry7.hq \
                   -k 10 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery7.smv \
               ${FOLDER}AH_formulas/1.7.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}1_bakery/bakery7.smv \
                   ${FOLDER}AH_formulas/1.7.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery7.smv \
               ${FOLDER}1_bakery/bakery7.smv \
               -f ${FOLDER}1_bakery/symmetry7.hq \
               -k 10 -s hpes -q"
            ;;
        *)
            echo "Usage: case_bakery7 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}

case_bakery9() {
    local case_name="Bakery9"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery9.smv \
               ${FOLDER}1_bakery/bakery9.smv \
               -f ${FOLDER}1_bakery/symmetry9.hq \
               -k 10 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}1_bakery/bakery9.smv \
                   ${FOLDER}1_bakery/bakery9.smv \
                   -f ${FOLDER}1_bakery/symmetry9.hq \
                   -k 10 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery9.smv \
               ${FOLDER}AH_formulas/1.9.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}1_bakery/bakery9.smv \
                   ${FOLDER}AH_formulas/1.9.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery9.smv \
               ${FOLDER}1_bakery/bakery9.smv \
               -f ${FOLDER}1_bakery/symmetry9.hq \
               -k 10 -s hpes -q"
            ;;
        *)
            echo "Usage: case_bakery9 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}

case_bakery11() {
    local case_name="Bakery11"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery11.smv \
               ${FOLDER}1_bakery/bakery11.smv \
               -f ${FOLDER}1_bakery/symmetry11.hq \
               -k 10 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}1_bakery/bakery11.smv \
                   ${FOLDER}1_bakery/bakery11.smv \
                   -f ${FOLDER}1_bakery/symmetry11.hq \
                   -k 10 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery11.smv \
               ${FOLDER}AH_formulas/1.11.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}1_bakery/bakery11.smv \
                   ${FOLDER}AH_formulas/1.11.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}1_bakery/bakery11.smv \
               ${FOLDER}1_bakery/bakery11.smv \
               -f ${FOLDER}1_bakery/symmetry11.hq \
               -k 10 -s hpes -q"
            ;;
        *)
            echo "Usage: case_bakery11 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}

case_snark1() {
    local case_name="SNARK1"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}2_snark/snark1_conc.smv \
               ${FOLDER}2_snark/snark1_seq.smv \
               -f ${FOLDER}2_snark/lin.hq \
               -k 18 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}2_snark/snark1_conc.smv \
                   ${FOLDER}2_snark/snark1_seq.smv \
                   -f ${FOLDER}2_snark/lin.hq \
                   -k 18 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}2_snark/snark1_conc.smv \
               ${FOLDER}2_snark/snark1_seq.smv \
               ${FOLDER}AH_formulas/2.1.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}2_snark/snark1_conc.smv \
                   ${FOLDER}2_snark/snark1_seq.smv \
                   ${FOLDER}AH_formulas/2.1.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}2_snark/snark1_conc.smv \
               ${FOLDER}2_snark/snark1_seq.smv \
               -f ${FOLDER}2_snark/lin.hq \
               -k 18 -s hpes -q"
            ;;
        *)
            echo "Usage: case_snark1 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_ni_correct() {
    local case_name="NI_correct"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_ni/NI_correct.smv \
               ${FOLDER}3_ni/NI_correct.smv \
               -f ${FOLDER}3_ni/NI_formula.hq \
               -k 50 -s hopt"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}3_ni/NI_correct.smv \
               ${FOLDER}AH_formulas/3.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_ni/NI_correct.smv \
               ${FOLDER}3_ni/NI_correct.smv \
               -f ${FOLDER}3_ni/NI_formula.hq \
               -k 50 -s hopt -q"
            ;;
        *)
            echo "Usage: case_ni_correct <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_ni_incorrect() {
    local case_name="NI_incorrect"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_ni/NI_incorrect.smv \
               ${FOLDER}3_ni/NI_incorrect.smv \
               -f ${FOLDER}3_ni/NI_formula.hq \
               -k 50 -s hopt"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}3_ni/NI_incorrect.smv \
                   ${FOLDER}3_ni/NI_incorrect.smv \
                   -f ${FOLDER}3_ni/NI_formula.hq \
                   -k 50 -s hopt -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}3_ni/NI_incorrect.smv \
               ${FOLDER}AH_formulas/3.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}3_ni/NI_incorrect.smv \
                   ${FOLDER}AH_formulas/3.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}3_ni/NI_incorrect.smv \
               ${FOLDER}3_ni/NI_incorrect.smv \
               -f ${FOLDER}3_ni/NI_formula.hq \
               -k 50 -s hopt -q"
            ;;
        *)
            echo "Usage: case_ni_incorrect <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_nrp_correct() {
    local case_name="NRP_correct"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        # update the bound to 20 to fix extra non-determinism
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_nrp/NRP_correct.smv \
               ${FOLDER}4_nrp/NRP_correct.smv \
               -f ${FOLDER}4_nrp/NRP_formula.hq \
               -k 16 -s pes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}4_nrp/NRP_correct.smv \
                   ${FOLDER}4_nrp/NRP_correct.smv \
                   -f ${FOLDER}4_nrp/NRP_formula.hq \
                   -k 16 -s pes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}4_nrp/NRP_correct.smv \
               ${FOLDER}AH_formulas/4.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}4_nrp/NRP_correct.smv \
                   ${FOLDER}AH_formulas/4.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_nrp/NRP_correct.smv \
               ${FOLDER}4_nrp/NRP_correct.smv \
               -f ${FOLDER}4_nrp/NRP_formula.hq \
               -k 16 -s pes -q"
            ;;
        *)
            echo "Usage: case_nrp_correct <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_nrp_incorrect() {
    local case_name="NRP_incorrect"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_nrp/NRP_incorrect.smv \
               ${FOLDER}4_nrp/NRP_incorrect.smv \
               -f ${FOLDER}4_nrp/NRP_formula.hq \
               -k 15 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}4_nrp/NRP_incorrect.smv \
               ${FOLDER}AH_formulas/4.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_nrp/NRP_incorrect.smv \
               ${FOLDER}4_nrp/NRP_incorrect.smv \
               -f ${FOLDER}4_nrp/NRP_formula.hq \
               -k 15 -s hpes -q"
            ;;
        *)
            echo "Usage: case_nrp_incorrect <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_rb100() {
    local case_name="Robustness100"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_100.smv \
               ${FOLDER}5_planning/robotic_robustness_100.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 20 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_robustness_100.smv \
               ${FOLDER}AH_formulas/5.1.hq \
               --incl-forq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_100.smv \
               ${FOLDER}5_planning/robotic_robustness_100.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 20 -s hpes -q"
            ;;
        *)
            echo "Usage: case_rb100 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}



case_rb400() {
    local case_name="Robustness400"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_400.smv \
               ${FOLDER}5_planning/robotic_robustness_400.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 40 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_robustness_400.smv \
               ${FOLDER}AH_formulas/5.1.hq \
               --incl-forq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_400.smv \
               ${FOLDER}5_planning/robotic_robustness_400.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 40 -s hpes -q"
            ;;
        *)
            echo "Usage: case_rb400 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_rb1600() {
    local case_name="Robustness1600"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_1600.smv \
               ${FOLDER}5_planning/robotic_robustness_1600.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 40 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_robustness_1600.smv \
               ${FOLDER}AH_formulas/5.1.hq \
               --incl-forq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_1600.smv \
               ${FOLDER}5_planning/robotic_robustness_1600.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 40 -s hpes -q"
            ;;
        *)
            echo "Usage: case_rb1600 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_rb3600() {
    local case_name="Robustness3600"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_3600.smv \
               ${FOLDER}5_planning/robotic_robustness_3600.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 120 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_robustness_3600.smv \
               ${FOLDER}AH_formulas/5.1.hq \
               --incl-forq"
               
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_robustness_3600.smv \
               ${FOLDER}5_planning/robotic_robustness_3600.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 120 -s hpes -q"
            ;;
        *)
            echo "Usage: case_rb3600 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_sp100() {
    local case_name="SP100"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_100.smv \
               ${FOLDER}5_planning/robotic_sp_100.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 20 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}5_planning/robotic_sp_100.smv \
                   ${FOLDER}5_planning/robotic_sp_100.smv \
                   -f ${FOLDER}5_planning/robotic_sp_formula.hq \
                   -k 20 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_100.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}5_planning/robotic_sp_100.smv \
                   ${FOLDER}AH_formulas/5.2.hq \
                   --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_100.smv \
               ${FOLDER}5_planning/robotic_sp_100.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 20 -s hpes -q"
            ;;
        *)
            echo "Usage: case_sp100 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_sp400() {
    local case_name="SP400"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_400.smv \
               ${FOLDER}5_planning/robotic_sp_400.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 40 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}5_planning/robotic_sp_400.smv \
                   ${FOLDER}5_planning/robotic_sp_400.smv \
                   -f ${FOLDER}5_planning/robotic_sp_formula.hq \
                   -k 40 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_400.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}5_planning/robotic_sp_400.smv \
                   ${FOLDER}AH_formulas/5.2.hq \
                   --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_400.smv \
               ${FOLDER}5_planning/robotic_sp_400.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 40 -s hpes -q"
            ;;
        *)
            echo "Usage: case_sp400 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_sp1600() {
    local case_name="SP1600"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_1600.smv \
               ${FOLDER}5_planning/robotic_sp_1600.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 80 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}5_planning/robotic_sp_1600.smv \
                   ${FOLDER}5_planning/robotic_sp_1600.smv \
                   -f ${FOLDER}5_planning/robotic_sp_formula.hq \
                   -k 80 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_1600.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}5_planning/robotic_sp_1600.smv \
                   ${FOLDER}AH_formulas/5.2.hq \
                   --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_1600.smv \
               ${FOLDER}5_planning/robotic_sp_1600.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 80 -s hpes -q"
            ;;
        *)
            echo "Usage: case_sp1600 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}

case_sp3600() {
    local case_name="SP3600"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_3600.smv \
               ${FOLDER}5_planning/robotic_sp_3600.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 120 -s hpes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}5_planning/robotic_sp_3600.smv \
                   ${FOLDER}5_planning/robotic_sp_3600.smv \
                   -f ${FOLDER}5_planning/robotic_sp_formula.hq \
                   -k 120 -s hpes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_3600.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}5_planning/robotic_sp_3600.smv \
                   ${FOLDER}AH_formulas/5.2.hq \
                   --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}5_planning/robotic_sp_3600.smv \
               ${FOLDER}5_planning/robotic_sp_3600.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 120 -s hpes -q"
            ;;
        *)
            echo "Usage: case_sp3600 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}

case_mutation() {
    local case_name="Mutation"
    local mode="${1:-}"  # argument: 1=SMT, 2=AutoHyper, 3=QBF
    shift
    local extra_flags=("$@")
    local want_witness=0
    if (( ${#extra_flags[@]} )); then
        for flag in "${extra_flags[@]}"; do
            if [[ "$flag" == "give_witness" ]]; then
                want_witness=1
            fi
        done
    fi

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}6_mutation/mutation_testing.smv \
               ${FOLDER}6_mutation/mutation_testing.smv \
               -f ${FOLDER}6_mutation/mutation_testing.hq \
               -k 5 -s pes"
            if (( want_witness )); then
                time_run "$case_name" "SMT_witness" \
                  "${CARGO_BIN} \
                   -n ${FOLDER}6_mutation/mutation_testing.smv \
                   ${FOLDER}6_mutation/mutation_testing.smv \
                   -f ${FOLDER}6_mutation/mutation_testing.hq \
                   -k 10 -s pes -c"
            fi
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}6_mutation/mutation_testing.smv \
               ${FOLDER}AH_formulas/6.hq"
            if (( want_witness )); then
                time_run "$case_name" "AH_witness" \
                  "AutoHyper/app/AutoHyper \
                   --nusmv ${FOLDER}6_mutation/mutation_testing.smv \
                   ${FOLDER}AH_formulas/6.hq --witness"
            fi
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}6_mutation/mutation_testing.smv \
               ${FOLDER}6_mutation/mutation_testing.smv \
               -f ${FOLDER}6_mutation/mutation_testing.hq \
               -k 10 -s pes -q"
            ;;
        *)
            echo "Usage: case_mutation <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}



# ------------
# MAIN DRIVER
# ------------

# Register the cases available for -compare
CASES=(
  # --- Bakery benchmarks ---
  bakery3
  bakery7
  bakery9
  bakery11

  # --- SNARK linearizability benchmark ---
  snark1

  # --- Non-interference (NI) benchmarks ---
  ni_correct
  ni_incorrect

  # --- Non-repudiation (NRP) benchmarks ---
  nrp_correct
  nrp_incorrect

  # --- Robotic Robustness benchmarks ---
  rb100
  rb400
  rb1600
  rb3600

  # --- Robotic SP (safety policy) benchmarks ---
  sp100
  sp400
  sp1600
  sp3600

  # --- Mutation testing benchmark ---
  mutation
)

LIGHT_CASES=()
for case_fn in "${CASES[@]}"; do
  case "$case_fn" in
    bakery9|bakery11|rb1600|rb3600|sp400|sp1600|sp3600) ;;
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

usage() {
  cat <<EOF
Usage: $0 [mode]
  -list                   List all available case functions
  -all <mode>             Run all cases with the chosen mode (smt|ah|qbf)
  -light <mode>           Run lightweight cases with the chosen mode (smt|ah|qbf)
  -heavy <mode>           Run heavy cases with the chosen mode (smt|ah|qbf)
  -compare all [extras]   Run all cases with all modes (smt/ah/qbf)
  -compare light [extras] Run lightweight cases with all modes (smt/ah/qbf)
  -compare heavy [extras] Run heavy cases with all modes (smt/ah/qbf)
  -compare <case> [extras] Run one case with all modes (see -list for case selections)
  -case <case> <mode> [extras] Run one case with selected mode (smt|ah|qbf)

Extra flags:
  give_witness            Extend SMT/AH variants with witness runs (when supported)
EOF
  exit 1
}


list_cases() {
  printf "Available cases:\n"
  for c in "${CASES[@]}"; do echo "  $c"; done
}

run_matrix() {
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
  for c in "${CASES[@]}"; do
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

run_single_case_matrix() {
  local case_name="${1:-}"; shift
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
  local fn="case_${case_name}"
  if declare -f "$fn" >/dev/null 2>&1; then
    for m in "${modes[@]}"; do
      if (( ${#extra_args[@]} )); then
        "$fn" "$m" "${extra_args[@]}"
      else
        "$fn" "$m"
      fi
    done
    render_tables
  else
    echo "(!) Unknown case: $case_name"
    list_cases
    exit 1
  fi
}


# ------------
# MAIN DRIVER
# ------------
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
    extra_compare_args=("$@")
    case "$compare_target" in
      all)
        if (( ${#extra_compare_args[@]} )); then
          run_matrix smt ah qbf -- "${extra_compare_args[@]}"
        else
          run_matrix smt ah qbf
        fi
        ;;
      light)
        if (( ${#extra_compare_args[@]} )); then
          run_light_compare_matrix smt ah qbf -- "${extra_compare_args[@]}"
        else
          run_light_compare_matrix smt ah qbf
        fi
        ;;
      heavy)
        if (( ${#extra_compare_args[@]} )); then
          run_heavy_compare_matrix smt ah qbf -- "${extra_compare_args[@]}"
        else
          run_heavy_compare_matrix smt ah qbf
        fi
        ;;
      *)
        if (( ${#extra_compare_args[@]} )); then
          run_single_case_matrix "$compare_target" smt ah qbf -- "${extra_compare_args[@]}"
        else
          run_single_case_matrix "$compare_target" smt ah qbf
        fi
        ;;
    esac
    ;;

  -all)
    shift
    mode_raw="${1:-}"
    [[ -z "$mode_raw" ]] && usage
    mode="$(printf '%s' "$mode_raw" | tr '[:upper:]' '[:lower:]')"
    case "$mode" in
      smt|ah|qbf) ;;
      *)
        echo "(!) Unknown mode for -all: $mode_raw"
        exit 1
        ;;
    esac
    shift
    if (( $# )); then
      run_matrix "$mode" -- "$@"
    else
      run_matrix "$mode"
    fi
    ;;

  -light)
    shift
    mode_raw="${1:-}"
    [[ -z "$mode_raw" ]] && usage
    mode="$(printf '%s' "$mode_raw" | tr '[:upper:]' '[:lower:]')"
    case "$mode" in
      smt|ah|qbf) ;;
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
      smt|ah|qbf) ;;
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
