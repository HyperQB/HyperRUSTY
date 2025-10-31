
#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-120}  # seconds

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
MD="${RESULTS_DIR}/table6(ahltl)_runtimes.md"

CARGO_BIN=${CARGO_BIN:-target/release/HyperRUSTY}
# if [[ ! -x "$CARGO_BIN" ]]; then
  echo "Building HyperQB (release)…"
  cargo build --release
# fi

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
echo "case,variant,result,real_s,log" > "$CSV"

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

    # Determine status from log (prefer UNSAT if both appear)
    local status="NA"
    if [[ -n "${TIMEOUT_BIN:-}" && $exit_code -eq 124 ]]; then
        echo "[TIMEOUT] $case_name ($variant) exceeded ${TIMEOUT_SEC}s." | tee -a "$log_file"
        real_s="${TIMEOUT_SEC}"
        status="TIMEOUT"
    else
        # Case-insensitive word match; -w avoids matching "saturated"
        if grep -qiwo 'UNSAT' "$log_file"; then
            status="UNSAT"
        elif grep -qiwo 'SAT' "$log_file"; then
            status="SAT"
        fi
        if [[ $exit_code -ne 0 && "$status" == "NA" ]]; then
            status="ERROR"
            real_s="NA"
        fi
    fi


    # execution finished.  
    # Append one row to CSV (simple real time)
    if [[ "$variant" =~ ^([Ss][Mm][Tt])$ ]]; then
        local line_count=0
        line_count=$(wc -l < "$CSV" 2>/dev/null || echo 0)
        if (( line_count > 1 )); then
            printf "%s\n" "-----,-----,-----,-----,-----" >> "$CSV"
        fi
    fi
    printf "%s,%s,%s,%s,%s\n" \
        "$case_name" "$variant" "$status" "${real_s:-0.0}" "$log_file" >> "$CSV"
        
    # Append one row to CSV (full info)
    # printf "%s,%s,%s,%s,%s,%.3f,%.3f,%.3f,%s,%s\n" \
    # "$stamp" "$case_name" "$variant" "$status" "$exit_code" \
    # "$real_s" "$user_s" "$sys_s" "$max_rss_kb" "$log_file" >> "$CSV"

}

# ---- Pretty-print table (plain + markdown) ----
render_tables() {
  echo
  echo "=== Table 6 runtimes (A-HLTL cases) ==="
  column -s, -t < "$CSV" | sed '1s/^/**/;1s/$/**/' | column -t

  # Markdown table
  {
    echo "| Case | Variant | Result | Real (s) | Log |"
    echo "|------|---------|--------|---------:|-----|"
    tail -n +2 "$CSV" | awk -F, '{printf "| %s | %s | %s | %s | %s |\n",$1,$2,$3,$4,$5}'
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
               -n ${FOLDER}2_concleaks/concleaks_2procs.smv \
               ${FOLDER}2_concleaks/concleaks_2procs.smv \
               -f ${FOLDER}2_concleaks/od.hq \
               -k 11 -m 22 -s hpes"
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
               -n ${FOLDER}2_concleaks/concleaks_3procs.smv \
               ${FOLDER}2_concleaks/concleaks_3procs.smv \
               -f ${FOLDER}2_concleaks/od.hq \
               -k 18 -m 36 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}2_concleaks/concleaks_3procs.smv \
               ${FOLDER}2_concleaks/concleaks_3procs.smv \
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
               -k 12 -m 24 -s hpes"
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
               -k 23 -m 45 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/lp/LP_source.smv \
               ${FOLDER}4_optimization/original/lp/LP_target.smv \
               -f ${FOLDER}4_optimization/original/lp/LP.hq \
               -k 23 -m 45 -s hpes -q"
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
               -n ${FOLDER}4_optimization/original/lp/LP_source.smv \
               ${FOLDER}4_optimization/original/lp/LP_target.smv \
               -f ${FOLDER}4_optimization/original/lp/LP.hq \
               -k 23 -m 45 -s hpes -q"
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
               -n ${FOLDER}4_optimization/with_loops/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_loops/lp/LP_target_wrong_ndet.smv \
               -f ${FOLDER}4_optimization/with_loops/lp/LP.hq \
               -k 17 -m 34 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/with_loops/lp/LP_source_ndet.smv \
               ${FOLDER}4_optimization/with_loops/lp/LP_target_wrong_ndet.smv \
               -f ${FOLDER}4_optimization/with_loops/lp/LP.hq \
               -k 17 -m 34 -s hpes -q"
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

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/eflp/EFLP_source.smv \
               ${FOLDER}4_optimization/original/eflp/EFLP_target.smv \
               -f ${FOLDER}4_optimization/original/eflp/EFLP.hq \
               -k 32 -m 64 -s hpes"
            ;;
        2|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "${CARGO_BIN} \
               -n ${FOLDER}4_optimization/original/eflp/EFLP_source.smv \
               ${FOLDER}4_optimization/original/eflp/EFLP_target.smv \
               -f ${FOLDER}4_optimization/original/eflp/EFLP.hq \
               -k 32 -m 64 -s hpes -q"
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
               -k 6 -m 12 -s hpes -q"
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
  -compare all             Run all CASES with all modes (smt|qbf)
  -compare <case_name>     Run only the specified case with all modes
  -case <case_name> <mode>      Run a single case function with one of the modes (smt|qbf)
EOF
  exit 1
}

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

case "${1:-}" in
  -compare)
    shift
    if [[ -z "${1:-}" ]]; then
      echo "(!) The '-compare' option requires an argument."
      echo "   Usage: $0 -compare [all|<case_name>]"
      echo
      list_cases
      exit 1
    elif [[ "$1" == "all" ]]; then
      run_matrix smt qbf
    else
      run_single_case_matrix "$1" smt qbf
    fi
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
    render_tables
    ;;

  -light)
    shift
    if [[ -z "${1:-}" ]]; then
      echo "(!) The '-light' option requires an argument."
      echo "   Usage: $0 -light [smt|qbf]"
      exit 1
    local_subset=(
      acdb
      concleak
      specexec_v1
      specexec_v4
    )
    elif [[ "$1" == "smt" ]]; then
      for c in "${local_subset[@]}"; do
        local fn="case_${c}"
        "$fn" smt
      done
    else
      for c in "${local_subset[@]}"; do
        local fn="case_${c}"
        "$fn" qbf
      done
    fi
    render_tables
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
