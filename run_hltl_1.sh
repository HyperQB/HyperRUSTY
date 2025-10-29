#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-60}  # seconds

# Detect timeout binary safely (avoid unbound variable errors)
if command -v gtimeout >/dev/null 2>&1; then
  TIMEOUT_BIN="gtimeout"
elif command -v timeout >/dev/null 2>&1; then
  TIMEOUT_BIN="timeout"
else
  TIMEOUT_BIN=""   # fallback: no timeout available
fi

# ---- Paths for results/logs ----
FOLDER="benchmarks/sync/"
RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/table4_runtimes.csv"
MD="${RESULTS_DIR}/table4_runtimes.md"

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
    printf "%s,%s,%s,%.3f,%s\n" \
        "$case_name" "$variant" "$status" "${real_s:-0.0}" "$log_file" >> "$CSV"
    # Append one row to CSV (full info)
    # printf "%s,%s,%s,%s,%s,%.3f,%.3f,%.3f,%s,%s\n" \
    # "$stamp" "$case_name" "$variant" "$status" "$exit_code" \
    # "$real_s" "$user_s" "$sys_s" "$max_rss_kb" "$log_file" >> "$CSV"

}

# ---- Pretty-print table (plain + markdown) ----
render_tables() {
  echo
  echo "=== Table 4 runtimes (TACAS'21 cases) ==="
  column -s, -t < "$CSV" | sed '1s/^/**/;1s/$/**/' | column -t

  # Markdown table
  {
    echo "| Case | Variant | Result | Real (s) | Log |"
    echo "|------|---------|--------|---------:|-----|"
    tail -n +2 "$CSV" | awk -F, '{printf "| %s | %s | %s | %.3f | %s |\n",$1,$2,$3,$4,$5}'
  } > "$MD"
  printf "\nMarkdown table written to: $MD"
}


# --------------------------
# ---- Case definitions ----
# --------------------------

case_bakery3() {
    local case_name="Bakery3"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}1_bakery/bakery3.smv \
               ${FOLDER}1_bakery/bakery3.smv \
               -f ${FOLDER}1_bakery/symmetry3.hq \
               -k 10 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery3.smv \
               ${FOLDER}AH_formulas/1.1.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}1_bakery/bakery7.smv \
               ${FOLDER}1_bakery/bakery7.smv \
               -f ${FOLDER}1_bakery/symmetry7.hq \
               -k 10 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery7.smv \
               ${FOLDER}AH_formulas/1.7.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}1_bakery/bakery9.smv \
               ${FOLDER}1_bakery/bakery9.smv \
               -f ${FOLDER}1_bakery/symmetry9.hq \
               -k 10 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery9.smv \
               ${FOLDER}AH_formulas/1.9.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}1_bakery/bakery11.smv \
               ${FOLDER}1_bakery/bakery11.smv \
               -f ${FOLDER}1_bakery/symmetry11.hq \
               -k 10 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}1_bakery/bakery11.smv \
               ${FOLDER}AH_formulas/1.11.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}2_snark/snark1_conc.smv \
               ${FOLDER}2_snark/snark1_seq.smv \
               -f ${FOLDER}2_snark/lin.hq \
               -k 18 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}2_snark/snark1_conc.smv \
               ${FOLDER}2_snark/snark1_seq.smv \
               ${FOLDER}AH_formulas/2.1.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}3_ni/NI_incorrect.smv \
               ${FOLDER}3_ni/NI_incorrect.smv \
               -f ${FOLDER}3_ni/NI_formula.hq \
               -k 50 -s hopt"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}3_ni/NI_incorrect.smv \
               ${FOLDER}AH_formulas/3.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}4_nrp/NRP_correct.smv \
               ${FOLDER}4_nrp/NRP_correct.smv \
               -f ${FOLDER}4_nrp/NRP_formula.hq \
               -k 20 -s pes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}4_nrp/NRP_correct.smv \
               ${FOLDER}AH_formulas/4.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
               -n ${FOLDER}4_nrp/NRP_correct.smv \
               ${FOLDER}4_nrp/NRP_correct.smv \
               -f ${FOLDER}4_nrp/NRP_formula.hq \
               -k 20 -s pes -q"
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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

case_rb100_witness() {
    local case_name="Robustness100_witness"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}5_planning/robotic_robustness_100.smv \
               ${FOLDER}5_planning/robotic_robustness_100.smv \
               -f ${FOLDER}5_planning/robotic_robustness_formula.hq \
               -k 20 -s hpes -c"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_robustness_100.smv \
               ${FOLDER}AH_formulas/5.1.hq \
               --incl-forq --witness"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}5_planning/robotic_sp_100.smv \
               ${FOLDER}5_planning/robotic_sp_100.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 20 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_100.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}5_planning/robotic_sp_400.smv \
               ${FOLDER}5_planning/robotic_sp_400.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 40 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_400.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}5_planning/robotic_sp_1600.smv \
               ${FOLDER}5_planning/robotic_sp_1600.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 40 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_1600.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
               -n ${FOLDER}5_planning/robotic_sp_1600.smv \
               ${FOLDER}5_planning/robotic_sp_1600.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 40 -s hpes -q"
            ;;
        *)
            echo "Usage: case_sp1600 <1|2|3> or <smt|ah|qbf>"
            return 1
            ;;
    esac
}


case_sp3600() {
    local case_name="SP3600"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}5_planning/robotic_sp_3600.smv \
               ${FOLDER}5_planning/robotic_sp_3600.smv \
               -f ${FOLDER}5_planning/robotic_sp_formula.hq \
               -k 120 -s hpes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}5_planning/robotic_sp_3600.smv \
               ${FOLDER}AH_formulas/5.2.hq \
               "
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
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
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- \
               -n ${FOLDER}6_mutation/mutation_testing.smv \
               ${FOLDER}6_mutation/mutation_testing.smv \
               -f ${FOLDER}6_mutation/mutation_testing.hq \
               -k 5 -s pes"
            ;;
        2|ah)
            printf "\n[AutoHyper]   Running %s...\n" "$case_name"
            time_run "$case_name" "AH" \
              "AutoHyper/app/AutoHyper \
               --nusmv ${FOLDER}6_mutation/mutation_testing.smv \
               ${FOLDER}AH_formulas/6.hq"
            ;;
        3|qbf)
            printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
            time_run "$case_name" "QBF" \
              "cargo run --release -- \
               -n ${FOLDER}6_mutation/mutation_testing.smv \
               ${FOLDER}6_mutation/mutation_testing.smv \
               -f ${FOLDER}6_mutation/mutation_testing.hq \
               -k 5 -s pes -q"
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

usage() {
  cat <<EOF
Usage: $0 [mode]
  -all <mode>             Run all cases with the chosen mode (smt|ah|qbf)
  -light <mode>           Run lightweight cases with the chosen mode (smt|ah|qbf)
  -compare all            Run all cases with all modes (smt/ah/qbf)
  -compare light          Run lightweight cases with all modes (smt/ah/qbf)
  -list                   List all available case functions
  -compare <case_name>    Run one case with all modes (see -list for case selections)
  -case <func> <mode>     Run one case with selected mode (smt|ah|qbf)
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
    if ! declare -f "$fn" >/dev/null 2>&1; then
      echo "(!) Missing case function: $fn"
      exit 1
    fi
    for m in "${modes[@]}"; do
      "$fn" "$m"
    done
  done
  render_tables
}

LIGHT_CASES=()
for case_fn in "${CASES[@]}"; do
  case "$case_fn" in
    bakery9|bakery11|rb1600|rb3600|sp400|sp1600|sp3600) ;;
    *) LIGHT_CASES+=("$case_fn");;
  esac
done

run_light_compare_matrix() {
  local modes=("$@")
  for c in "${LIGHT_CASES[@]}"; do
    local fn="case_${c}"
    if ! declare -f "$fn" >/dev/null 2>&1; then
      echo "(!) Missing case function: $fn"
      exit 1
    fi
    for m in "${modes[@]}"; do
      "$fn" "$m"
    done
  done
  render_tables
}

run_light_mode() {
  local mode="$1"
  for c in "${LIGHT_CASES[@]}"; do
    local fn="case_${c}"
    if ! declare -f "$fn" >/dev/null 2>&1; then
      echo "(!) Missing case function: $fn"
      exit 1
    fi
    "$fn" "$mode"
  done
  render_tables
}

run_single_case_matrix() {
  local case_name="$1"; shift
  local modes=("$@")
  local fn="case_${case_name}"
  if declare -f "$fn" >/dev/null 2>&1; then
    for m in "${modes[@]}"; do
      "$fn" "$m"
    done
    render_tables
  else
    echo "(!) Unknown case: $case_name"
    list_cases
    exit 1
  fi
}

case "${1:-}" in
  -compare)
    shift
    compare_target="${1:-}"
    if [[ -z "$compare_target" ]]; then
      echo "(!) The '-compare' option requires an argument."
      echo "   Usage: $0 -compare [all|light|<case_name>]"
      echo
      list_cases
      exit 1
    fi
    case "$compare_target" in
      all)
        run_matrix smt ah qbf
        ;;
      light)
        run_light_compare_matrix smt ah qbf
        ;;
      *)
        run_single_case_matrix "$compare_target" smt ah qbf
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
    run_matrix "$mode"
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
    run_light_mode "$mode"
    ;;

  -case)
    shift
    func="${1:-}"; mode="${2:-}"
    [[ -z "$func" || -z "$mode" ]] && usage
    fn="case_${func}"
    if declare -f "$fn" >/dev/null 2>&1; then
      "$fn" "$mode"
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
