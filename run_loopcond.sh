
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
FOLDER="benchmarks/loop_conditions/"
RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/table7(loop)_results.csv"
MD="${RESULTS_DIR}/table7(loop)_results.md"

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
echo "case,result,real_s,log" > "$CSV"

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
    real_s=${real_s:-0.0}
    case "$real_s" in
        ''|*[!0-9.-]*) real_s=0.0 ;;
    esac
    printf "%s,%s,%.3f,%s\n" \
        "$case_name" "$status" "${real_s:-0.0}" "$log_file" >> "$CSV"
    # Append one row to CSV (full info)
    # printf "%s,%s,%s,%s,%s,%.3f,%.3f,%.3f,%s,%s\n" \
    # "$stamp" "$case_name" "$variant" "$status" "$exit_code" \
    # "$real_s" "$user_s" "$sys_s" "$max_rss_kb" "$log_file" >> "$CSV"

}

# ---- Pretty-print table (plain + markdown) ----
render_tables() {
  echo
  echo "=== Table 7 runtimes (loop condition cases) ==="
  column -s, -t < "$CSV" | sed '1s/^/**/;1s/$/**/' | column -t

  # Markdown table
  {
    echo "| Case | Result | Real (s) | Log |"
    echo "|------|--------|---------:|-----|"
    tail -n +2 "$CSV" | awk -F, '{printf "| %s | %s | %.3f | %s |\n",$1,$2,$3,$4}'
  } > "$MD"
  printf "\nMarkdown table written to: $MD"
}



# --------------------------
# ---- Case definitions ----
# --------------------------



case_abp() {
    local case_name="ABP"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}abp/abp_1.smv \
              ${FOLDER}abp/abp_2.smv \
              -f ${FOLDER}abp/abp.hq -l"
            ;;

        *)
            echo "Usage: case_abp <1|smt>"
            return 1
            ;;
    esac
}

case_abp_buggy() {
    local case_name="ABP_BUGGY"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}abp/abp_1_buggy.smv \
              ${FOLDER}abp/abp_2_buggy.smv \
              -f ${FOLDER}abp/abp.hq -l"
            ;;

        *)
            echo "Usage: case_abp_buggy <1|smt>"
            return 1
            ;;
    esac
}

case_mm() {
    local case_name="MM"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}mm/mm1.smv \
              ${FOLDER}mm/mm2.smv \
              -f ${FOLDER}mm/mm.hq -l"
            ;;

        *)
            echo "Usage: case_mm <1|smt>"
            return 1
            ;;
    esac
}

case_mm_buggy() {
    local case_name="MM_BUGGY"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}mm/mm1_buggy.smv \
              ${FOLDER}mm/mm2_buggy.smv \
              -f ${FOLDER}mm/mm.hq -l"
            ;;

        *)
            echo "Usage: case_mm_buggy <1|smt>"
            return 1
            ;;
    esac
}

case_cbf() {
    local case_name="CBF"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}cbf/cbf1.smv \
              ${FOLDER}cbf/cbf2.smv \
              -f ${FOLDER}cbf/cbf.hq -l"
            ;;

        *)
            echo "Usage: case_cbf <1|smt>"
            return 1
            ;;
    esac
}

case_cbf_buggy() {
    local case_name="CBF_BUGGY"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}cbf/cbf1_buggy.smv \
              ${FOLDER}cbf/cbf2_buggy.smv \
              -f ${FOLDER}cbf/cbf.hq -l"
            ;;

        *)
            echo "Usage: case_cbf_buggy <1|smt>"
            return 1
            ;;
    esac
}

case_rp() {
    local case_name="RP"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}robust_path_planning/rp_1.smv \
              ${FOLDER}robust_path_planning/rp_2.smv \
              -f ${FOLDER}robust_path_planning/rp.hq -l"
            ;;

        *)
            echo "Usage: case_rp <1|smt>"
            return 1
            ;;
    esac
}

case_rp_nosol() {
    local case_name="RP_NOSOL"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}robust_path_planning/rp_1_no_sol.smv \
              ${FOLDER}robust_path_planning/rp_2.smv \
              -f ${FOLDER}robust_path_planning/rp.hq -l"
            ;;

        *)
            echo "Usage: case_rp_nosol <1|smt>"
            return 1
            ;;
    esac
}

case_gcw() {
    local case_name="GCW"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}gcw/gcw1.smv \
              ${FOLDER}gcw/gcw2.smv \
              -f ${FOLDER}gcw/gcw.hq -l"
            ;;

        *)
            echo "Usage: case_gcw <1|smt>"
            return 1
            ;;
    esac
}

case_gcw_buggy() {
    local case_name="GCW_BUGGY"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -n \
              ${FOLDER}gcw/gcw1_buggy.smv \
              ${FOLDER}gcw/gcw2_buggy.smv \
              -f ${FOLDER}gcw/gcw.hq -l"
            ;;

        *)
            echo "Usage: case_gcw_buggy <1|smt>"
            return 1
            ;;
    esac
}

# ------------
# MAIN DRIVER
# ------------

# Register the cases available for -all
CASES=(
    case_abp
    case_abp_buggy
    case_mm
    case_mm_buggy
    case_cbf
    case_cbf_buggy
    case_rp
    case_rp_nosol
    case_gcw
    case_gcw_buggy
)

usage() {
  cat <<EOF
Usage: $0 [mode]
  -all              Run all CASES with smt modes
  -light            Run a lightweight subset (edit inside)
  -case <func>      Run a single case (SMT mode)
  -list             List all available cases
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
    for m in "${modes[@]}"; do
      "$c" "$m"
    done
  done
  render_tables
}

run_single_case_matrix() {
  local case_name="$1"; shift
  local modes=("$@")
  if declare -f "$case_name" >/dev/null 2>&1; then
    for m in "${modes[@]}"; do
      "$case_name" "$m"
    done
    render_tables
  else
    echo "(!) Unknown case function: $case_name"
    list_cases
    exit 1
  fi
}

case "${1:-}" in
  -all)
    run_matrix smt 
    ;;


  -light)
    local_subset=(case_abp case_abp_buggy case_mm case_mm_buggy case_cbf case_cbf_buggy case_rp case_rp_nosol case_gcw case_gcw_buggy)
    for c in "${local_subset[@]}"; do
      "$c" smt
    done
    render_tables
    ;;

  -case)
    shift
    func="${1:-}"
    [[ -z "$func" ]] && usage
    if declare -f "$func" >/dev/null 2>&1; then
      "$func" smt
      render_tables
    else
      echo "(!) Unknown case function: $func"
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
