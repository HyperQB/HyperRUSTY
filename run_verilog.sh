
#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-180}  # seconds

# Detect timeout binary safely (avoid unbound variable errors)
if command -v gtimeout >/dev/null 2>&1; then
  TIMEOUT_BIN="gtimeout"
elif command -v timeout >/dev/null 2>&1; then
  TIMEOUT_BIN="timeout"
else
  TIMEOUT_BIN=""   # fallback: no timeout available
fi

# ---- Paths for results/logs ----
FOLDER="benchmarks/verilog/"
RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/table8(verilog)_results.csv"
MD="${RESULTS_DIR}/table1(verilog)_results.md"

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
  echo "=== Table 8 runtimes (verilog cases) ==="
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

case_fpu2() {
    local case_name="FPU2"
    local mode="$1"  # argument: 1=SMT, 2=AutoHyper, 3=QBF

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -v \
              ${FOLDER}divider/divider.ys \
              ${FOLDER}divider/divider.ys \
               -t divider -o model.smt2 \
               -f ${FOLDER}divider/formula.hq -k 8 -s pes"
            ;;

        *)
            echo "Usage: case_fpu2 <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_spi() {
    local case_name="SPI"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -v \
              ${FOLDER}SPI/spi_build.ys \
              ${FOLDER}SPI/spi_build.ys \
              -t SPISlave -o spi.smt2 \
              -f ${FOLDER}SPI/formula.hq -k 8 -s hpes"
            ;;

        *)
            echo "Usage: case_spi <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_led_EA() {
    local case_name="LED_EA"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -v \
              ${FOLDER}LED/build_ea.ys \
              ${FOLDER}LED/build_ea.ys \
              -t led_fsm -o model.smt2 \
              -f ${FOLDER}LED/formula_ea.hq -k 101 -s pes"
            ;;

        *)
            echo "Usage: case_led_EA <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_led_AE() {
    local case_name="LED_AE"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -v \
              ${FOLDER}LED/build_ae.ys \
              ${FOLDER}LED/build_ae.ys \
              -t led_fsm -o model.smt2 \
              -f ${FOLDER}LED/formula_ae.hq -k 10 -s pes -c"
            ;;

        *)
            echo "Usage: case_led_AE <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_led_EE_true() {
    local case_name="LED_EE"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -v \
              ${FOLDER}LED/build_ee.ys \
              ${FOLDER}LED/build_ee.ys \
              -t light -o model.smt2 \
              -f ${FOLDER}LED/formula_ee_t.hq -k 101 -s hpes"
            ;;

        *)
            echo "Usage: case_led_EE <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}

case_led_EE_false() {
    local case_name="LED_EE"
    local mode="$1"

    case "$mode" in
        1|smt)
            printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
            time_run "$case_name" "SMT" \
              "cargo run --release -- -v \
              ${FOLDER}LED/build_ee.ys \
              ${FOLDER}LED/build_ee.ys \
              -t light -o model.smt2 \
              -f ${FOLDER}LED/formula_ee_f.hq -k 101 -s hpes"
            ;;

        *)
            echo "Usage: case_led_EE <1|2> or <smt|qbf>"
            return 1
            ;;
    esac
}


# ------------
# MAIN DRIVER
# ------------

# Register the cases available for -all
CASES=(
    case_led_EA
    case_led_AE
    case_led_EE_false
    case_led_EE_true
    case_spi
    case_fpu2
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
    local_subset=(case_fpu2 case_spi case_led_EA case_led_AE case_led_EE)
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
