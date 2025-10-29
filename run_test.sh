#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-60}
BOUND=${BOUND:-6}
STEPS=${STEPS:-hpes}

if command -v gtimeout >/dev/null 2>&1; then
  TIMEOUT_BIN="gtimeout"
elif command -v timeout >/dev/null 2>&1; then
  TIMEOUT_BIN="timeout"
else
  TIMEOUT_BIN=""
fi

RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/run_test.csv"
MD="${RESULTS_DIR}/run_test.md"

mkdir -p "${LOG_DIR}"
echo "case,variant,result,real_s,log" > "${CSV}"

time_run() {
    local case_name="$1"; shift
    local variant="$1"; shift

    local log_base="${case_name// /_}_${variant// /_}"
    local log_file="${LOG_DIR}/${log_base}.log"
    local tmp
    tmp="$(mktemp)"

    local cmd="$*"
    local exit_code=0

    set +e
    if [[ -n "${TIMEOUT_BIN:-}" ]]; then
        "$TIMEOUT_BIN" "$TIMEOUT_SEC" bash -c \
          "gtime -f '%e,%U,%S,%M' -o '$tmp' bash -c \"$cmd\"" \
          2>&1 | tee "${log_file}"
        exit_code=${PIPESTATUS[0]}
    else
        gtime -f "%e,%U,%S,%M" -o "$tmp" bash -c "$cmd" \
          2>&1 | tee "${log_file}"
        exit_code=${PIPESTATUS[0]}
    fi
    set -e

    IFS=, read -r real_s _user_s _sys_s _max_rss < "$tmp" || true
    rm -f "$tmp"

    local status="NA"
    if [[ -n "${TIMEOUT_BIN:-}" && $exit_code -eq 124 ]]; then
        status="TIMEOUT"
        real_s="${TIMEOUT_SEC}"
    else
        if grep -qiwo 'UNSAT' "$log_file"; then
            status="UNSAT"
        elif grep -qiwo 'SAT' "$log_file"; then
            status="SAT"
        elif [[ $exit_code -ne 0 ]]; then
            status="ERROR"
            real_s="NA"
        fi
    fi

    printf "%s,%s,%s,%s,%s\n" \
        "$case_name" "$variant" "$status" "${real_s:-0.0}" "$log_file" >> "$CSV"
}

render_tables() {
  echo
  echo "=== InfoFlow runtimes ==="
  column -s, -t < "$CSV" | sed '1s/^/**/;1s/$/**/' | column -t

  {
    echo "| Case | Variant | Result | Real (s) | Log |"
    echo "|------|---------|--------|---------:|-----|"
    tail -n +2 "$CSV" | awk -F, '{printf "| %s | %s | %s | %s | %s |\n",$1,$2,$3,$4,$5}'
  } > "$MD"
  printf "\nMarkdown table written to: %s\n" "$MD"
}

CASE_NAME="INFOFLOW"
SMV_FILE="benchmarks/sync/0_infoflow/info.smv"
HQ_FILE="benchmarks/sync/0_infoflow/info.hq"

echo "[HyperQB SMT] Running ${CASE_NAME}..."
time_run "$CASE_NAME" "SMT" \
  "cargo run --release -- \
   -n ${SMV_FILE} ${SMV_FILE} \
   -f ${HQ_FILE} \
   -k ${BOUND} -s ${STEPS}"

echo "[HyperQB QBF] Running ${CASE_NAME}..."
time_run "$CASE_NAME" "QBF" \
  "cargo run --release -- \
   -n ${SMV_FILE} ${SMV_FILE} \
   -f ${HQ_FILE} \
   -k ${BOUND} -s ${STEPS} -q"

render_tables
