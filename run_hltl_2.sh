#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-100}  # seconds

FOLDER="benchmarks/sync/"

# ---- Paths for results/logs ----
RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/table5_runtimes.csv"
MD="${RESULTS_DIR}/table5_runtimes.md"



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
        (
          "$TIMEOUT_BIN" "$TIMEOUT_SEC" bash -c \
            "gtime -f '%e,%U,%S,%M' -o '$tmp' bash -c \"$cmd\""
        ) > >(tee -a "$log_file") 2> >(tee -a "$log_file" >&2)
        exit_code=$?
    else
        (
          gtime -f "%e,%U,%S,%M" -o "$tmp" bash -c "$cmd"
        ) > >(tee -a "$log_file") 2> >(tee -a "$log_file" >&2)
        exit_code=$?
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
  echo "=== Table 5 runtimes (New HyperLTL cases) ==="
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

#=== Co-termination ===#
case_coterm() {
  local case_name="Co-termination"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}7_coterm/coterm1.smv \
         ${FOLDER}7_coterm/coterm1.smv \
         -f ${FOLDER}7_coterm/coterm.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}7_coterm/coterm1.smv \
         ${FOLDER}AH_formulas/7.hq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}7_coterm/coterm1.smv \
         ${FOLDER}7_coterm/coterm1.smv \
         -f ${FOLDER}7_coterm/coterm.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_coterm1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Deniability ===#
case_deniability() {
  local case_name="Deniability"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}8_deniability/electronic_wallet.smv \
         ${FOLDER}8_deniability/electronic_wallet.smv \
         ${FOLDER}8_deniability/electronic_wallet.smv \
         -f ${FOLDER}8_deniability/den.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}8_deniability/electronic_wallet.smv \
         ${FOLDER}AH_formulas/8.hq \
         --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}8_deniability/electronic_wallet.smv \
         ${FOLDER}8_deniability/electronic_wallet.smv \
         ${FOLDER}8_deniability/electronic_wallet.smv \
         -f ${FOLDER}8_deniability/den.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_deniability <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Shared buffer ===#
case_buffer_scheduled_classic() {
  local case_name="Buffer_ClassicOD"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}9_buffer/scheduled_buffer.smv \
         -f ${FOLDER}9_buffer/classic_OD.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}AH_formulas/9.1.hq \
         "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}9_buffer/scheduled_buffer.smv \
         -f ${FOLDER}9_buffer/classic_OD.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_buffer_scheduled_classic <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_buffer_scheduled_intrans_od() {
  local case_name="Buffer_IntransOD"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}9_buffer/scheduled_buffer.smv \
         -f ${FOLDER}9_buffer/intrans_OD.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}AH_formulas/9.2.hq \
         "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}9_buffer/scheduled_buffer.smv \
         -f ${FOLDER}9_buffer/intrans_OD.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_buffer_scheduled_intrans_od <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_buffer_scheduled_intrans_gmni() {
  local case_name="Buffer_Intrans_GMNI"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}9_buffer/scheduled_buffer.smv \
         -f ${FOLDER}9_buffer/intrans_GMNI.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}AH_formulas/9.3.hq \
         "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}9_buffer/scheduled_buffer.smv \
         -f ${FOLDER}9_buffer/intrans_GMNI.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_buffer_scheduled_intrans_gmni <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_buffer_unscheduled_classic() {
  local case_name="Buffer_ClassicOD"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}9_buffer/unscheduled_buffer.smv \
         ${FOLDER}9_buffer/unscheduled_buffer.smv \
         -f ${FOLDER}9_buffer/classic_OD.hq \
         -k 10 -s hpes -c"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}9_buffer/unscheduled_buffer.smv \
         ${FOLDER}AH_formulas/9.1.hq \
         "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}9_buffer/unscheduled_buffer.smv \
         ${FOLDER}9_buffer/unscheduled_buffer.smv \
         -f ${FOLDER}9_buffer/classic_OD.hq \
         -k 10 -s hpes -c -q"
      ;;
    *) echo "Usage: case_buffer_unscheduled_classic <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Non-determinism Experiment ===#
case_niexp_tini() {
  local case_name="NIExp_TINI"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}10_NIexp/ni_example.smv \
         ${FOLDER}10_NIexp/ni_example.smv \
         -f ${FOLDER}10_NIexp/tini.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}10_NIexp/ni_example.smv \
         ${FOLDER}AH_formulas/10.1.hq \
         --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}10_NIexp/ni_example.smv \
         ${FOLDER}10_NIexp/ni_example.smv \
         -f ${FOLDER}10_NIexp/tini.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_niexp_tini <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_niexp_tsni() {
  local case_name="NIExp_TSNI"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}10_NIexp/ni_example.smv \
         ${FOLDER}10_NIexp/ni_example.smv \
         -f ${FOLDER}10_NIexp/tsni.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}10_NIexp/ni_example.smv \
         ${FOLDER}AH_formulas/10.2.hq \
         --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}10_NIexp/ni_example.smv \
         ${FOLDER}10_NIexp/ni_example.smv \
         -f ${FOLDER}10_NIexp/tsni.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_niexp_tsni <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== k-safety ===#
case_ksafety() {
  local case_name="k_safety"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}11_ksafety/doubleSquare.smv \
         ${FOLDER}11_ksafety/doubleSquare.smv \
         -f ${FOLDER}11_ksafety/doubleSquare.hq \
         -k 50 -s hpes -c"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}11_ksafety/doubleSquare.smv \
         ${FOLDER}AH_formulas/11.hq \
         "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}11_ksafety/doubleSquare.smv \
         ${FOLDER}11_ksafety/doubleSquare.smv \
         -f ${FOLDER}11_ksafety/doubleSquare.hq \
         -k 200 -s hpes -c -q"
      ;;
    *) echo "Usage: case_ksafety <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Mapping synthesis ===#
case_mapsynth1() {
  local case_name="MapSynth1"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}12_mapsynth/msynth_MM.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}12_mapsynth/msynth_MM.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}AH_formulas/12.1.hq \
        "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}12_mapsynth/msynth_MM.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_mapsynth1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_mapsynth2() {
  local case_name="MapSynth2"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}12_mapsynth/msynth2_MM.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth2.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}12_mapsynth/msynth2_MM.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}AH_formulas/12.2.hq \
         --incl-forq"
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}12_mapsynth/msynth2_MM.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth2.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_mapsynth2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== TEAM LTL ===#
case_teamltl_v1() {
  local case_name="TeamLTL_v1"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}13_teamltl/team.smv \
         ${FOLDER}13_teamltl/team.smv \
         ${FOLDER}13_teamltl/team.smv \
         -f ${FOLDER}13_teamltl/team.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}13_teamltl/team.smv \
         ${FOLDER}AH_formulas/13.1.hq \
         "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}13_teamltl/team.smv \
         ${FOLDER}13_teamltl/team.smv \
         ${FOLDER}13_teamltl/team.smv \
         -f ${FOLDER}13_teamltl/team.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_teamltl_v1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_teamltl_v2() {
  local case_name="TeamLTL_v2"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}13_teamltl/team2.smv \
         ${FOLDER}13_teamltl/team2.smv \
         ${FOLDER}13_teamltl/team2.smv \
         -f ${FOLDER}13_teamltl/team.hq \
         -k 21 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}13_teamltl/team2.smv \
         ${FOLDER}AH_formulas/13.2.hq \
         "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}13_teamltl/team2.smv \
         ${FOLDER}13_teamltl/team2.smv \
         ${FOLDER}13_teamltl/team2.smv \
         -f ${FOLDER}13_teamltl/team.hq \
         -k 21 -s hpes -q"
      ;;
    *) echo "Usage: case_teamltl_v2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== NDET ===#
case_ndet_v1() {
  local case_name="NDET_v1"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}14_ndet/NI_v1.smv \
         ${FOLDER}14_ndet/NI_v1.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}14_ndet/NI_v1.smv \
         ${FOLDER}AH_formulas/14.hq \
         --incl-forq"
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}14_ndet/NI_v1.smv \
         ${FOLDER}14_ndet/NI_v1.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_ndet_v1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_ndet_v2() {
  local case_name="NDET_v2"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}14_ndet/NI_v2.smv \
         ${FOLDER}14_ndet/NI_v2.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}14_ndet/NI_v2.smv \
         ${FOLDER}AH_formulas/14.hq \
         --incl-forq"
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}14_ndet/NI_v2.smv \
         ${FOLDER}14_ndet/NI_v2.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_ndet_v2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_ndet_v3() {
  local case_name="NDET_v3"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}14_ndet/NI_v3.smv \
         ${FOLDER}14_ndet/NI_v3.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}14_ndet/NI_v3.smv \
         ${FOLDER}AH_formulas/14.hq \
         --incl-forq"
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}14_ndet/NI_v3.smv \
         ${FOLDER}14_ndet/NI_v3.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_ndet_v3 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Bank ===#
case_bank_v1() {
  local case_name="Bank_v1"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}15_bank/bank3_complex_V1.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}AH_formulas/15.hq \
         "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}15_bank/bank3_complex_V1.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_bank_v1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_bank_v2() {
  local case_name="Bank_v2"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}15_bank/bank3_complex_V2.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}AH_formulas/15.hq \
         "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}15_bank/bank3_complex_V2.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_bank_v2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_bank_v3() {
  local case_name="Bank_v3"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}15_bank/bank3_complex_V3.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}AH_formulas/15.hq \
        "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}15_bank/bank3_complex_V3.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_bank_v3 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Constructor ===#
case_constructor() {
  local case_name="Constructor"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}16_constructor/constructor_atomic.smv \
         ${FOLDER}16_constructor/constructor_seq.smv \
         -f ${FOLDER}16_constructor/Linearizability.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}16_constructor/constructor_atomic.smv \
         ${FOLDER}16_constructor/constructor_seq.smv \
         ${FOLDER}AH_formulas/16.hq \
         "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}16_constructor/constructor_atomic.smv \
         ${FOLDER}16_constructor/constructor_seq.smv \
         -f ${FOLDER}16_constructor/Linearizability.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_constructor <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}


#=== bidding ===#
case_bidding_safe_1() {
  local case_name="Bidding_v1"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_safe.smv \
         ${FOLDER}18_bidding/bid_safe.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_safe.smv \
         ${FOLDER}AH_formulas/18.hq \
      "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_safe.smv \
         ${FOLDER}18_bidding/bid_safe.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_bidding_safe_1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_bidding_safe_2() {
  local case_name="Bidding_v2"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_safe_2.smv \
         ${FOLDER}18_bidding/bid_safe_2.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_safe_2.smv \
         ${FOLDER}AH_formulas/18.hq \
         "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_safe_2.smv \
         ${FOLDER}18_bidding/bid_safe_2.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_bidding_safe_2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_bidding_safe_3() {
  local case_name="Bidding_v3"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_safe_4.smv \
         ${FOLDER}18_bidding/bid_safe_4.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_safe_4.smv \
         ${FOLDER}AH_formulas/18.hq \
         "
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_safe_4.smv \
         ${FOLDER}18_bidding/bid_safe_4.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_bidding_safe_3 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_bidding_unsafe() {
  local case_name="Bidding_unsafe"
  local mode="${1:-}"
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
      local smt_cmd="${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_unsafe.smv \
         ${FOLDER}18_bidding/bid_unsafe.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes"
      time_run "$case_name" "SMT" "$smt_cmd"
      if (( want_witness )); then
        local smt_cmd_witness="$smt_cmd"
        [[ "$smt_cmd_witness" != *" -c"* ]] && smt_cmd_witness+=" -c"
        time_run "$case_name" "SMT_witness" "$smt_cmd_witness"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      local ah_cmd="AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_unsafe.smv \
         ${FOLDER}AH_formulas/18.hq \
         "
      time_run "$case_name" "AH" "$ah_cmd"
      if (( want_witness )); then
        local ah_cmd_witness="$ah_cmd"
        [[ "$ah_cmd_witness" != *"--witness"* ]] && ah_cmd_witness+=" --witness"
        time_run "$case_name" "AH_witness" "$ah_cmd_witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}18_bidding/bid_unsafe.smv \
         ${FOLDER}18_bidding/bid_unsafe.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_bidding_unsafe <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== IQueue ===#
case_iqueue() {
  local case_name="IQueue"
  local mode="${1:-}"
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
         -n ${FOLDER}19_iqueue/iqueue_conc.smv \
         ${FOLDER}19_iqueue/iqueue_seq.smv \
         -f ${FOLDER}19_iqueue/iqueue.hq \
         -k 10 -s hpes"
      if (( want_witness )); then
        time_run "$case_name" "SMT_witness" \
          "${CARGO_BIN} \
           -n ${FOLDER}19_iqueue/iqueue_conc.smv \
           ${FOLDER}19_iqueue/iqueue_seq.smv \
           -f ${FOLDER}19_iqueue/iqueue.hq \
           -k 10 -s hpes -c"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}19_iqueue/iqueue_conc.smv \
         ${FOLDER}19_iqueue/iqueue_seq.smv \
         ${FOLDER}AH_formulas/19.hq \
         "
      if (( want_witness )); then
        time_run "$case_name" "AH_witness" \
          "AutoHyper/app/AutoHyper \
           --nusmv ${FOLDER}19_iqueue/iqueue_conc.smv \
           ${FOLDER}19_iqueue/iqueue_seq.smv \
           ${FOLDER}AH_formulas/19.hq \
           --witness --witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}19_iqueue/iqueue_conc.smv \
         ${FOLDER}19_iqueue/iqueue_seq.smv \
         -f ${FOLDER}19_iqueue/iqueue.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_iqueue <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Keypad ===#
case_keypad() {
  local case_name="Keypad"
  local mode="${1:-}"
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
         -n ${FOLDER}20_keypad/keypad.smv \
         ${FOLDER}20_keypad/keypad.smv \
         -f ${FOLDER}20_keypad/keypad_2.hq \
         -k 10 -s hpes"
      if (( want_witness )); then
        time_run "$case_name" "SMT_witness" \
          "${CARGO_BIN} \
           -n ${FOLDER}20_keypad/keypad.smv \
           ${FOLDER}20_keypad/keypad.smv \
           -f ${FOLDER}20_keypad/keypad_2.hq \
           -k 10 -s hpes -c"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}20_keypad/keypad.smv \
         ${FOLDER}AH_formulas/20.hq \
         "
      if (( want_witness )); then
        time_run "$case_name" "AH_witness" \
          "AutoHyper/app/AutoHyper \
           --nusmv ${FOLDER}20_keypad/keypad.smv \
           ${FOLDER}AH_formulas/20.hq \
           --witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}20_keypad/keypad.smv \
         ${FOLDER}20_keypad/keypad.smv \
         -f ${FOLDER}20_keypad/keypad_2.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_keypad <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Queue (LIN) ===#
case_simple_queue() {
  local case_name="SimpleQueue"
  local mode="${1:-}"
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
         -n ${FOLDER}21_queue/concurrent.smv \
         ${FOLDER}21_queue/atomic.smv \
         -f ${FOLDER}21_queue/lin.hq \
         -k 10 -s hpes"
      if (( want_witness )); then
        time_run "$case_name" "SMT_witness" \
          "${CARGO_BIN} \
           -n ${FOLDER}21_queue/concurrent.smv \
           ${FOLDER}21_queue/atomic.smv \
           -f ${FOLDER}21_queue/lin.hq \
           -k 10 -s hpes -c"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}21_queue/concurrent.smv \
         ${FOLDER}21_queue/atomic.smv \
         ${FOLDER}AH_formulas/21.hq \
         "
      if (( want_witness )); then
        time_run "$case_name" "AH_witness" \
          "AutoHyper/app/AutoHyper \
           --nusmv ${FOLDER}21_queue/concurrent.smv \
           ${FOLDER}21_queue/atomic.smv \
           ${FOLDER}AH_formulas/21.hq \
           --witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}21_queue/atomic.smv \
         ${FOLDER}21_queue/concurrent.smv \
         -f ${FOLDER}21_queue/lin2.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_simple_queue <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== EMM_ABA ===#
case_emm_aba() {
  local case_name="EMM_ABA"
  local mode="${1:-}"
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
         -n ${FOLDER}22_emm_aba/emm_aba_conc.smv \
         ${FOLDER}22_emm_aba/emm_aba_seq.smv \
         -f ${FOLDER}22_emm_aba/emm_aba.hq \
         -k 6 -s hpes"
      if (( want_witness )); then
        time_run "$case_name" "SMT_witness" \
          "${CARGO_BIN} \
           -n ${FOLDER}22_emm_aba/emm_aba_conc.smv \
           ${FOLDER}22_emm_aba/emm_aba_seq.smv \
           -f ${FOLDER}22_emm_aba/emm_aba.hq \
           -k 6 -s hpes -c"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}22_emm_aba/emm_aba_conc.smv \
         ${FOLDER}22_emm_aba/emm_aba_seq.smv \
         ${FOLDER}AH_formulas/22.hq \
         --incl-forq"
      if (( want_witness )); then
        time_run "$case_name" "AH_witness" \
          "AutoHyper/app/AutoHyper \
           --nusmv ${FOLDER}22_emm_aba/emm_aba_conc.smv \
           ${FOLDER}22_emm_aba/emm_aba_seq.smv \
           ${FOLDER}AH_formulas/22.hq \
           --incl-forq --witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}22_emm_aba/emm_aba_conc.smv \
         ${FOLDER}22_emm_aba/emm_aba_seq.smv \
         -f ${FOLDER}22_emm_aba/emm_aba.hq \
         -k 6 -s hpes -q"
      ;;
    *) echo "Usage: case_emm_aba <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Lazy list ===#
case_lazy_list() {
  local case_name="LazyList"
  local mode="${1:-}"
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
         -n ${FOLDER}23_lazy_list/lazy_list_conc.smv \
         ${FOLDER}23_lazy_list/lazy_list_seq.smv \
         -f ${FOLDER}23_lazy_list/lazy_list.hq \
         -k 13 -s hpes"
      if (( want_witness )); then
        time_run "$case_name" "SMT_witness" \
          "${CARGO_BIN} \
           -n ${FOLDER}23_lazy_list/lazy_list_conc.smv \
           ${FOLDER}23_lazy_list/lazy_list_seq.smv \
           -f ${FOLDER}23_lazy_list/lazy_list.hq \
           -k 13 -s hpes -c"
      fi
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}23_lazy_list/lazy_list_conc.smv \
         ${FOLDER}23_lazy_list/lazy_list_seq.smv \
         ${FOLDER}AH_formulas/23.hq \
         --incl-forq"
      if (( want_witness )); then
        time_run "$case_name" "AH_witness" \
          "AutoHyper/app/AutoHyper \
           --nusmv ${FOLDER}23_lazy_list/lazy_list_conc.smv \
           ${FOLDER}23_lazy_list/lazy_list_seq.smv \
           ${FOLDER}AH_formulas/23.hq \
           --incl-forq --witness"
      fi
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "${CARGO_BIN} \
         -n ${FOLDER}23_lazy_list/lazy_list_conc.smv \
         ${FOLDER}23_lazy_list/lazy_list_seq.smv \
         -f ${FOLDER}23_lazy_list/lazy_list.hq \
         -k 13 -s hpes -q"
      ;;
    *) echo "Usage: case_lazy_list <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

# ------------
# MAIN DRIVER
# ------------

# Register the cases available for -compare (use names without the `case_` prefix)
CASES=(
  # --- Co-termination ---
  coterm

  # --- Deniability ---
  deniability

  # --- Shared buffer ---
  buffer_scheduled_classic
  buffer_scheduled_intrans_od
  buffer_scheduled_intrans_gmni
  buffer_unscheduled_classic

  # --- Non-determinism Experience ---
  niexp_tini
  niexp_tsni

  # --- k-safety ---
  ksafety

  # --- Mapping synthesis ---
  mapsynth1
  mapsynth2

  # --- TEAM LTL ---
  teamltl_v1
  teamltl_v2

  # --- NDET ---
  ndet_v1
  ndet_v2
  ndet_v3

  # --- Bank ---
  bank_v1
  bank_v2
  bank_v3

  # --- Constructor (LIN) ---
  constructor

  # --- Bidding ---
  bidding_safe_1
  bidding_safe_2
  bidding_safe_3
  bidding_unsafe

  # --- IQueue (LIN) ---
  iqueue

  # --- Keypad ---
  keypad

  # --- Queue (LIN) ---
  simple_queue

  # --- EMM_ABA (LIN) ---
  emm_aba

  # --- Lazy list (LIN) ---
  lazy_list
)


usage() {
  cat <<EOF
Usage: $0 [option]
  -list                   List available case names
  -all <mode> [extras]             Run all cases with the chosen mode (smt|ah|qbf)
  -light <mode> [extras]           Run lightweight cases (excluding MapSynth2, IQueue, LazyList) with the chosen mode
  -compare all [extras]            Run all cases with all modes (smt/ah/qbf)
  -compare light [extras]          Run lightweight cases with all modes
  -compare <case> [extras]         Run one case with all modes (see -list for names)
  -case <case> <mode> [extras]     Run one case with the selected mode (smt|ah|qbf)

Case names are specified without the leading 'case_' prefix.
Extra flags:
  give_witness            Extend SMT/AH variants with witness runs (when supported)
EOF
  exit 1
}
LIGHT_CASES=()
for case_fn in "${CASES[@]}"; do
  case "$case_fn" in
    mapsynth2|ndet_v3|iqueue|emm_aba|lazy_list) ;;
    *) LIGHT_CASES+=("$case_fn");;
  esac
done

usage() {
  cat <<EOF
Usage: $0 [mode]
  -all <mode>             Run all cases with the chosen mode (smt|ah|qbf)
  -light <mode>           Run lightweight cases with the chosen mode (smt|ah|qbf)
  -compare all [extras]   Run all cases with all modes (smt/ah/qbf)
  -compare light [extras] Run lightweight cases with all modes (smt/ah/qbf)
  -list                   List all available case functions
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
      echo "   Usage: $0 -compare [all|light|<case_name>]"
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
