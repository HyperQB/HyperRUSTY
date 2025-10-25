#!/bin/bash
set -euo pipefail

TIMEOUT_SEC=${TIMEOUT_SEC:-10}  # seconds

# Detect timeout binary safely (avoid unbound variable errors)
if command -v gtimeout >/dev/null 2>&1; then
  TIMEOUT_BIN="gtimeout"
elif command -v timeout >/dev/null 2>&1; then
  TIMEOUT_BIN="timeout"
else
  TIMEOUT_BIN=""   # fallback: no timeout available
fi

# ---- Paths for results/logs ----
RESULTS_DIR="_outfiles"
LOG_DIR="${RESULTS_DIR}/logs"
CSV="${RESULTS_DIR}/table2_runtimes.csv"
MD="${RESULTS_DIR}/table2_runtimes.md"

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
echo "case,variant,real_s,log" > "$CSV"

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
    echo "| Case | Variant | Exit | Real (s) | User (s) | Sys (s) | MaxRSS (KB) | Log |"
    echo "|------|---------|------|----------:|---------:|--------:|------------:|-----|"
    tail -n +2 "$CSV" | awk -F, '{printf "| %s | %s | %s | %.3f | %.3f | %.3f | %s | %s |\n",$2,$3,$4,$5,$6,$7,$8,$9}'
  } > "$MD"
  printf "\nMarkdown table written to: $MD"
}


FOLDER="benchmarks/sync/"
# --------------------------
# ---- Case definitions ----
# --------------------------

#=== Co-termination ===#
case_coterm1() {
  local case_name="Co-term1"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
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
        "cargo run --release -- \
         -n ${FOLDER}7_coterm/coterm1.smv \
         ${FOLDER}7_coterm/coterm1.smv \
         -f ${FOLDER}7_coterm/coterm.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_coterm1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Deniability ===#
case_e_wallet() {
  local case_name="Deniability"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
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
         --log --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}8_deniability/electronic_wallet.smv \
         ${FOLDER}8_deniability/electronic_wallet.smv \
         ${FOLDER}8_deniability/electronic_wallet.smv \
         -f ${FOLDER}8_deniability/den.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_e_wallet <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Shared buffer ===#
case_buffer_scheduled_classic() {
  local case_name="Buffer_ClassicOD"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}9_buffer/scheduled_buffer.smv \
         -f ${FOLDER}9_buffer/classic_OD.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}9_buffer/scheduled_buffer.smv \
         ${FOLDER}AH_formulas/9.1.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
        "cargo run --release -- \
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
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
        "cargo run --release -- \
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
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}9_buffer/unscheduled_buffer.smv \
         ${FOLDER}9_buffer/unscheduled_buffer.smv \
         -f ${FOLDER}9_buffer/classic_OD.hq \
         -k 10 -s hpes -c"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}9_buffer/unscheduled_buffer.smv \
         ${FOLDER}AH_formulas/9.1.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}9_buffer/unscheduled_buffer.smv \
         ${FOLDER}9_buffer/unscheduled_buffer.smv \
         -f ${FOLDER}9_buffer/classic_OD.hq \
         -k 10 -s hpes -c -q"
      ;;
    *) echo "Usage: case_buffer_unscheduled_classic <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Non-determinism Experience ===#
case_niexp_tini() {
  local case_name="NIExp_TINI"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
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
         --log --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
        "cargo run --release -- \
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
         --log --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}10_NIexp/ni_example.smv \
         ${FOLDER}10_NIexp/ni_example.smv \
         -f ${FOLDER}10_NIexp/tsni.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_niexp_tsni <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== k-safety ===#
case_ksafety_doubleSquare() {
  local case_name="k_safety"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
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
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}11_ksafety/doubleSquare.smv \
         ${FOLDER}11_ksafety/doubleSquare.smv \
         -f ${FOLDER}11_ksafety/doubleSquare.hq \
         -k 50 -s hpes -c -q"
      ;;
    *) echo "Usage: case_ksafety_doubleSquare <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Mapping synthesis ===#
case_mapsynth_msynth() {
  local case_name="MapSynth1"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}12_mapsynth/msynth_MM.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}12_mapsynth/msynth_MM.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}AH_formulas/12.1.hq \
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}12_mapsynth/msynth_MM.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         ${FOLDER}12_mapsynth/msynth_MA.smv \
         ${FOLDER}12_mapsynth/msynth_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_mapsynth_msynth <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_mapsynth_msynth2() {
  local case_name="MapSynth2"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}12_mapsynth/msynth2_MM.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth2.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}12_mapsynth/msynth2_MM.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}AH_formulas/12.2.hq \
         --log --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}12_mapsynth/msynth2_MM.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         ${FOLDER}12_mapsynth/msynth2_MA.smv \
         ${FOLDER}12_mapsynth/msynth2_MB.smv \
         -f ${FOLDER}12_mapsynth/msynth2.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_mapsynth_msynth2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== TEAM LTL ===#
case_teamltl_team() {
  local case_name="TeamLTL_v1"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
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
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}13_teamltl/team.smv \
         ${FOLDER}13_teamltl/team.smv \
         ${FOLDER}13_teamltl/team.smv \
         -f ${FOLDER}13_teamltl/team.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_teamltl_team <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_teamltl_team2() {
  local case_name="TeamLTL_v2"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
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
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}13_teamltl/team2.smv \
         ${FOLDER}13_teamltl/team2.smv \
         ${FOLDER}13_teamltl/team2.smv \
         -f ${FOLDER}13_teamltl/team.hq \
         -k 21 -s hpes -q"
      ;;
    *) echo "Usage: case_teamltl_team2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== NDET ===#
case_ndet_ni_v1() {
  local case_name="NDET_v1"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}14_ndet/NI_v1.smv \
         ${FOLDER}14_ndet/NI_v1.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}14_ndet/NI_v1.smv \
         ${FOLDER}AH_formulas/14.hq \
         --log --witness --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}14_ndet/NI_v1.smv \
         ${FOLDER}14_ndet/NI_v1.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_ndet_ni_v1 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_ndet_ni_v2() {
  local case_name="NDET_v2"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}14_ndet/NI_v2.smv \
         ${FOLDER}14_ndet/NI_v2.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}14_ndet/NI_v2.smv \
         ${FOLDER}AH_formulas/14.hq \
         --log --witness --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}14_ndet/NI_v2.smv \
         ${FOLDER}14_ndet/NI_v2.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_ndet_ni_v2 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

case_ndet_ni_v3() {
  local case_name="NDET_v3"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}14_ndet/NI_v3.smv \
         ${FOLDER}14_ndet/NI_v3.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}14_ndet/NI_v3.smv \
         ${FOLDER}AH_formulas/14.hq \
         --log --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}14_ndet/NI_v3.smv \
         ${FOLDER}14_ndet/NI_v3.smv \
         -f ${FOLDER}14_ndet/NI.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_ndet_ni_v3 <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Bank ===#
case_bank_v1() {
  local case_name="Bank_v1"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}15_bank/bank3_complex_V1.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}15_bank/bank3_complex_V1.smv \
         ${FOLDER}AH_formulas/15.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}15_bank/bank3_complex_V2.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}15_bank/bank3_complex_V2.smv \
         ${FOLDER}AH_formulas/15.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}15_bank/bank3_complex_V3.smv \
         -f ${FOLDER}15_bank/gmni.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}15_bank/bank3_complex_V3.smv \
         ${FOLDER}AH_formulas/15.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}16_constructor/constructor_conc.smv \
         ${FOLDER}16_constructor/constructor_seq.smv \
         -f ${FOLDER}16_constructor/Linearizability.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}16_constructor/constructor_conc.smv \
         ${FOLDER}16_constructor/constructor_seq.smv \
         ${FOLDER}AH_formulas/16.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}16_constructor/constructor_conc.smv \
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
        "cargo run --release -- \
         -n ${FOLDER}18_bidding/bid_safe.smv \
         ${FOLDER}18_bidding/bid_safe.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_safe.smv \
         ${FOLDER}AH_formulas/18.hq \
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
        "cargo run --release -- \
         -n ${FOLDER}18_bidding/bid_safe_2.smv \
         ${FOLDER}18_bidding/bid_safe_2.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_safe_2.smv \
         ${FOLDER}AH_formulas/18.hq \
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
        "cargo run --release -- \
         -n ${FOLDER}18_bidding/bid_safe_4.smv \
         ${FOLDER}18_bidding/bid_safe_4.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_safe_4.smv \
         ${FOLDER}AH_formulas/18.hq \
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}18_bidding/bid_unsafe.smv \
         ${FOLDER}18_bidding/bid_unsafe.smv \
         -f ${FOLDER}18_bidding/bidding.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}18_bidding/bid_unsafe.smv \
         ${FOLDER}AH_formulas/18.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}19_iqueue/iqueue_conc.smv \
         ${FOLDER}19_iqueue/iqueue_seq.smv \
         -f ${FOLDER}19_iqueue/iqueue.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}19_iqueue/iqueue_conc.smv \
         ${FOLDER}19_iqueue/iqueue_seq.smv \
         ${FOLDER}AH_formulas/19.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}20_keypad/keypad.smv \
         ${FOLDER}20_keypad/keypad.smv \
         -f ${FOLDER}20_keypad/keypad_2.hq \
         -k 10 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}20_keypad/keypad.smv \
         ${FOLDER}AH_formulas/20.hq \
         --log --witness"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}20_keypad/keypad.smv \
         ${FOLDER}20_keypad/keypad.smv \
         -f ${FOLDER}20_keypad/keypad_2.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_keypad <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== Queue (LIN) ===#
case_queue_lin() {
  local case_name="SimpleQueue"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}21_queue/concurrent.smv \
         ${FOLDER}21_queue/atomic.smv \
         -f ${FOLDER}21_queue/lin.hq \
         -k 10 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}21_queue/concurrent.smv \
         ${FOLDER}21_queue/atomic.smv \
         ${FOLDER}AH_formulas/21.hq \
         --log"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
         -n ${FOLDER}21_queue/concurrent.smv \
         ${FOLDER}21_queue/atomic.smv \
         -f ${FOLDER}21_queue/lin.hq \
         -k 10 -s hpes -q"
      ;;
    *) echo "Usage: case_queue_lin <1|2|3> or <smt|ah|qbf>"; return 1 ;;
  esac
}

#=== EMM_ABA ===#
case_emm_aba() {
  local case_name="EMM_ABA"
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}22_emm_aba/emm_aba_conc.smv \
         ${FOLDER}22_emm_aba/emm_aba_seq.smv \
         -f ${FOLDER}22_emm_aba/emm_aba.hq \
         -k 6 -s hpes -q"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}22_emm_aba/emm_aba_conc.smv \
         ${FOLDER}22_emm_aba/emm_aba_seq.smv \
         ${FOLDER}AH_formulas/22.hq \
         --log --witness --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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
  local mode="$1"
  case "$mode" in
    1|smt)
      printf "\n[HyperQB SMT] Running %s...\n" "$case_name"
      time_run "$case_name" "SMT" \
        "cargo run --release -- \
         -n ${FOLDER}23_lazy_list/lazy_list_conc.smv \
         ${FOLDER}23_lazy_list/lazy_list_seq.smv \
         -f ${FOLDER}23_lazy_list/lazy_list.hq \
         -k 13 -s hpes"
      ;;
    2|ah)
      printf "\n[AutoHyper]   Running %s...\n" "$case_name"
      time_run "$case_name" "AH" \
        "AutoHyper/app/AutoHyper \
         --nusmv ${FOLDER}23_lazy_list/lazy_list_conc.smv \
         ${FOLDER}23_lazy_list/lazy_list_seq.smv \
         ${FOLDER}AH_formulas/23.hq \
         --log --incl-forq"
      ;;
    3|qbf)
      printf "\n[HyperQB QBF] Running %s...\n" "$case_name"
      time_run "$case_name" "QBF" \
        "cargo run --release -- \
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

# Register the cases available for -compare
CASES=(
  # --- Co-termination ---
  case_coterm1

  # --- Deniability ---
  case_e_wallet

  # --- Shared buffer ---
  case_buffer_scheduled_classic
  case_buffer_scheduled_intrans_od # MMMMM
  case_buffer_scheduled_intrans_gmni
  case_buffer_unscheduled_classic

  # --- Non-determinism Experience ---
  case_niexp_tini
  case_niexp_tsni

  # --- k-safety ---
  case_ksafety_doubleSquare # MMMMM

  # --- Mapping synthesis ---
  case_mapsynth_msynth
  case_mapsynth_msynth2

  # --- TEAM LTL ---
  case_teamltl_team
  case_teamltl_team2

  # --- NDET ---
  case_ndet_ni_v1 # MMMMMM
  case_ndet_ni_v2 # MMMMMM
  case_ndet_ni_v3 # MMMMMM

  # --- Bank ---
  case_bank_v1
  case_bank_v2
  case_bank_v3

  # --- Constructor (LIN) ---
  case_constructor

  # --- Bidding ---
  case_bidding_safe_1
  case_bidding_safe_2
  case_bidding_safe_3
  case_bidding_unsafe

  # --- IQueue (LIN) ---
  case_iqueue

  # --- Keypad ---
  case_keypad

  # --- Queue (LIN) ---
  case_queue_lin # MMMMM

  # --- EMM_ABA (LIN) ---
  case_emm_aba

  # --- Lazy list (LIN) ---
  case_lazy_list
)

usage() {
  cat <<EOF
Usage: $0 [mode]
  -compare all             Run all CASES with all modes (smt, ah, qbf)
  -compare <case_name>     Run only the specified case with all modes
  -smt|-ah|-qbf            Run all CASES with the chosen mode
  -light                   Run a lightweight subset (edit inside)
  -case <func> <mode>      Run a single case function with mode (smt|ah|qbf)
  -list                    List available case functions
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
  -compare)
    shift
    if [[ -z "${1:-}" ]]; then
      echo "(!) The '-compare' option requires an argument."
      echo "   Usage: $0 -compare [all|<case_name>]"
      echo
      list_cases
      exit 1
    elif [[ "$1" == "all" ]]; then
      run_matrix smt ah qbf
    elif [[ "$1" == "battle" ]]; then
      run_matrix smt ah 
    else
      run_single_case_matrix "$1" smt ah qbf
    fi
    ;;
    
  -all)
    run_matrix smt
    ;;

  -smt|-ah|-qbf)
    mode="${1#-}"
    run_matrix "$mode"
    ;;

  -light)
    local_subset=(case_bakery3 case_bakery5)
    for c in "${local_subset[@]}"; do
      "$c" smt
    done
    render_tables
    ;;

  -case)
    shift
    func="${1:-}"; mode="${2:-}"
    [[ -z "$func" || -z "$mode" ]] && usage
    if declare -f "$func" >/dev/null 2>&1; then
      "$func" "$mode"
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