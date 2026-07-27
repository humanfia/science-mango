#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARCHON_VENV="/root/proposal_for_physic/science-mango/.venv"
ARCHON_BIN="$ARCHON_VENV/bin/archon"
RUNTIME_DIR="$RUN_ROOT/.archon/runtime"
PID_FILE="$RUNTIME_DIR/ipho_2026_archon.pid"
LOG_FILE="$RUNTIME_DIR/ipho_2026_archon.log"

mkdir -p "$RUNTIME_DIR"

if [[ -s "$PID_FILE" ]]; then
    existing_pid="$(<"$PID_FILE")"
    if kill -0 "$existing_pid" 2>/dev/null; then
        echo "IPhO 2026 Archon is already running (PID $existing_pid)."
        exit 0
    fi
fi

resume_args=()
if [[ "${1:-}" == "--resume" ]]; then
    resume_args+=("--resume")
elif [[ -n "${1:-}" ]]; then
    echo "Usage: $0 [--resume]" >&2
    exit 2
fi

"$RUN_ROOT/scripts/start_lean_explore.sh"

nohup setsid env PATH="$ARCHON_VENV/bin:$PATH" PYTHONUNBUFFERED=1 \
    "$ARCHON_BIN" loop "$RUN_ROOT" \
    --max-iterations 100 \
    --max-parallel 28 \
    --max-objectives 28 \
    --no-dashboard \
    "${resume_args[@]}" \
    >>"$LOG_FILE" 2>&1 < /dev/null &
archon_pid=$!
printf '%s\n' "$archon_pid" > "$PID_FILE"

sleep 5
if ! kill -0 "$archon_pid" 2>/dev/null; then
    echo "Archon exited during startup. Recent log:" >&2
    tail -n 100 "$LOG_FILE" >&2 || true
    exit 1
fi

echo "IPhO 2026 Archon started in background (PID $archon_pid)."
echo "Log: $LOG_FILE"
