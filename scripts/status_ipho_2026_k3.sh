#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUNTIME_DIR="$RUN_ROOT/.archon/runtime"
ARCHON_PID_FILE="$RUNTIME_DIR/ipho_2026_k3_archon.pid"
LEAN_PID_FILE="$RUNTIME_DIR/lean_explore_8765.pid"
PROXY_PID_FILE="$RUNTIME_DIR/moonshot_chat_proxy.pid"
LOG_FILE="$RUNTIME_DIR/ipho_2026_k3_archon.log"

show_process() {
    local label="$1"
    local pid_file="$2"
    if [[ ! -s "$pid_file" ]]; then
        echo "$label: no PID file"
        return
    fi
    local process_pid
    process_pid="$(<"$pid_file")"
    if kill -0 "$process_pid" 2>/dev/null; then
        echo "$label: RUNNING (PID $process_pid)"
        ps -p "$process_pid" -o pid=,etime=,%cpu=,%mem=,stat=,cmd=
    else
        echo "$label: STOPPED (stale PID $process_pid)"
    fi
}

show_process "LeanExplore" "$LEAN_PID_FILE"
show_process "Moonshot Chat proxy" "$PROXY_PID_FILE"
show_process "Archon" "$ARCHON_PID_FILE"

if curl --silent --output /dev/null --max-time 1 \
    http://127.0.0.1:8765/mcp; then
    echo "LeanExplore endpoint: READY"
else
    echo "LeanExplore endpoint: NOT READY"
fi

if curl --silent --fail --output /dev/null --max-time 1 \
    http://127.0.0.1:8767/healthz; then
    echo "Moonshot Chat proxy: READY → api.moonshot.ai/v1/chat/completions"
else
    echo "Moonshot Chat proxy: NOT READY"
fi

codex_workers="$(pgrep -fc '/vendor/.*/codex/codex exec' || true)"
echo "Active K3 Codex workers: $codex_workers / 28"

echo
echo "Current Archon stage:"
if [[ -f "$RUN_ROOT/.archon/PROGRESS.md" ]]; then
    sed -n '/^## Current Stage$/,/^## /p' "$RUN_ROOT/.archon/PROGRESS.md" | sed '$d'
else
    echo "(no PROGRESS.md)"
fi

echo
echo "Recent Archon log:"
if [[ -f "$LOG_FILE" ]]; then
    tail -n 40 "$LOG_FILE"
else
    echo "(no log yet)"
fi
