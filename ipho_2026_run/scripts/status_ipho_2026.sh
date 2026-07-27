#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUNTIME_DIR="$RUN_ROOT/.archon/runtime"

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

show_process "LeanExplore" "$RUNTIME_DIR/lean_explore_8765.pid"
show_process "Archon" "$RUNTIME_DIR/ipho_2026_archon.pid"

if curl --silent --output /dev/null --max-time 1 \
    http://127.0.0.1:8765/mcp; then
    echo "LeanExplore endpoint: READY"
else
    echo "LeanExplore endpoint: NOT READY"
fi

echo
echo "Current Archon stage:"
sed -n '/^## Current Stage$/,/^## /p' "$RUN_ROOT/.archon/PROGRESS.md" | sed '$d'

echo
echo "Recent Archon log:"
if [[ -f "$RUNTIME_DIR/ipho_2026_archon.log" ]]; then
    tail -n 30 "$RUNTIME_DIR/ipho_2026_archon.log"
else
    echo "(no log yet)"
fi
