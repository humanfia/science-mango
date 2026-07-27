#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="/root/proposal_for_physic/science-mango/.venv/bin/python"
RUNTIME_DIR="$RUN_ROOT/.archon/runtime"
PID_FILE="$RUNTIME_DIR/lean_explore_8765.pid"
LOG_FILE="$RUNTIME_DIR/lean_explore_8765.log"

mkdir -p "$RUNTIME_DIR"

if [[ -s "$PID_FILE" ]]; then
    existing_pid="$(<"$PID_FILE")"
    if kill -0 "$existing_pid" 2>/dev/null; then
        echo "LeanExplore is already running (PID $existing_pid)."
        exit 0
    fi
fi

nohup setsid "$PYTHON_BIN" "$RUN_ROOT/scripts/lean_explore_http.py" \
    >>"$LOG_FILE" 2>&1 < /dev/null &
service_pid=$!
printf '%s\n' "$service_pid" > "$PID_FILE"

for _attempt in $(seq 1 60); do
    if ! kill -0 "$service_pid" 2>/dev/null; then
        echo "LeanExplore exited during startup. Recent log:" >&2
        tail -n 60 "$LOG_FILE" >&2 || true
        exit 1
    fi
    if curl --silent --output /dev/null --max-time 1 \
        http://127.0.0.1:8765/mcp; then
        echo "LeanExplore HTTP MCP is ready (PID $service_pid, port 8765)."
        exit 0
    fi
    sleep 1
done

echo "LeanExplore is alive but port 8765 did not become ready in 60 seconds." >&2
tail -n 60 "$LOG_FILE" >&2 || true
exit 1
