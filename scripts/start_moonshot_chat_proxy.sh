#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="/root/proposal_for_physic/science-mango/.venv/bin/python"
RUNTIME_DIR="$RUN_ROOT/.archon/runtime"
PID_FILE="$RUNTIME_DIR/moonshot_chat_proxy.pid"
LOG_FILE="$RUNTIME_DIR/moonshot_chat_proxy.log"
AUDIT_FILE="$RUNTIME_DIR/moonshot_chat_proxy.jsonl"
HEALTH_URL="http://127.0.0.1:8767/healthz"

mkdir -p "$RUNTIME_DIR"

if curl --silent --fail --output /dev/null --max-time 1 "$HEALTH_URL"; then
    echo "Moonshot Chat proxy is ready on 127.0.0.1:8767."
    exit 0
fi

if [[ -s "$PID_FILE" ]]; then
    existing_pid="$(<"$PID_FILE")"
    if kill -0 "$existing_pid" 2>/dev/null; then
        echo "Moonshot Chat proxy process $existing_pid is alive but unhealthy." >&2
        exit 1
    fi
fi

nohup setsid "$PYTHON_BIN" "$RUN_ROOT/scripts/moonshot_chat_proxy.py" \
    --host 127.0.0.1 \
    --port 8767 \
    --upstream-host api.moonshot.ai \
    --upstream-path /v1/chat/completions \
    --audit-log "$AUDIT_FILE" \
    >>"$LOG_FILE" 2>&1 < /dev/null &
proxy_pid=$!
printf '%s\n' "$proxy_pid" > "$PID_FILE"

for _attempt in $(seq 1 30); do
    if ! kill -0 "$proxy_pid" 2>/dev/null; then
        echo "Moonshot Chat proxy exited during startup. Recent log:" >&2
        tail -n 60 "$LOG_FILE" >&2 || true
        exit 1
    fi
    if curl --silent --fail --output /dev/null --max-time 1 "$HEALTH_URL"; then
        echo "Moonshot Chat proxy is ready (PID $proxy_pid, port 8767)."
        exit 0
    fi
    sleep 1
done

echo "Moonshot Chat proxy did not become ready in 30 seconds." >&2
exit 1
