#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARCHON_VENV="/root/proposal_for_physic/science-mango/.venv"
ARCHON_BIN="$ARCHON_VENV/bin/archon"
CODEX_BIN="/root/proposal_for_physic/tools/codex-0.80/node_modules/.bin/codex"
RUNTIME_DIR="$RUN_ROOT/.archon/runtime"
PID_FILE="$RUNTIME_DIR/ipho_2026_k3_archon.pid"
LOG_FILE="$RUNTIME_DIR/ipho_2026_k3_archon.log"
CONFIG_FILE="$RUN_ROOT/.archon/config.json"
ENV_FILE="$RUN_ROOT/.archon/.env"

mkdir -p "$RUNTIME_DIR"

if [[ -s "$PID_FILE" ]]; then
    existing_pid="$(<"$PID_FILE")"
    if kill -0 "$existing_pid" 2>/dev/null; then
        echo "IPhO 2026 K3 Archon is already running (PID $existing_pid)."
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

[[ -x "$CODEX_BIN" ]]
[[ "$("$CODEX_BIN" --version)" == "codex-cli 0.80.0" ]]
grep -q '^MOONSHOT_API_KEY=sk-' "$ENV_FILE"
grep -q '^MOONSHOT_OPENAI_BASE_URL=http://127.0.0.1:8767/v1$' "$ENV_FILE"

jq -e '
  .loop.harness == "k3-chat"
  and .loop.model == "biui-0724"
  and .loop.max_parallel == 28
  and .loop.max_objectives == 28
  and .harnesses["k3-chat"].runner == "codex"
  and .harnesses["k3-chat"].model == "biui-0724"
  and .harnesses["k3-chat"].wire_api == "chat"
  and .harnesses["k3-chat"].ephemeral == false
' "$CONFIG_FILE" >/dev/null

"$RUN_ROOT/scripts/start_moonshot_chat_proxy.sh"
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

echo "IPhO 2026 K3 Archon started with 28-way concurrency (PID $archon_pid)."
echo "Model: biui-0724"
echo "Wire API: OpenAI Chat Completions"
echo "Local compatibility proxy: http://127.0.0.1:8767/v1"
echo "Upstream: https://api.moonshot.ai/v1/chat/completions"
echo "Log: $LOG_FILE"
