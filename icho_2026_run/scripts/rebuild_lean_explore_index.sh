#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="$(cd "$RUN_ROOT/.." && pwd)"
PYTHON_BIN="$REPO_ROOT/.venv/bin/python"

if [[ ! -x "$PYTHON_BIN" ]]; then
    echo "Archon virtualenv not found at $PYTHON_BIN" >&2
    exit 1
fi

if [[ ! -d "$RUN_ROOT/.lake/packages/crnt-lean/CRNT" ]]; then
    echo "crnt-lean sources are missing; run 'lake update crnt-lean' first." >&2
    exit 1
fi

mkdir -p "$RUN_ROOT/.archon/lean-explore"

env PYTHONPATH="$REPO_ROOT/src${PYTHONPATH:+:$PYTHONPATH}" \
    "$PYTHON_BIN" -m archon.commands.tooling.project_lean_index \
    "$RUN_ROOT" \
    --source-root IChO2026Chem \
    --source-root .lake/packages/crnt-lean/CRNT \
    --package Chemistry \
    --output .archon/lean-explore/project-index.json
