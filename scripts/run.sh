#!/usr/bin/env bash
set -euo pipefail

PROJECT="${1:-/home/ma-user/Python_project/ArchonHiphoProblemSetSmoke_20260701-224644}"
ARCHON_ROOT="${ARCHON_ROOT:-/home/ma-user/Python_project/Archon}"

export PATH="/home/ma-user/.elan/bin:/home/ma-user/.local/node-v22.15.1-linux-x64/bin:/home/ma-user/.local/archon-npm/bin:${PATH}"

cd "$ARCHON_ROOT"
exec .venv/bin/archon loop "$PROJECT" --from prover --max-iterations "${ARCHON_MAX_ITERATIONS:-1}" --max-parallel "${ARCHON_MAX_PARALLEL:-4}" --max-objectives "${ARCHON_MAX_OBJECTIVES:-10}" --no-dashboard
