# IPhO 2026 answer-blind experiment handoff

This branch is the cross-machine handoff for the IPhO 2026 answer-blind
formalization experiment. It contains the Kimi and GPT launchers, tests, and a
sanitized Kimi checkpoint. It does **not** contain credentials, Codex login
data, runtime binaries, model caches, or the controller-only grader.

> Important: this repository contains historical official solution and marking
> files under `ipho_2026_source/`. Never run a solver in this Git checkout.
> Always build a fresh problem-only workspace and use the dedicated-UID
> launcher below.

## Handoff status — 2026-09-07 UTC

Branch: `ipho-2026-answer-blind-handoff-20260907`

The last Kimi controller/broker is no longer running. Its durable gate state is:

| Item | State |
| --- | --- |
| Formalization review | 28/28 passed |
| Proof review | 26/28 solved |
| T1-C1, T1-C2 | solved in r25 |
| T1-B2 | retry, 3/4 reviewed attempts; 20 proof placeholders |
| T2-A1 | reopened for migration, 3/4 reviewed attempts; 25 proof placeholders |
| GPT IPhO run | not started |

The 26 solved targets are E1-A1/A5/B4/B6/C6/C7; T1-A1/B1/C1/C2;
T2-B1/B2/B3/C1/C2/C3/C4; and T3-A1/A2/A3/B1/B2/C2/C3/C4/C5.

The portable continuation is in
[`handoff/ipho-2026-kimi-r25`](handoff/ipho-2026-kimi-r25). It contains only
the generated Lean/blueprint and question-source-report overlay, gate state,
minimal lifecycle anchor,
the exact problem-only bundle, and selected B2 scratch files. Large agent logs,
secrets, caches, broker state, and grading material are excluded. T2-A1 was
administratively reopened with its history and consumed attempts preserved;
this does not certify a proof.

The original r25 stopped after three 1800-second no-JSONL watchdog events while
proving T1-B2. It did receive compiler feedback (16 `lake env lean` calls), but
only changed scratch files and never wrote a finished proof to the main target.
Three remaining PPID=1 processes on the old machine were stale workers, not
live progress.

## Pipeline and versions

Controller-only canonical data -> question-only bundle -> fresh history-free
solver seed -> Kimi or GPT harness -> local LeanExplore (Mathlib + Physlib) ->
formalization review -> proof/compiler review.

- Kimi: `anthropic-kimi-k3`, `https://api.unipatai.com/v1/messages`, max 4 workers.
- GPT: `gpt-5.6-sol`, native Codex login, effort `max`, configured at 32
  workers (only 28 objectives exist).
- Lean `v4.31.0`, Mathlib `v4.31.0`, Physlib
  `1706ae68b63996f1d97717e672e50c9e3933d933`.
- Claude and Codex inactivity watchdog: 1800 seconds, up to three harness
  attempts (two restarts).

Kimi must reach 28/28 before GPT starts. GPT must use a separate fresh seed and
must never inherit Kimi Lean files, blueprints, reports, or `.archon` state.

## Machine-local prerequisites

Copy these out of band or rebuild them on the receiving machine:

```text
/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-idle1800
/root/icho-answer-blind-overlay-49360f26-univ-kimi-k3
/root/icho-full32-lake-packages-bf7-prebuilt-49360f26
/root/.lean_explore
/root/lean-explore-hf-qwen3-embedding-0.6b-97b0c614
/root/science-mango/.venv/lib/python3.14/site-packages
```

The Kimi runtime source marker must name
`10b04c62f66af0815bfa0bfa3c5cb3cbd5ef5358`; the provider overlay marker must
name `49360f26a1196d108ec98f66a341b5d04f3c6d2c`.

The GPT launcher pins
`/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-gpt-idle1800`. That runtime
had not yet been built at checkpoint capture. The committed runtime builder
derives it from the exact Kimi runtime, relocates embedded paths, installs only
the reviewed physics/LeanExplore overlay, changes the Codex inactivity default
to 1800 seconds, and validates the sealed result. Editing Git source alone does
not update a sealed runtime.

Create distinct non-root service users:

```bash
id ichokimis1 || useradd --create-home --shell /bin/bash ichokimis1
id ichokimib1 || useradd --create-home --shell /usr/sbin/nologin ichokimib1
```

The old UIDs were 26320 and 26323, but the new UIDs may differ. Provision
secrets outside Git:

```bash
export IPHO_KIMI_CREDENTIAL=/root/.credentials/icho-univ-token
export IPHO_CODEX_TEMPLATE=/root/icho-r8-codex-template
chmod 600 "$IPHO_KIMI_CREDENTIAL" "$IPHO_CODEX_TEMPLATE/auth.json"
chown root:root "$IPHO_KIMI_CREDENTIAL" "$IPHO_CODEX_TEMPLATE/auth.json"
```

Never paste keys into Git, this README, receipts, or command-line arguments.
For GPT, the per-run `auth.json` copy is necessarily readable by the dedicated
solver UID (including tools launched under that UID). Use a dedicated,
revocable Codex login rather than a valuable shared credential, and dispose of
the private run home after the campaign and its child processes have stopped.

## Restore and finish Kimi

Use `/root`, not `/tmp`, for run state; `/tmp` filled up on the old machine.

```bash
git clone --branch ipho-2026-answer-blind-handoff-20260907 \
  git@github.com:humanfia/science-mango.git /root/science-mango-ipho-handoff
export IPHO_REPO=/root/science-mango-ipho-handoff
export IPHO_WORKSPACE=/root/ipho-2026-kimi-continuation
export IPHO_CTRL=/root/ipho-2026-controller-continuation
export IPHO_DEPS=/root/icho-full32-lake-packages-bf7-prebuilt-49360f26
export IPHO_HF_CACHE=/root/lean-explore-hf-qwen3-embedding-0.6b-97b0c614
export IPHO_LE_SITE=/root/science-mango/.venv/lib/python3.14/site-packages
export IPHO_RUNTIME_KIMI=/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-idle1800
```

Build and validate the clean seed. The committed `questions_only.jsonl` must
hash to `bf35dfc9202003e5ade794d8b99611f18c43e09832bc22dea12d335ac703d511`.

```bash
test ! -e "$IPHO_WORKSPACE"
python3 "$IPHO_REPO/scripts/build_ipho_answer_blind_solver_seed.py" \
  --questions-only "$IPHO_REPO/handoff/ipho-2026-kimi-r25/controller-blind/questions_only.jsonl" \
  --blind-manifest "$IPHO_REPO/handoff/ipho-2026-kimi-r25/controller-blind/questions_only.jsonl.manifest.json" \
  --asset-root "$IPHO_REPO/ipho_2026_source" --lake-root "$IPHO_REPO" \
  --output "$IPHO_WORKSPACE"
python3 "$IPHO_REPO/scripts/build_ipho_answer_blind_solver_seed.py" \
  --validate-seed "$IPHO_WORKSPACE"
python3 "$IPHO_REPO/scripts/configure_ipho_answer_blind_workspace.py" \
  "$IPHO_WORKSPACE" --variant kimi-k3 --max-objectives 28 --max-parallel 2
# This also restores the 28 question-only source reports bound by the gate.
cp -a "$IPHO_REPO/handoff/ipho-2026-kimi-r25/workspace-overlay/." "$IPHO_WORKSPACE/"
cp -a "$IPHO_REPO/handoff/ipho-2026-kimi-r25/archon-state/." "$IPHO_WORKSPACE/.archon/"
```

Assert the restored gate before launch:

```bash
python3 - "$IPHO_WORKSPACE/.archon/proof-review-gate.json" <<'PY'
import json, sys
states = {k: v["status"] for k, v in json.load(open(sys.argv[1]))["targets"].items()}
assert list(states.values()).count("solved") == 26, states
assert states["IPhO2026Problems/problem_ipho_2026_t1_b2.lean"] == "retry"
assert states["IPhO2026Problems/problem_ipho_2026_t2_a1.lean"] == "retry"
print("checkpoint OK: 26 solved, 2 retry")
PY
```

Start only B2 and T2-A1. Controller directory must exist as root mode 0700;
private home/tmp must not exist. Always use a fresh run ID and fresh paths.

```bash
export RUN_ID=ipho2026-kimi-blind-continuation-01
export RUN_CTRL="$IPHO_CTRL/campaign-$RUN_ID"
export RUN_HOME="/root/ipho-private-home-$RUN_ID"
export RUN_TMP="/root/ipho-private-tmp-$RUN_ID"
install -d -o root -g root -m 0700 "$IPHO_CTRL" "$RUN_CTRL"
test ! -e "$RUN_HOME" && test ! -e "$RUN_TMP"
python3 "$IPHO_REPO/scripts/run_ipho_answer_blind_campaign.py" \
  --credential-file "$IPHO_KIMI_CREDENTIAL" \
  --controller-dir "$RUN_CTRL" --workspace "$IPHO_WORKSPACE" \
  --dependency-root "$IPHO_DEPS" --private-home "$RUN_HOME" \
  --private-tmp "$RUN_TMP" --run-id "$RUN_ID" \
  --solver-user ichokimis1 --runtime-root "$IPHO_RUNTIME_KIMI" \
  --lean-explore-cache /root/.lean_explore \
  --lean-explore-hf-cache "$IPHO_HF_CACHE" \
  --lean-explore-site-packages "$IPHO_LE_SITE" \
  --max-iterations 4 --max-parallel 2 --max-objectives 2 --timeout-s 172800
```

Run the controller in the foreground inside `tmux`/`screen` and detach. Do not
Ctrl-Z it: the controller owns the broker lease.

## Gate before GPT

Require a successful Kimi receipt, quiescent solver UID, and exactly 28 solved:

```bash
python3 - "$IPHO_WORKSPACE/.archon/proof-review-gate.json" <<'PY'
import collections, json, sys
counts = collections.Counter(v["status"] for v in json.load(open(sys.argv[1]))["targets"].values())
print(dict(counts))
assert counts == {"solved": 28}, counts
PY
ps -u ichokimis1 -o pid,ppid,stat,etime,args
```

## Start the fresh GPT run

Do not apply the Kimi checkpoint overlay here.

```bash
export IPHO_GPT_WORKSPACE=/root/ipho-2026-gpt-fresh
export IPHO_RUNTIME_KIMI=/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-idle1800
export IPHO_RUNTIME_GPT=/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-gpt-idle1800
if test ! -e "$IPHO_RUNTIME_GPT"; then
  python3 "$IPHO_REPO/scripts/build_ipho_answer_blind_gpt_runtime.py"
fi
python3 "$IPHO_REPO/scripts/build_ipho_answer_blind_gpt_runtime.py" --validate-only

test ! -e "$IPHO_GPT_WORKSPACE"
python3 "$IPHO_REPO/scripts/build_ipho_answer_blind_solver_seed.py" \
  --questions-only "$IPHO_REPO/handoff/ipho-2026-kimi-r25/controller-blind/questions_only.jsonl" \
  --blind-manifest "$IPHO_REPO/handoff/ipho-2026-kimi-r25/controller-blind/questions_only.jsonl.manifest.json" \
  --asset-root "$IPHO_REPO/ipho_2026_source" --lake-root "$IPHO_REPO" \
  --output "$IPHO_GPT_WORKSPACE"
python3 "$IPHO_REPO/scripts/build_ipho_answer_blind_solver_seed.py" \
  --validate-seed "$IPHO_GPT_WORKSPACE"
python3 "$IPHO_REPO/scripts/configure_ipho_answer_blind_workspace.py" \
  "$IPHO_GPT_WORKSPACE" --variant gpt --max-objectives 28 --max-parallel 32

# Deterministically ingest the 28 question-only records. This creates source
# reports, blueprint stubs, and PROGRESS objectives; it does not call a model.
"$IPHO_RUNTIME_GPT/bin/archon" physics-formalize "$IPHO_GPT_WORKSPACE" \
  --input-jsonl "$IPHO_GPT_WORKSPACE/ipho_2026_source/questions_only.jsonl" \
  --image-root "$IPHO_GPT_WORKSPACE/ipho_2026_source/image" \
  --out-dir IPhO2026Problems \
  --report-dir reports/ipho_2026 \
  --work-dir "$IPHO_GPT_WORKSPACE/.archon/physics-formalize/full28" \
  --dataset-format native \
  --evaluation-mode answer-blind \
  --update-progress
test "$(find "$IPHO_GPT_WORKSPACE/reports/ipho_2026" -name '*.source.json' | wc -l)" -eq 28
grep -q autoformalize "$IPHO_GPT_WORKSPACE/.archon/PROGRESS.md"

export RUN_ID=ipho2026-gpt56sol-blind-01
export RUN_CTRL="$IPHO_CTRL/campaign-$RUN_ID"
export RUN_HOME="/root/ipho-private-home-$RUN_ID"
export RUN_TMP="/root/ipho-private-tmp-$RUN_ID"
install -d -o root -g root -m 0700 "$RUN_CTRL"
test ! -e "$RUN_HOME" && test ! -e "$RUN_TMP"
python3 "$IPHO_REPO/scripts/run_ipho_answer_blind_gpt_campaign.py" \
  --codex-home-template "$IPHO_CODEX_TEMPLATE" \
  --controller-dir "$RUN_CTRL" --workspace "$IPHO_GPT_WORKSPACE" \
  --dependency-root "$IPHO_DEPS" --private-home "$RUN_HOME" \
  --private-tmp "$RUN_TMP" --run-id "$RUN_ID" \
  --solver-user ichokimis1 --runtime-root "$IPHO_RUNTIME_GPT" \
  --lean-explore-cache /root/.lean_explore \
  --lean-explore-hf-cache "$IPHO_HF_CACHE" \
  --lean-explore-site-packages "$IPHO_LE_SITE" \
  --max-iterations 4 --max-parallel 32 --max-objectives 28 --timeout-s 172800
```

## Tests, monitoring, and pitfalls

```bash
export IPHO_TEST_PYTHON=/path/to/python-with-science-mango-dependencies
cd "$IPHO_REPO"
PYTHONPATH="$IPHO_REPO/src" "$IPHO_TEST_PYTHON" -m unittest \
  tests.test_ipho_answer_blind_bundles \
  tests.test_ipho_answer_blind_solver_seed \
  tests.test_configure_ipho_answer_blind_workspace \
  tests.test_ipho_answer_blind_confined_loop \
  tests.test_ipho_answer_blind_campaign \
  tests.test_ipho_answer_blind_gpt_campaign \
  tests.test_ipho_answer_blind_gpt_runtime \
  tests.test_codex_agent
git diff --check
```

Monitor with `tail -F "$RUN_CTRL/$RUN_ID-ipho-confined-loop.log"` for Kimi,
`tail -F "$RUN_CTRL/$RUN_ID-ipho-gpt-campaign.log"` for GPT, and
`ps -u ichokimis1 -o pid,ppid,stat,etime,args`. Also check `df -h /root /tmp`.

- Runtime and Kimi overlay paths are absolute pins; `--runtime-root` is not a
  relocation bypass.
- Controller dirs must exist; private home/tmp must be entirely absent.
- The 1800-second setting is inactivity, not total campaign timeout.
- Kimi accepts at most 4 workers; only GPT accepts 32.
- Never commit `.archon-physics.env`, `.codex/auth.json`, keys, broker env or
  transcripts, live logs, or grader outputs.

See [`handoff/ipho-2026-kimi-r25/README.md`](handoff/ipho-2026-kimi-r25/README.md)
for checkpoint inventory and integrity checks.
