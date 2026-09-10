# GPT answer-blind full-theory expansion

Scope: all 68 numbered theory subquestions, 437 raw rubric points. Model:
`gpt-5.6-sol`. Concurrency: 32. This is a new campaign; previous 32-target
proofs, blueprints, reports and sessions must not be reused as solver inputs.
The historical 168/168 score does not describe this expanded campaign.

## Implementation and current status

- At 2026-09-10 16:29 UTC, campaign `gpt56-003` was running with 32 live
  Codex workers and 32 companion code-mode hosts. Fresh post-restart logs
  contain actual shell calls and successful reads of the bound workspace.
  All 68 source/formalizer and semantic-review contracts and the three
  read-only pinned-library origin probes passed startup checks. This is
  startup evidence, not a solved count or an official-answer score.
- The bundle builder supports `--full-theory --expected-count 68`, checks the
  exact canonical theory inventory, and supplies problem-derived output
  contracts for the additional 36 questions. Original 32-target mode is unchanged.
- Structure contracts require explicit connectivity, charge, radicals and
  requested stereochemistry, with derivations from source constraints. They
  do not certify that the new questions have been formalized or solved.
- The GPT controller supports `--target-count 68`, retains a default concurrency
  of 32, and records `full68` execution scope. Bundle hashes, source reports,
  verifier isolation and root ownership checks remain enforced.
- On the preparation host, the user is non-root and `sudo -n true` fails.
  The historical IChO runtimes and prepared seeds were not found in `/opt`
  or `/srv`. The rootless native launcher below supports this host without
  weakening the original controller's root checks. Root-only integration
  tests still require a privileged deployment host.

## Prepare the controller-side bundles

From this repository on the trusted controller host, with a new private
controller directory (never mount that directory into a solver):

```bash
python3 scripts/build_icho_answer_blind_bundles.py \
  --input-jsonl icho_2026_source/processed/icho_2026_theory.jsonl \
  --blind-output /srv/icho-full68-controller/questions_only.jsonl \
  --grader-output /srv/icho-full68-controller/grader_only.jsonl \
  --image-root icho_2026_source/image \
  --problem-pdf icho_2026_source/raw/theory_problem.pdf \
  --solution-pdf icho_2026_source/raw/theory_solution.pdf \
  --full-theory --expected-count 68
```

Use `build_answer_blind_solver_seed.py` to create a fresh seed from the
questions-only bundle, problem PDF/images and allowlisted generic Lake files.
Configure the new workspace with:

```bash
python3 scripts/configure_answer_blind_workspace.py \
  /srv/icho-answer-blind-full68-v1-gpt \
  --variant gpt --max-objectives 68 --max-parallel 32
```

The deployment still needs the sealed runtime rebuilt with the updated
controller via `install_answer_blind_runtime_wrappers.py`, dependencies,
model authentication, four dedicated verifier users/scratch roots, and all
68 problem-only source reports produced by the trusted ingestion pipeline.
The following is the final preflight/launch interface, **not a replacement
for those provisioning steps**:

```bash
/opt/icho-full68-runtime/bin/answer-blind-gpt-campaign \
  --campaign-id gpt56-full68-001 \
  --campaign-root /srv/icho-full68-campaigns/gpt56-full68-001 \
  --seed-workspace /srv/icho-answer-blind-full68-v1-gpt \
  --runtime-root /opt/icho-full68-runtime \
  --dependency-root /opt/icho-full68-runtime/lake/packages \
  --codex-home /root/.codex \
  --target-count 68 --concurrency 32 --preflight
```

Only after preflight succeeds, run the same command without `--preflight`.
Keep the original singleton lock to prevent overlapping old/new campaigns
from sharing verifier lanes. Retrying a failed subset requires a sealed
terminal parent index bound to the same 68-row bundle.

## Verification

```bash
python3 -m unittest tests.test_icho_full68 tests.test_icho_answer_blind_bundle
python3 -m unittest tests.test_answer_blind_gpt_campaign \
  tests.test_answer_blind_structured_solver tests.test_answer_blind_workspace_config
```

The full68 tests use the actual theory dataset, count 437 points, check the
68 contracts and blindness flags, reject the bundle in old 32-target mode,
reject a substituted theory ID, and check GPT model/concurrency defaults.

## Non-root native Archon runner

`scripts/run_answer_blind_rootless_campaign.py` wraps the existing native
`run_answer_blind_archon_campaign.py`, not the root-only structured controller.
It retains the native formalization, formalization review, proof, proof review
and final-build lifecycle, with 68 objectives and 32 parallel lanes. It first
prepares the workspace without models, then mounts inputs read-only and starts
the native loop. Q8.10 is supported by the corrected clean-seed ID validator.

Prerequisites: unprivileged user and mount namespaces, bubblewrap, Codex,
Python with the Archon dependencies, Lean 4.31.0, and the pinned Mathlib,
Physlib and CRNT package caches. On the preparation host these are installed
under `/home/jing`; the existing Python environment is mounted by its exact
directory, without exposing its parent repository.

Example for the prepared host (first invocation creates a runtime snapshot):

```bash
python3 scripts/run_answer_blind_rootless_campaign.py \
  --source /home/jing/icho-gpt-full68 \
  --runtime /home/jing/icho-full68-runtime/native-v5 \
  --seed /home/jing/icho-full68-seed-v2 \
  --packages /home/jing/icho-full68-dependencies/.lake/packages \
  --campaign /home/jing/icho-full68-runs/gpt56-003 \
  --private-home /home/jing/icho-full68-home-003 \
  --python /home/jing/science-mango/.venv/bin/python \
  --lean-bin /home/jing/.elan/toolchains/leanprover--lean4---v4.31.0/bin \
  --codex /home/jing/.local/bin/codex \
  --bwrap /home/jing/icho-full68-runtime/tools/bubblewrap/usr/bin/bwrap \
  --auth-file /home/jing/.codex/auth.json --snapshot --preflight
```

After preflight, use the same paths with `--detach` instead of `--snapshot
--preflight`. Authentication is copied only into the experiment's private home;
never commit it. Reinvoking after an interrupted native run resumes that fresh
campaign. A host-side lock prevents duplicate supervisors for the same campaign.

The host-side status file is `gpt56-003.rootless.json`, the supervisor log is
`gpt56-003.launcher.log`, and the native log is `gpt56-003/run.log`, all under
`/home/jing/icho-full68-runs`. Status `preparing` means no solving loop has
started yet; `running` means the native loop process has started, not that any
question has passed review. Per-target results remain in the native gate files.
The inner native `pipeline` string retains its historical `full32` identifier
for compatibility; scope is determined by the checked `row_count: 68`, exact
68-row manifest, and outer rootless receipt, not that legacy identifier.

The current Codex distribution's sibling `codex-code-mode-host` executable is
also required and mounted read-only. The native configuration enables this
host so model-selected code-mode tool calls can actually execute. A plain-text
login probe is not sufficient: test shell execution and `lean --version` too.

This fresh full68 mode explicitly rederives dependencies from problem inputs,
including Q1.4/Q1.5 results needed by Q1.6. It does not import historical proofs
or root-signed prior-run answers. The inline-prior policy is rejected for any
scope other than the exact canonical 68 rows; historical receipt checks remain
unchanged outside this mode. Free-text structure obligations are carried in
`semantic_requirements`, bound into the semantic DAG and review evidence,
while the existing machine-readable `audit_requirements` enum stays closed.
Q8.4's 35 outputs are checked against its exact source inventory; the generic
32-entry bound remains on auxiliary lists, not the requested-output inventory.
Pinned-library Review accepts non-root-owned dependencies only on kernel
read-only mounts (chmod alone is insufficient), and startup probes verify
actual declaration origins in Mathlib, Physlib and CRNT. Historical root-only
ownership tests require a root host; they are not evidence for this namespace mode.

Preparation attempts `gpt56-001` and `gpt56-002` are retained for diagnostics,
not results. The first stopped before model dispatch; the second was stopped
after detecting unavailable model tools. Their outputs are not inputs to the
fresh `gpt56-003` campaign.

The rootless namespace hides the source checkout, historical results, grader
key, host home and host processes. The engine/dependencies and problem inputs
are read-only. Network access is retained for Codex and hosted LeanExplore;
web search, plugins and apps are disabled in the model harness. This mode does
**not** claim network isolation or the original separate-UID verifier boundary.
Independent official-answer scoring is not part of this launcher and must wait
until the solving processes have stopped and outputs have been frozen.

CLI configuration was checked against the installed CLI, the
[official configuration reference](https://learn.chatgpt.com/docs/config-file/config-reference),
and the [local code-mode host documentation](https://learn.chatgpt.com/docs/app-server).

Run the non-root tests with `bwrap` on PATH:

```bash
python3 -m unittest tests.test_answer_blind_rootless tests.test_icho_full68
```

On 2026-09-10 the related eight-module suite ran 148 tests: 146 passed and
2 genuine-root ownership fixtures were skipped on this non-root host. The
suite covered the rootless launcher, native campaign, full68 bundle, legacy
bundle, problem-only review contract, semantic DAG, certified-prior context,
and native semantic review. Live namespace and model tool probes are separate
from these unit tests.

The full68 problem-only bundle SHA-256 is
`865b4417565ec94097e4287aa7746ee08fb527c80f72b7c15378fa0db9fd8ddc`.
Initial hosted LeanExplore grounding completed for 62 targets; 6 remained
incomplete after transient service/rate-limit responses. The native lifecycle
retains this evidence and permits source-derived local helpers; incomplete
grounding is not recorded as solving or review success.

The namespace integration test checks that an unmounted host sentinel is
invisible and that an attempted write to the read-only seed fails.
