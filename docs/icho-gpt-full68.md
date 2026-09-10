# GPT answer-blind full-theory expansion

Scope: all 68 numbered theory subquestions, 437 raw rubric points. Model:
`gpt-5.6-sol`. Concurrency: 32. This is a new campaign; previous 32-target
proofs, blueprints, reports and sessions must not be reused as solver inputs.
The historical 168/168 score does not describe this expanded campaign.

## Implementation and current status

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
  or `/srv`. The experiment has **not been launched**. Root-only integration
  tests also require the deployment host.

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
