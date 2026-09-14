# Quantum research harness

This is the current harness used for the quantum-code M5 research and independent
proof audits. Its research control modules and existing tests are imported unchanged; the CLI now also dispatches the formalize mode.
[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) records their exact source hashes.
[README.research.md](README.research.md) preserves the original research-run notes.

It provides bounded solver/reviewer/integrator scheduling, frozen input hashes,
separate proof-repair and unfinished-audit queues, same-reviewer continuation,
semantic task dispatch, and independent review of integrated proofs. An unfinished
review is not a mathematical rejection. Automatic research-review status does not
certify a mathematical theorem. The new [formalize entry point](../quantum_formalize/README.md)
connects dual-library LeanExplore retrieval to proof generation, compiler repair,
and a mandatory Lean type/axiom gate. The existing science-mango application
remains available as a separate workflow.

## Install and check

Run from this repository root. The pinned humanize2 runtime requires Python 3.12
or newer; use a separate environment from the existing application.

```bash
python3.12 -m venv .venv-quantum-harness
.venv-quantum-harness/bin/python -m pip install -r pipelines/quantum_humanize/requirements.txt
.venv-quantum-harness/bin/python -m pip install 'pytest>=9' pytest-subtests
.venv-quantum-harness/bin/python -m pipelines.quantum_humanize doctor
.venv-quantum-harness/bin/python -m pytest -q pipelines/quantum_humanize
```

The runtime is pinned to humanfia/humanize2 commit
`48d1559805cbdb083958bf381a2ff57c183f96ab`. Doctor verifies this provenance.
The control tests use fake agents and do not start model calls.

## Select the research checkout explicitly

The harness code lives here; mathematical manuscripts, evidence, the baseline
checker, and run outputs live in the research checkout. The commands below assume
a validated research checkout at `../quantum-research`:

```bash
.venv-quantum-harness/bin/python -m pip install -r ../quantum-research/requirements-study.txt
.venv-quantum-harness/bin/python scripts/run_quantum_harness.py \
  --repo ../quantum-research --obligation birth_lift --prepare
```

Preparation freezes the full explicit docs/scripts/tests/evidence/data input set
and runs the research checkout's baseline checker. If the checkout uses Git LFS,
hydrate the baseline data required by that checkout before preparation. Do not
remove failing checks merely to start model turns.

A fresh public clone is not automatically a validated baseline. During this import,
research publication commit `753c672d28da4c550078fcb81b93122530ebf4df` was rejected
because its published README differs from the historical `MANIFEST.json` entry.
The original research workspace passes preparation. Use a checkout whose archive
manifest matches its files, or explicitly review and maintain that research
project's baseline before launching. This import retains the guard unchanged.

Without either `--prepare` or `--live`, the same wrapper prints a launch command
without starting models. A live run additionally needs an authenticated `codex`
CLI on PATH:

```bash
.venv-quantum-harness/bin/python scripts/run_quantum_harness.py \
  --repo ../quantum-research --obligation birth_lift --live
```

The wrapper retains the research defaults: `gpt-6-astra`, effort `medium`, four
concurrent calls, twenty rounds, 640 calls, and four audit continuations with
60-minute ordinary-call timeouts. `--model`, `--effort`, and `--rounds` override
their respective defaults. The upstream reported-output soft cap is not a total
input/reasoning token budget. Real turns are started only with `--live`.

The imported obligation prompts preserve their historical research context; they
are not a new verdict that M5 is open. See the research repository's current
completion record before assigning new work. For an exact task and selected
scope guards, use the underlying `python -m pipelines.quantum_humanize launch
--help` interface with explicit `--repo`, `--task`, and `--extra-input` arguments.
That lower-level interface does not automatically include every baseline input.

## Resume an unchanged proof audit

Prepare an audit-input JSON under the research checkout's
`.humanize-quantum-runs/` directory. It contains candidates and their dependency
hashes, not imported review votes. Paths passed below are relative to that research
checkout:

```bash
.venv-quantum-harness/bin/python scripts/run_quantum_harness.py \
  --repo ../quantum-research --obligation birth_lift \
  --audit-input .humanize-quantum-runs/controller/audit-seed.json \
  --audit-only --rounds 1 --live
```

Outputs and frozen snapshots are written beneath the selected research checkout's
`.humanize-quantum-runs/`. No credentials, environments, or session transcripts are
part of this harness import. The full M5 mathematical proof remains in the
[research repository](https://github.com/ShuxiangCao/quantum_code_discovery_proof/blob/main/research_checkpoints/period_residue_arithmetic_law_reviewed/PROOF.md).
