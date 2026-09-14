# LeanExplore → proof → compiler repair → acceptance

This flow connects the quantum research harness to a real Lean proof loop. It
searches **Mathlib and Physlib separately on every attempt**, requests a structured
proof from the existing pinned Humanize/Codex backend, compiles it, feeds compiler
diagnostics back into the next attempt, and accepts only the frozen target after
an independent compiled-import type and axiom check.

The online LeanExplore v2 service currently confirms package filters `Mathlib`
and `Physlib`. Older documentation calls the physics package `PhysLean`; live
checks found that legacy filter returns HTTP 500. The adapter uses the confirmed
`Physlib` name, checks `packages_applied`, and preserves one receipt per query and
library. A failed request is not converted to an empty search or a missing lemma.
The public API needs no key. No account settings or MCP credentials are modified.

## Requirements

Use the pinned Python/hmz environment described in
[the research harness README](../quantum_humanize/README.md). This retrieval adapter
uses the public LeanExplore API and the Python standard library; it does not
require local embedding models or an API SDK install. A live proof call needs the
same authenticated Codex CLI as the existing harness.

Provide a Lake project with `lean-toolchain` and `lakefile.toml` or `lakefile.lean`.
Resolve and build the intended Mathlib/Physlib dependency versions in that project.
Physlib is a **Lean project dependency**, while LeanExplore is a **search service**;
a search hit alone does not install or validate an import. Search-index source
revisions can differ from your installed revision. The local compiler checks
actual compatibility. The flow builds the specified imports before proof attempts.

## Freeze a target

Create a JSON specification, for example:

```json
{
  "name": "QuantumHarnessExample.nat_add_comm",
  "statement": "∀ a b : Nat, a + b = b + a",
  "imports": ["Mathlib.Data.Nat.Basic"],
  "context": "",
  "queries": ["addition commutativity"],
  "guidance": "Prove exactly this declaration."
}
```

`statement` is a closed Lean proposition. `context` can contain the project's
trusted supporting declarations; keep namespaces/sections balanced and use fully
qualified names in the statement. It is never model-editable. `imports` is the
fixed module list; choose the Physlib modules you need when a theorem uses physics
objects. Neither imports nor assumptions can be added by the proof worker.

This spec is the acceptance contract, not an automatic translation certificate:
check that it faithfully expresses the intended mathematical theorem. The flow
does not silently equate one accepted elementary lemma with formalizing all M5.
The supplied natural-number example is an infrastructure smoke test only.

## Run

From the science-mango repository root:

```bash
# Validate the spec and describe a run. No network or model calls.
.venv-quantum-harness/bin/python -m pipelines.quantum_humanize formalize \
  --project /path/to/lean-project \
  --spec pipelines/quantum_formalize/examples/nat_add_comm.json

# Query both libraries, without starting a proof worker.
.venv-quantum-harness/bin/python -m pipelines.quantum_humanize formalize \
  --project /path/to/lean-project \
  --spec pipelines/quantum_formalize/examples/nat_add_comm.json --search-only

# Run retrieval, proof generation, compiler repair and acceptance.
.venv-quantum-harness/bin/python -m pipelines.quantum_humanize formalize \
  --project /path/to/lean-project \
  --spec pipelines/quantum_formalize/examples/nat_add_comm.json \
  --rounds 5 --compile-timeout 180 --turn-timeout 600 --live
```

Defaults preserve `gpt-6-astra / medium`; explicit `--model` and `--effort` override
them. A round has one model call and queries both libraries for up to three search
queries. Timeouts and the round cap are enforced. Search/build failure and round
exhaustion return nonzero from the CLI, rather than successful proof status.

## What acceptance checks

1. The operator's spec and local Lean sources/configuration are hashed. Local
   source changes during proof attempts stop the run.
2. A controller-written `FrozenTarget` module fixes the target proposition.
   The worker returns only a proof body, not a replacement declaration/file.
3. Lean compiles a fresh candidate `.olean`; syntax/type errors go back to the
   worker. The flow never edits the original project proof files.
4. A separate module imports the compiled candidate, checks it against the frozen
   target, and runs `#print axioms` on that exact declaration.
5. Only the standard foundations `propext`, `Classical.choice`, and `Quot.sound`
   are allowed. `sorryAx`, custom axioms and missing/ambiguous audit output reject
   acceptance. Direct unfinished proofs and metaprogramming escapes are refused.

The existing Archon informational axiom sweep is not used as a success flag;
this flow has its own mandatory acceptance gate. It does not change the theorem's
strength or require unrelated inherited/anchored results.

Artifacts live in the Lean project's `.humanize-formal-runs/`: frozen spec and
environment hashes, retrieval receipts, prompts and drafts, source/olean files,
compiler output, per-attempt verdicts and a final `result.json`. Accepted status
applies only to the named fixed declaration. Keep the generated target module
alongside the proof module when reproducing an accepted artifact.

## Tests

```bash
.venv-quantum-harness/bin/python -m pytest -q pipelines/quantum_formalize
QUANTUM_LEAN_TEST_TOOLCHAIN=leanprover/lean4:v4.34.0-rc1 \
  .venv-quantum-harness/bin/python -m pytest -q pipelines/quantum_formalize
.venv-quantum-harness/bin/hmz check --strict pipelines/quantum_formalize
```

The second command additionally runs actual Lean acceptance and rejection tests
using an installed toolchain. Normal unit tests do not contact models or search
servers. Online retrieval and live end-to-end validation are recorded separately.

Upstream interfaces: [LeanExplore API](https://github.com/justincasher/lean-explore/blob/main/docs/api-client.md),
[Physlib](https://github.com/leanprover-community/physlib).
