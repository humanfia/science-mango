# Formalization integration validation — 2026-09-14

## Checks run

- Combined research/formalization regression run: **103 tests and 77 subtests
  passed** in 180.98 seconds, including actual Lean acceptance/rejection tests.
- Two subsequently added boundary regressions passed separately: Humanize detects
  the configuration schema, and compiler timeout is not a mathematical rejection.
  The current combined suite therefore contains **105 tests and 77 subtests**.
- `hmz check --strict pipelines/quantum_formalize pipelines/quantum_humanize`:
  both flows passed, with no errors or warnings.
- All remaining verbatim research-adapter files match SOURCE_MANIFEST.json;
  the CLI adaptation is recorded separately there.

## Actual external services and compiler

Live LeanExplore v2 requests for `addition commutativity` confirmed both package
filters: Mathlib returned five hits and Physlib returned three. The legacy
PhysLean filter returned HTTP 500 in an earlier probe; it is not used by the
implemented mapping. Authentication was not required for the working endpoint.

A genuine Humanize/Codex run using **gpt-6-astra / medium** searched both libraries,
generated a proof, encountered a Lean syntax error, received that diagnostic, and
repaired the proof on its second attempt. The immutable target was
`∀ a b : Nat, a + b = b + a`. Lean **4.34.0-rc1** compiled the repaired proof;
the separate exact-target check passed and the theorem had **no axiom dependencies**.

The [portable receipt](examples/live_smoke/receipt.json) records each attempt,
the query and hits from each library, the actual drafts, and the failure feedback.
The final [target](examples/live_smoke/FrozenTarget.lean),
[proof](examples/live_smoke/Candidate.lean), and
[acceptance module](examples/live_smoke/Acceptance.lean) are included. This live
receipt predates the final change to unique per-attempt module filenames; those
filenames were subsequently tested with the real compiler regression suite.

Real Lean negative tests verified rejection of:

- a term of the wrong type;
- a proof using a custom axiom;
- a proof indirectly using a helper proved with `sorry`.

Unit tests additionally cover missing library responses, ignored package filters,
source drift, missing/ambiguous axiom output, metaprogramming/command escapes,
round exhaustion, structured-output schema compatibility and repair feedback.

The first live launch exposed a config-parameter ordering mismatch with the
pinned Humanize loader; the next exposed a required-field mismatch in the native
structured-output schema. Both were corrected and regression-tested before the
successful two-attempt run. They were integration failures, not proof gaps.

## Scope of this evidence

This validates the connected formalization workflow. It **does not claim that the
M5 theorem is already formalized**, or that a natural-language theorem was
translated correctly merely because a Lean declaration passed. A real target's
specification must preserve that theorem's intended statement and assumptions.
The example demonstrates the full machinery with an elementary library theorem.
