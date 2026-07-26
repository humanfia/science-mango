# Recommendations — iter-005 plan

## 1. Repair global blockers through an authorized audit route

Do not ordinary-prover-dispatch these `review_exhausted` doctor entries:

> `0206` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0472` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

Authorize statement/import repair (or reset their gate status after audit), rerun direct Lake checks and doctor, then review their modeling before proof work.

## 2. Continue proof work only on vetted targets

- Closest supported shortlist: `0007`, `0008`, `0017`, `0016`. Each is gate-passed, has one `sorry`, zero missing dependencies, and a substantive blueprint derivation.
- `0007`: combine reflection, `r=π/2-θ`, Snell, `sin(π/2-θ)=cos θ`, acute-branch injectivity, and the `tan/arctan` characterization.
- `0008`, `0017`, `0016`: expect certified trig bounds/branch reasoning; reuse exact angle identities before numerical interval work. Never conclude from recorded answer metadata.
- Do not assign the other 215 `review_exhausted` omissions until an authorized audit reconstructs their missing final-review verdicts.

## 3. Reuse iter-004 proof patterns

- Endpoint state functions: specialize both endpoints, prove typed state equality (`Temperature.ext`, `NNReal.coe_injective`), transport, subtract.
- Dimensionful algebra: specialize laws in named units, rewrite independent calibrations, then `norm_num` + `linarith`/`nlinarith`.
- Geometry: derive observable geometry first (crest/surface contributions), then apply kinematics or finite additivity.
- For finite choice uniqueness, use explicit constructor cases; the compact `cases ... <;>` closer in `0476` over-applied after goals closed.
- Keep multi-target `simp only ... at h₁ h₂` hypothesis lists on one tactic line; the split form in `0494` is a parser error.

## 4. Infrastructure

- Restore run-local `.archon/AGENTS.md` and `.archon/prompts/{plan,review}.md` from the known canonical copies.
- Fix attempt preprocessing so Edit paths/payloads and shell builds survive; iter-004 lost all code-change payloads and reported zero builds/goals.
- Current graph needs no topology work: `gaps=0`, `unmatched=0`; frontier is 2,262.

