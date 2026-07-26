# Iteration 004 review summary

## Outcome

- Stage: `prover`; 10 targets attempted, 10 proof-closed.
- Source sorries: **2,229 → 2,219**; sorry-bearing files: **1,000 → 990**.
- Reviewer reran all 10 files with `lake env lean`; all exit 0. `lake build` also exits 0. Only frozen-unused-hypothesis lints remain in `0669`, `0761`, and `0846`.
- Project-wide physics verdict remains **BLOCKED**, not COMPLETE/review-passing: doctor reports two live modeling blockers (`0206`, `0472`).
- Repository has no `HEAD^`; project files are untracked, so no parent diff exists.

## Attempt evidence

- Primary ledger: 123 JSONL lines (summary + 122 events): 22 edits, 100 shell calls, zero goal/diagnostic events. Preprocessing erased all Edit payloads (`file`, `old_text`, `new_text` empty) and misclassified shell checks as zero builds. Final source, shell results, and `provers-combined.jsonl` supply the missing code/error evidence.
- `0301`: evaluated the translated profile at `(3,0)` and `(8,1)` with `rw [translationLaw.translatedProfile, readouts.initialProfileFromRaster]`; `scaleHeightOnlyAtCrest` identified both crest positions; `constantSpeedMotion 1`, direction simplification, and `linarith` gave `v=5`. First source edit compiled.
- `0339`: specialized isothermal/caloric fields at `0,1`; `Temperature.ext` + `NNReal.coe_injective` converted equal Celsius readouts to typed temperature equality; transported through `internalEnergyAtTemperature`; `sub_self` closed the endpoint difference. First source edit compiled.
- `0404`: specialized the boundary-work law, derived `p=200000 Pa` and endpoints `3V₁,V₁`, rewrote the `80 J` readout, then `nlinarith` proved `200 cm³`; `simpa` selected C. First source edit compiled.
- `0473`: composed the figure and heat-input readouts, rewrote `Q_H=mH` with `10000` and `5·10^4`, then `norm_num; linarith` proved `0.20 g`. First source edit compiled.
- `0476`: first proof transferred pressure correctly, but its compact choice-case closer failed at line 383 with `error: No goals to be solved` three times. Replacing it with explicit `A/B/C/D` cases compiled; C closes by `rfl`, other cases by `norm_num`.
- `0494`: first proof failed before elaboration at line 323 with `error: expected '*' or checkColGt`; the logged code split `simp only [...] at` from its two hypotheses. Moving `hCurvedFirstLaw hDtoAFirstLaw` onto the same tactic line compiled. The proof uses two first-law instances, isochoric zero work, and `linarith`.
- `0669`: destructured calibrated endpoint times/positions, rewrote the average-velocity law to `(0-0)/(8-0)`, normalized to zero, then unfolded recorded choice C. First edit compiled; only `h_problem` is unused.
- `0761`: specialized the lower-four-link Newton law in SI units, rewrote four `0.100 kg` masses, `a=2.50`, `g=9.80`, normalized decimals, and used `linarith` for `4.92 N`. First edit compiled; only `figureData` is unused.
- `0846`: expanded net flux and each of the three surface contributions, then `simp [axialFluxOrientationFactor]` canceled `-EA+0+EA`. First edit compiled; figure/geometry/field binders are unused because the governing-law premise packages their consequences.
- `0942`: derived `C=5/10^6 F` and `ω=2500`, rewrote `X_C=1/(ωC)`, and closed `80 Ω` with `norm_num`. First edit compiled.

## Physics and grounding gate

- No touched target hides its conclusion in a premise, replaces the claim with `True`/reflexivity, uses a global approximation, disconnects a field/operator claim, or introduces `axiom`, `admit`, `native_decide`, or `sorryAx`.
- Each declaration has a genuine post-formalization report in `logs/iter-002/task_results-archive/` or `logs/iter-003/task_results-archive/` recording actual LeanExplore queries/candidates, adopted Mathlib/Physlib names, local abstractions, and gaps. Current `physics-grounding-*` preflights are automated inventories and were treated as supplementary only.
- No dedicated `physics-reviewer` report exists because subagents are disabled; the required checklist was applied directly.

## Blueprint doctor blockers

Structural results: 0 orphan chapters, broken/malformed refs, axioms, coverage problems, or grounding problems. Live `physics_modeling_problems`:

> `0206` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0472` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

## Blueprint markers updated (manual)

- `0301`, `0339`, `0404`, `0473`, `0476`, `0494`, `0669`, `0761`, `0846`, `0942`: added statement and proof `\leanok` to each target chapter.
- Override justification: current sync is iter-004 but added 0 markers because the standalone generated files are not named Lake modules. Direct path compilation succeeds, each linked declaration is `sorry`-free, and the project build passes.
- No `\mathlibok`, `\lean{...}` correction, `% NOTE:`, or `\notready` change was needed.

## Graph and next step

- Venv CLI: `gaps=0`, `unmatched=0`, frontier `2,262`; no 1-to-1 coverage debt remains.
- Next proof shortlist with one sorry and substantive blueprint proofs: `0007`, `0008`, `0017`, `0016`. Keep the 217 `review_exhausted` files out of ordinary prover dispatch.

