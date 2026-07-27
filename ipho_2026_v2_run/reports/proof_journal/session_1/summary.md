# Session 1 Review Summary

- Iteration/stage: `iter-001` / `autoformalize`
- Scope: exactly 28 listed objectives
- Direct Lean preflight: 28 passed, 0 failed; no checks rerun
- Open target sorries after autoformalization: 85; before-count not reliably present in compact evidence
- Formalization Review: 21 passed, 7 failed
- Attempt log: 1,301 events / 77 edits; no captured goal, diagnostic, or build events. Per-target compile evidence comes from deterministic preflight.
- Grounding logs: all 28 contain query/candidate, grounded-name, local-abstraction, and gap sections
- Dedicated `physics-reviewer`: disabled; checklist applied directly

## Verdicts

| Target | Compile / sorries | Formalization Review | Finding |
| --- | ---: | --- | --- |
| `1_A_1` | pass / 6 | passed | Hydrostatic/torque/critical-contact bridges derive `a=Δh/(2√2)`; 0.005 m is rounding only. |
| `1_B_1` | pass / 1 | passed | Conserved effective energy plus strict outer-turning-point branch fixes `1600a₀/9`. |
| `1_B_2` | pass / 5 | passed | Hyperbolic-conic limit is tied to the actual outgoing trajectory and signed Figure 1b orientation. |
| `1_C_1` | pass / 7 | passed | Conservation/minimization contract is sound and uses the official factor `2` omitted by the generated blueprint. |
| `1_C_2` | pass / 1 | passed | Corrected C.1 quadratic and lower-root selection entail the official excess-energy rounding. |
| `2_A_1` | pass / 4 | failed | Live doctor blocker: missing Physlib/PhysLean import. |
| `2_B_1` | pass / 5 | passed | Global coefficient identity avoids the one-equation/two-unknowns countermodel. |
| `2_B_2` | pass / 3 | passed | Explicit aperture and irradiance balances derive the power ratio. |
| `2_B_3` | pass / 3 | passed | B.1/B.2 equations, positive baseline, and angle branch derive 12 cm. |
| `2_C_1` | pass / 4 | failed | Live doctor blocker: missing Physlib/PhysLean import. |
| `2_C_2` | pass / 1 | failed | Rigorous `IsBigO` statement passes semantic checks, but live missing-import doctor blocker remains. |
| `2_C_3` | pass / 6 | passed | Actual neighboring-ray intersections and a right-hand `Tendsto` carrier ground the caustic. |
| `2_C_4` | pass / 2 | passed | `IsEquivalent` on a punctured neighborhood faithfully expresses the `2/3` small-angle law. |
| `3_A_1` | pass / 1 | passed | Ampère plus `V=(2πR)A` derives `H=NIA/V`. |
| `3_A_2` | pass / 2 | passed | Flux linkage, Faraday polarity, source work, and A.1 derive `dW=VH dB`. |
| `3_A_3` | pass / 4 | passed | Vacuum-core subtraction and differential constitutive laws derive `μ₀VH dM`. |
| `3_B_1` | pass / 4 | passed | Process derivatives and endpoints ground the signed isothermal heat formula. |
| `3_B_2` | pass / 3 | passed | Explicit adiabatic ODE/invariant plus positivity selects the square-root branch. |
| `3_C_2` | pass / 2 | passed | Carnot heat signs and nonnegative magnetization select the stated root. |
| `3_C_3` | pass / 1 | passed | Cycle heat and helium calorimetry determine the numerical cooling bounds. |
| `3_C_4` | pass / 2 | passed | Carnot ratio, power balance, body derivative, and endpoints support the time integral. |
| `3_C_5` | pass / 1 | passed | Total heat/work and the local C.4 result derive overall COP. |
| `4_A_1` | pass / 3 | failed | `officialSampleTarget` lacks Figure 17/readout/error premises; amount/molecule uncertainty is unpropagated and inconsistent. |
| `4_A_5` | pass / 3 | failed | Ideal `1/T₀` is sound; fixed-band membership does not propagate the experimental `±0.0007 K⁻¹`. |
| `4_B_4` | pass / 1 | passed | Two-state Dalton/pressure/geometry/ideal-gas equations derive `Pᵥ`. |
| `4_B_6` | pass / 4 | failed | Conversion and uncertainty propagation are sound; live missing-import doctor blocker remains. |
| `4_C_6` | pass / 3 | failed | Symbolic reciprocal/error bound is sound, but `1.17±0.03 K/W` is a disconnected definition without raw C.5 instantiation. |
| `4_C_7` | pass / 3 | passed | Signed radial Fourier/resistance laws and RSS sensitivities ground `0.25±0.01 W/(m·K)`. |

## Blueprint doctor

- Structural graph: no orphan chapters, broken references, malformed references, or axioms.
- Live physics-modeling blockers:
  - `problem_IPhO_2026_2_A_1.lean`: `missing-physlib-import` — “physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions”.
  - `problem_IPhO_2026_2_C_1.lean`: same blocker.
  - `problem_IPhO_2026_2_C_2.lean`: same blocker.
  - `problem_IPhO_2026_4_B_6.lean`: same blocker.
- `physics_grounding_problems`: empty.

## Source/blueprint corrections

- C.1 blueprint formula omits the factor `2` multiplying `ΔU` under the square root. The Lean C.1/C.2 contracts follow the official conservation law and official C.2 expansion; correct both recorded previous-part texts.
- Many target environments still lack explicit `\lean{...}` links. `sync_leanok-state.json` is current for all 28 objectives and reports 0 additions/removals; no manual marker override was made.

## Blueprint markers updated (manual)

- None.

## Reusable findings

- Local approximations must use `IsBigO`, `IsEquivalent`, derivatives, or limits; C.2–C.4 provide good patterns.
- Experimental `value ± uncertainty` needs input error carriers and a propagation theorem instantiated to the reported output. A fixed estimate definition or fixed-band membership is insufficient.
- Previous-part results can be restated locally as explicit equations under the natural-language-only policy; do not import sibling Lean outputs.
- Signed physics needs conclusion-relevant orientation carriers: outer/inner heat flow, outgoing ray branch, cooling direction, or nonnegative square-root branch.

