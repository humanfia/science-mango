# Session 8 Review

- Iteration/stage: iter-008, prover.
- Assigned targets: 32.
- Certified: 26. Broken proof bodies: 6 (`0061`, `0303`, `0333`, `0346`, `0380`, `0458`).
- Textual `sorry` count: 2,207 → 2,175; sorry-bearing files: 978 → 946. These counts include the six broken files whose `sorry` was removed without producing an elaborating theorem, so they are not proof-closure counts.
- Ledger: 756 events, 88 edits, and 0 normalized goal/diagnostic/build events. The 88 `code_change` payloads are blank; attempts in `milestones.jsonl` were reconstructed from surrounding raw events, prover logs/reports, final source, and fresh direct checks.

## Target outcomes

| Target | Verdict | Significant proof route or failure |
|---|---|---|
| `0014` | certified | Trig bounds locate the odd reflection heights; `Finset.ext`, `omega`, and `nlinarith` give six. A direct `congrArg Real.tan` attempt had a type mismatch. |
| `0030` | certified | Normalize centimeter/meter coercions, solve three Gaussian imaging equations and magnifications, then compose. |
| `0035` | certified | Signed lensmaker equation with `f=5`, `R₁=9`, `R₂=-11` gives `199/100` by `norm_num`/`linarith`. |
| `0046` | certified | SI scaling plus the diffraction relation and explicit trig bounds close `round_eq_iff` at 633 nm. |
| `0060` | certified | Figure angle readouts and the reflection law reduce to linear arithmetic, choice A. |
| `0061` | **broken** | Geometry reaches `y=9`, but `change` is not definitionally equal to the Euclidean angle target and the final goal remains `9 - 0 = 9`. |
| `0083` | certified | Single-slit/graph-slope equations, explicit sqrt/trig bounds, and rounding establish choice C. |
| `0085` | certified | Exact segment optical lengths `16/5`, `17/5`, `159/25` sum to the 43.2 ps tolerance, choice C. |
| `0093` | certified | `WithDim.ext` and Malus' law at crossed A/C axes reduce the intensity to zero. |
| `0157` | certified | Triple/boiling/unknown manometer readouts plus constant-volume pressure-temperature proportionality give 348 K. |
| `0171` | certified | Signed Doppler law and source data normalize with `abs_le` to answer A. |
| `0200` | certified | Oscillator square laws yield `4ω_l²=3ω_s²`; positivity selects the 12.5–13.5 Hz choice-D interval. |
| `0303` | **broken** | Uses unavailable constants `Real.pi_gt_d2` and `Real.pi_lt_d4`. |
| `0333` | **broken** | Parser stops at line 316 with `expected '*' or checkColGt`. |
| `0346` | **broken** | Process classification/Mayer derivation closes the goal, then a trailing tactic fails with `No goals to be solved`. The corrected result A/about 28 C is preserved. |
| `0363` | certified | Unfold inverse-pV/ideal-gas laws and normalize the Celsius rounding tolerance. |
| `0367` | certified | The independent previous-part state-two result transports across the isothermal 2→3 law. |
| `0372` | certified | Helium mass gives `1/40` mole; the state-one ideal-gas equation gives the exact symbolic Celsius expression. |
| `0373` | certified | Tripled pressure and volume multiply Kelvin temperature by nine, yielding 2364 C. |
| `0376` | certified | Initial/final ideal-gas laws, amount conservation, fixed temperature, and common pressure give 400000 Pa. |
| `0380` | **broken** | A second simplifier at line 275 fails with `` `simp` made no progress ``. |
| `0408` | certified | Rectangle-leg work and two first-law equations eliminate the common internal-energy change. |
| `0424` | certified | Engine heat/work gives 500 J input to the refrigerator; its ratio and first law give `Q₃=2500`. |
| `0458` | **broken** | Unsolved pressure equality at line 425, failed rewrite at 433, and missing nonzeroness at 465. |
| `0471` | certified | Calibrated path works plus the first law give `ΔU=510` and ACD heat 600, choice B. |
| `0510` | certified | Relativistic velocity addition normalizes to `160/163`, choice D. |
| `0523` | certified | Signed Galilean addition `20 + (-30) = -10`, choice D. |
| `0642` | certified | `10 μA / (1.6×10⁻¹⁹ C)` gives `6.25×10¹³` photoelectrons/s. |
| `0748` | certified | Oriented vector subtraction and unit conversion give `80 i - 60 j`. |
| `0794` | certified | Position laws agree at 10 s; `nlinarith` proves strict ordering on either side, choice B. |
| `0843` | certified | `10 cm = 0.1 m`, plane-angle `sin 30°`, and the flux law give 1, choice D. |
| `0856` | certified | Turning-point `K=0`, dipole potential, and energy conservation give aligned `K=1 μJ`, choice D. |

The full attempt ledger, including code fragments, failures, line numbers, and reusable lemmas, is in `milestones.jsonl`.

## Verification and physics verdict

- Fresh `lake env lean PhyXMiniProblems/problem_phyx_mini_NNNN.lean` checks pass for the 26 certified targets and fail reproducibly for the six listed above. Root `lake build` passes, but these standalone generated files are not registered Lake targets, so the root build does not override the direct failures.
- All 32 assigned files contain no textual `sorry`; the 26 certified files also pass the reviewer escape-hatch scan. No Lean file was edited during review.
- Genuine current or archived post-formalization reports were checked for all 32 targets. They record actual LeanExplore queries/candidates, grounded names, local abstractions, grounding gaps, and source/law/answer splits. Generic `physics-grounding-*` preflights were treated only as supplementary.
- Manual statement anti-fake, governing-law completeness, parameter capture, and answer-as-assumption checks pass all 32 formalized statements. No target is `True`, reflexive algebra, a disconnected scalar claim, or a global exact local approximation. `0367` correctly depends on a separately represented previous-part result.
- No dedicated `physics-reviewer` subagent was enabled; the required checklist was applied manually.
- Project/global verdict is **BLOCKED**, not complete or review-passing. The doctor’s `physics_modeling_problems` contains:
  - `PhyXMiniProblems/problem_phyx_mini_0206.lean` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”.
  - `PhyXMiniProblems/problem_phyx_mini_0472.lean` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”.
- Doctor otherwise reports 0 orphan chapters, broken/malformed references, axioms, and physics-grounding problems.

## Graph and markers

- Fresh `leandag build`: 31,570 blueprint nodes, 63,585 edges, 2,175 sorry-bearing declarations, 29 isolated declarations, 0 unknown `\uses`/coverage gaps, and **106 unmatched Lean declarations**.
- The 106 unmatched helpers occur in 28 chapters: `0075` (9), `0135` (2), `0150` (7), `0158` (3), `0195` (2), `0206` (5), `0308` (7), `0331` (1), `0388` (4), `0435` (3), `0439` (5), `0462` (2), `0463` (5), `0465` (5), `0466` (2), `0467` (1), `0472` (8), `0478` (4), `0483` (2), `0488` (2), `0498` (6), `0513` (3), `0514` (2), `0611` (1), `0663` (1), `0786` (2), `0790` (7), `0941` (5).
- Added statement/proof `\leanok` only for the 26 directly certified iter-008 targets. The six broken targets remain unmarked.
- Restored 32 valid statement/proof markers for the 16 previously certified chapters removed by current iter-008 sync: `0005`, `0301`, `0339`, `0340`, `0402`, `0404`, `0473`, `0476`, `0494`, `0669`, `0761`, `0792`, `0846`, `0882`, `0922`, `0942`.
- Justification: `sync_leanok-state.json` is current (`iter=8`) but removed all 32 prior markers because the generated standalone files are not Lake module targets. Direct checks and source audits support the manual override. Final graph marker count is 43 proved blueprint declarations, including the scaffold.

## Control note

- Run-local `.archon/AGENTS.md` and `.archon/prompts/review.md` remain absent. This review used canonical archive copies with SHA-256 values identical across the available project copies.
