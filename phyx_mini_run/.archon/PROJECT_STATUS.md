# Project Status

## Knowledge Base

### Proof and modeling patterns

- For acute-angle Snell/tangent geometry, clear tangent denominators only after proving sine/cosine signs; strict sine and cosine comparisons can then be contradicted with `Real.sin_sq_add_cos_sq` (`0005`).
- When two thermodynamic paths share endpoints, apply the first law on both paths and eliminate the common internal-energy change by linear arithmetic (`0340`).
- Calibrated piecewise-linear pressure-volume work reduces cleanly by rewriting each segment into `straightSegmentWork`, substituting graph coordinates, and normalizing rational unit conversions (`0402`).
- For three-dimensional Euclidean vectors, combine `InnerProductGeometry.cos_angle_mul_norm_mul_norm`, `EuclideanSpace.real_norm_sq_eq`, plane/orientation hypotheses, and coordinate extensionality with `cross_apply` (`0792`).
- A custom time subtype may need a local `IsDirectedOrder` instance before `atTop` has the `NeBot` structure required for limit uniqueness; construct a max upper bound and expose subtype comparisons with `change` (`0882`).
- Toroidal-inductance derivations can chain Ampere, flux, linkage, and inductance laws once the denominator `2 * Real.pi * meanRadius` is proved nonzero explicitly using `Real.pi_ne_zero` and radius positivity (`0922`).
- Keep source/figure readouts, domain/branch conditions, governing laws, previous-part results, and the current conclusion in distinct predicates. A reusable `Satisfies...` law may not contain the target-specialized answer.
- Derive exact or bounded physical quantities before choosing a rounded multiple-choice answer; represent rounding with a tolerance or nearest-choice relation, not a false exact decimal equality.
- Local approximations require a local contract. Patterns already accepted in this corpus include `HasDerivAt` (`0267`), explicit neighborhoods (`0268`, `0269`), a limit (`0546`), a claim connected to `deriv` (`0658`), and `IsLittleO` (`0997`).
- Preserve dimensional primitives with Physlib/PhysLean types where available. Calibration and table data must be named and traceable to a source, not tuned to force the requested result.
- Genuine post-formalization reports use multiple filename and heading variants. Identify them by target ID and content: actual-used LeanExplore queries/candidates, grounded names, local abstractions, and gaps. Automated `physics-grounding-*` preflights are supplementary, not lane evidence.
- A direct `lake env lean <file>` sweep is useful for elaboration verification but says nothing about semantic faithfulness and does not close a `sorry`-bodied theorem.
- Endpoint/state-function pattern (`0339`): specialize path data and the state law at both endpoints, prove typed state equality with `Temperature.ext` plus `NNReal.coe_injective`, transport through the state function, then reduce with `sub_self`.
- Scalarize governing laws only at the proof boundary: specialize a dimensionful law in named units, rewrite independent readouts, then use `norm_num` with `linarith`/`nlinarith`. This closed `0404`, `0473`, `0476`, `0494`, `0669`, `0761`, and `0942`.
- Geometric cancellation patterns: identify translated-profile crests at two times before applying kinematics (`0301`); expand a boundary sum and simplify orientation factors (`0846`).
- Dimensionful scalarization pattern: rewrite `CarriesDimension.toDimensionful_apply_apply`, derive exact unit/readout equalities, and only then normalize the governing law. For rounded answers, retain explicit sign/square/trig bounds through `round_eq_iff` or a tolerance (`0030`, `0046`, `0083`, `0085`, `0843`).
- Oscillator/thermodynamic positivity pattern: equations in squares determine only a magnitude; retain positive-frequency/temperature/volume hypotheses before selecting a root or clearing a denominator (`0200`, `0458`).
- Generated standalone problem files are not Lake module targets. Root `lake build` may pass while a direct file has syntax errors, unknown constants, unsolved goals, or a tactic after closure. No textual `sorry` is not proof closure; require `lake env lean <file>` before `\leanok`.
- Acute inverse-trigonometric pattern: derive certified sine bounds, retain the principal physical angle interval, and only then apply sine monotonicity or `arcsin`/`arctan` inversion. This closes multi-interface and threshold optics without assuming rounded answers (`0000`, `0001`, `0007`, `0009`, `0016`, `0017`, `0021`).
- If a needed decimal bound for `π` has no verified Mathlib name, derive the narrow interval locally from `Real.sin_bound` plus a coarse bound such as `Real.pi_le_four`; do not guess lemma names (`0000`, `0013`, `0303`).
- Extremum/least-value physics claims require both a physical boundary witness and a universal comparison against all admissible states (`0009`, `0010`, `0012`, `0015`, `0021`, `0025`).
- Missing material data must stay symbolic. In `0380`, the source supports the volume-weighted density formula but not a numerical choice because granite, sand, and water densities are absent.
- Local first-order Snell pattern: attach derivatives to the actual ray/image functions with `HasDerivAt`, transport them through an exact eventual equality near the optical axis, and use derivative uniqueness only afterward (`0040`, `0041`, `0055`).
- Multi-stage signed-optics pattern: derive each stage distance and magnification independently, then compose signs and propagate image heights (`0031`, `0032`, `0043`).
- Source facts to preserve from iter-012: `0043` has overall magnification `+2` and final signed height `+16 cm`; recorded B = `-1` is only the second-lens stage. In `0049`, the parallel-sheet source text gives outgoing direction `60°`, answer B; the auxiliary mirror-room image is unrelated.

### Known blockers — do not retry unchanged

- Iter-006 resolved the invalid third-review wave: 180/217 statements passed and 37 remain prover-blocked. Combined with the prior gate, 963 targets have passed verdicts once the orchestrator consumes session 6; never treat the remaining 37 as implicit passes.
- Thirty-five targets lack a genuine current post-formalization report: 0078, 0135, 0165, 0195, 0197, 0206, 0325, 0330, 0331, 0384, 0388, 0418, 0435, 0441, 0455, 0462, 0463, 0465, 0466, 0467, 0472, 0478, 0483, 0488, 0498, 0513, 0514, 0547, 0596, 0611, 0627, 0663, 0776, 0786, 0790. Generic preflights do not satisfy the grounding gate.
- `0117` and `0629` have stale reports: their current statements truthfully replace unsupported numeric answers with symbolic law consequences, but the reports still describe the old choice-A conclusions. Refresh evidence before proof dispatch.
- Live doctor blockers remain `missing-mathlib-import` on `0206` and `0472`; both also lack current reports.
- Approximation repairs now accepted in the reviewed set: `0078` uses `Tendsto`, `0137` uses axis-local `HasDerivAt`, `0227` states the small-amplitude limit quantity, `0478` is symbolic, and `0596` has an explicit remainder bound. The last three missing-report targets remain blocked on evidence, not on the repaired statement alone.
- Missing-data claims require source-honest symbolic conclusions and current evidence. Do not restore numeric answers in `0117`, `0478`, `0629`, `0939`, or the undefined-`sigma` threshold in `0954`.
- Specific facts to preserve: 0016 is B/about 27.5 degrees; 0104 uses `E2/E1` and gives about 0.44818; 0346 gives A/about 28 C; 0983 has exactly one factor of `b`; 0990 supports only a symbolic inductance result. Do not restore the recorded contradictory targets.
- Iter-004 closed ten targets (`0301`, `0339`, `0404`, `0473`, `0476`, `0494`, `0669`, `0761`, `0846`, `0942`): 2,229 → 2,219 `sorry` occurrences and 1,000 → 990 sorry-bearing files.
- Iter-005 closed six targets (`0341`, `0572`, `0795`, `0830`, `0946`, `0988`): 2,219 → 2,213 `sorry` occurrences and 990 → 984 sorry-bearing files.
- Iter-007 closes six additional target proofs (`0005`, `0340`, `0402`, `0792`, `0882`, `0922`), reducing sorries from 2,213 to 2,207 and sorry-bearing files from 984 to 978. All six compile directly and pass manual anti-fake, physical-hypothesis, and answer-as-assumption review.
- Iter-008 certified 26 of 32 assigned proofs. At that review, six files (`0061`, `0303`, `0333`, `0346`, `0380`, `0458`) contained no `sorry` but failed direct elaboration and remained open. Textual counts nevertheless fell from 2,207 to 2,175 sorries and 978 to 946 sorry-bearing files.
- Iter-011 resolves all six iter-008 elaboration failures and certifies 26 new files. The bounded direct preflight passes 32/32 with zero sorries; 40 new placeholders are removed, giving 2,135 textual sorries and 920 sorry-bearing files. All 32 pass manual grounding, anti-fake, governing-law, parameter, approximation, and answer-as-assumption review.
- Iter-011 repair details: rewrite coordinates before angle conversion (`0061`); use local certified pi bounds (`0303`); separate force balance, ideal-gas transport, and volume cancellation (`0333`); avoid tactics after closure (`0346`); remove progress-demanding redundant simplification (`0380`); and expose positive mass/nonzero cancellation before equilibrium-energy normalization (`0458`).
- Fresh iter-008 graph checks report 0 unknown `\uses`/coverage gaps but 106 unmatched Lean helper declarations across 28 chapters; do not repeat the earlier 0-unmatched claim. The 29 isolated declarations remain separate known debt.
- Iter-007 root `lake build` passes. The doctor reports no orphan chapters, broken references, or physics-grounding findings, but `0206` and `0472` remain live `missing-mathlib-import` physics-modeling blockers.
- Iter-007 `sync_leanok` was current but added 0 and removed 20 valid markers because standalone generated files are not registered Lake module targets. After direct Lean checks and escape-hatch scans, review restored those 20 markers and added 12 for the six current targets.
- Iter-008 `sync_leanok` repeated the false negative, removing 32 valid prior markers and adding 0. That review restored those 32 and added 52 statement/proof markers for the 26 directly certified targets; the six then-broken targets were left unmarked.
- Iter-011 `sync_leanok` is current in `current-objectives` scope for all 32 reviewed targets and records 0 additions and 0 removals.
- Iter-012 certifies all 32 assigned new targets (`0028`, `0029`, `0031`–`0034`, `0036`–`0045`, `0047`–`0059`, `0062`–`0064`) and closes 75 placeholders. Reviewed totals move from 2,135 to 2,060 textual sorries and from 920 to 888 sorry-bearing files.
- Iter-012 `sync_leanok` is current in `current-objectives` scope for exactly the 32 reviewed targets and records 0 additions and 0 removals.
- Run-local `.archon/AGENTS.md` and `.archon/prompts/review.md` remain missing and should be restored from the canonical identical-SHA copies.

## Last Updated

2026-07-23T10:26:39Z
