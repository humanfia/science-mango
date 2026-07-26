# Prover result: `problem_phyx_mini_0089.lean`

## Iteration 015 retry

- The iteration-14 proof review classified this target as `partial` only
  because the supplied source image omits the intensity graph needed to
  independently validate the stipulated first-dark-fringe readout `n = 7/5`.
  It identified no Lean elaboration, proof-integrity, or theorem-faithfulness
  defect.
- The assigned file already contains complete proof bodies for all three
  declarations, so no Lean edit was necessary or appropriate in this retry.
  The frozen signatures and all existing proofs were preserved.
- Fresh verification in iteration 015:
  `lake env lean PhyXMiniProblems/problem_phyx_mini_0089.lean` succeeds,
  Lean LSP reports no diagnostics, and a source scan finds no `sorry`,
  `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Fresh `lean_verify` checks for
  `phaseDifference_at_firstDarkFringe`,
  `materialLength_eq_fiveFourths_wavelength`, and
  `problem_phyx_mini_0089` report no source warnings and only the standard
  imported axioms `propext`, `Classical.choice`, and `Quot.sound`.
- Fresh visual inspection of `phyx_data/test_image/89.png` confirms that it
  depicts only the two rays, slab, mirrors, screen, and point `P`; no intensity
  graph or `n = 7/5` readout is present.
- The external evidence gap cannot be repaired within this prover assignment:
  changing `MatchesStatedAndGraphReadouts.firstDarkFringeReadout` or the
  numerical target would change a protected signature. The current
  conditional theorem is sound and needs no Lean redraft; the source owner
  should restore the missing graph and confirm `n = 7/5`.

## Completion status

- All three proof obligations are closed: `phaseDifference_at_firstDarkFringe`,
  `materialLength_eq_fiveFourths_wavelength`, and `problem_phyx_mini_0089`.
- No declaration header, hypothesis, conclusion, governing law, or physical
  abstraction was changed. The file contains no `sorry`, `admit`, new axiom,
  or proof-laundering construct.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0089.lean` succeeds.
  Lean LSP reports no diagnostics.
- `lean_verify` reports only the standard imported axioms `propext`,
  `Classical.choice`, and `Quot.sound` for each of the three proved
  declarations, with no source-scan warnings.

## Proof summary

- At every index `n`, the equal baseline paths, air index one, equal initial
  phases, and equal mirror shifts reduce the path and phase laws to
  `phase(n) * λ = (n - 1) * L`.
- Zero intensity at the stipulated first dark fringe `n = 7/5`, together with
  positive single-ray intensity, gives cosine `-1`. The proof writes the phase
  as an odd half-cycle and uses the strict positivity of every earlier
  displayed intensity to exclude all later odd half-cycles. Hence the phase
  at `7/5` is exactly `1/2`.
- Substitution at `7/5` yields `L = (5/4)λ` in every unit system. Evaluation
  at `n = 2`, followed by cancellation of positive `2π` and wavelength
  factors, gives phase `5/4`. Unfolding only the answer-choice readout then
  proves choice C.

## Assumption/target split

### Governing laws

- `SatisfiesOpticalPathDifferenceLaw`: relative to ambient air, the slab adds `(n - n_air)L` to ray 2's optical path, while retaining the outside-air path difference explicitly.
- `SatisfiesPhaseDifferenceLaw`: the phase difference in wavelength cycles satisfies `(phase cycles) * λ = optical path difference` in every unit system.
- `SatisfiesTwoBeamInterferenceLaw`: equal-intensity coherent rays obey `I = 2 I₀ (1 + cos (2π δ/λ))` at point `P`.
- `HasDepictedCoherentLayout`: the rays are initially in phase, receive equal mirror phase shifts, have equal outside-air path lengths, are reflected by their labelled mirrors, meet at screen point `P`, and only ray 2 crosses the slab.
- `HasPhysicalOpticalParameters`: positivity, equal single-ray intensities, nonnegative combined intensity, and scan-order conditions.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- Air refractive index `1`, tunable range `1 ≤ n ≤ 5/2`, and plotted endpoint `n_s = 3/2`.
- `IsFirstDarkFringeOnDisplayedScan setup (7/5)`, isolated as the graph calibration rather than an optical law.
- The supplied image itself establishes the labelled rays, slab `n` and `L`, separate mirrors, screen, and common point `P`.
- Important source gap: the supplied `89.png` contains only the apparatus and omits the intensity graph mentioned in the text. The `7/5` first-dark-fringe readout is the calibration consistent with the recorded `1.25 λ` answer and standard interference law; it is deliberately isolated in `MatchesStatedAndGraphReadouts` pending confirmation from the missing graph.

### Current target conclusions

- `phaseDifference_at_firstDarkFringe`: the first dark fringe has phase difference `1/2` wavelength cycle.
- `materialLength_eq_fiveFourths_wavelength`: `L = (5/4)λ`, stated through dimensionful readouts in every unit system.
- `problem_phyx_mini_0089`: at `n = 2`, the phase/path difference at `P` is `(5/4)λ`, hence answer choice C.

## Goal-faithfulness audit

- No premise or premise field states the phase difference at `n = 2`, the slab-length ratio `L/λ = 5/4`, or the correctness of choice C.
- The graph premise states a measured first intensity zero at `n = 7/5`; it does not state a phase value. Converting that intensity readout to half a cycle is the conclusion of a separate lemma using the interference, path, and phase laws.
- `recordedAnswerChoice := .C` is metadata only and is not a theorem premise. `AnswerChoice.wavelengthMultiple` merely transcribes all four displayed options.
- `IsCorrectAnswer` compares the physical phase function at `n = 2` with a displayed option; it does not define the phase function or make the target true by unfolding.
- `opticalPathDifferenceAtP`, `phaseDifferenceInWavelengthsAtP`, and `combinedIntensityReadoutAtP` are fields representing measured/physical functions. Their relations are supplied only by independent governing-law predicates.
- Real numbers are used for dimensionless indices, wavelength-cycle counts, radian phases, and explicitly named intensity instrument readouts. Physical lengths use Physlib's unit-covariant `Dimensionful` representation.

## Declarations created and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0089:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0089.problem_phyx_mini_0089`.
- Supporting declarations: `VariableIndexInterferometer`, `HasDepictedCoherentLayout`, `HasPhysicalOpticalParameters`, `IsFirstDarkFringeOnDisplayedScan`, `MatchesStatedAndGraphReadouts`, `SatisfiesOpticalPathDifferenceLaw`, `SatisfiesPhaseDifferenceLaw`, and `SatisfiesTwoBeamInterferenceLaw`.
- Derived lemmas: `phaseDifference_at_firstDarkFringe` and `materialLength_eq_fiveFourths_wavelength`.
- Figure/choice labels: `RayLabel`, `MirrorLabel`, `ScreenPoint`, `AnswerChoice`, `AnswerChoice.wavelengthMultiple`, and `IsCorrectAnswer`.
- The explicit write-permission rule forbids editing blueprint chapters, so
  the theorem environment was not marked `\leanok`; the orchestrator/plan
  agent should add it after accepting this proof.

## LeanExplore queries/candidates actually used

- Query `dimensionful physical quantity length wavelength SI units` returned and grounded `Dimensionful`, `UnitChoices.SI`, `Dimension.L𝓭`, and the example `UnitExamples.meters400`. Source/module information was fetched for these candidates. The formalization uses `Dimensionful` and `Dimension.L𝓭`; the SI/example declarations informed the unit-covariant readout pattern but were not imported as problem data.
- Query `optical path length refractive index interference intensity phase difference` returned manifold/geometric path-length declarations only. These were semantic near misses and were not used for optical path length.
- Query `Real.cos two pi phase interference` returned `Real.cos` and cosine-zero lemmas including `Real.cos_eq_zero_iff`. `Real.cos` is used in the governing interference law; its source and module were fetched.
- Query `WithDim physical dimension carrier` returned `WithDim` operations and
  dimension infrastructure. The project import supplies `WithDim`; no theorem
  from those search hits was needed by the proof.
- Query `Real.pi` returned `Real.pi`, whose source/module were fetched and which is used in the `2π` interference phase.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices` from `Physlib.Units.WithDim.Basic` / underlying units modules.
- Mathlib: `Real.cos` and `Real.pi` through `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.
- Compilation succeeds and LSP diagnostics are empty.

## Local abstractions introduced

- `LengthQuantity` is an abbreviation for Physlib's genuine unit-covariant `Dimensionful (WithDim Dimension.L𝓭 ℝ)`, not a scalar alias.
- The ray, mirror, and screen-point inductives retain the qualitative labels and roles from the apparatus image.
- `VariableIndexInterferometer` is the smallest local experiment interface found adequate to keep physical lengths, coherent phases, optical paths, intensities, scan endpoints, and the point-`P` observables distinct.
- Local law/readout predicates were introduced because LeanExplore found no optics-specific API for refractive-index optical path difference or two-beam interference.

## Source evidence limitation

- The theorem is soundly proved from its stated hypotheses. Independently, the
  supplied `89.png` contains the apparatus only and omits the
  intensity-versus-`n` graph referenced by the source text. Thus the formal
  premise that the first dark fringe is at `n = 7/5` cannot be checked against
  the available image.
- No Lean redraft is requested for the current conditional theorem. The source
  owner should restore the graph and confirm `n = 7/5`. If the graph differs,
  `MatchesStatedAndGraphReadouts` and the downstream numerical theorem must be
  redrafted by an authorized formalization pass.
- `.archon/AGENTS.md` is absent in this checkout. The available
  `.archon/prover-modes/physics.md` and the user-provided prover instructions
  were followed.
