# Autoformalization result: `problem_phyx_mini_0029.lean`

## Assumption/target split

### Governing laws

- `ObeysThinLensEquation` states the signed thin-lens equation
  `1/f = 1/dₒ + 1/dᵢ` using SI scalar readouts of dimensionful lengths.
- `ObeysOpticalPowerLaw` states the general relation `P = 1/f`, with the power
  readout in inverse metres (diopters).
- `UsesEyePlaneLensApproximation` states the standard approximation that the
  spectacle lens is at the eye plane, rather than silently identifying
  eye-relative and lens-relative distances.
- `FormsVirtualImageAtUnaidedNearPoint` states that the near segment forms a
  virtual image at the unaided near point, with negative image distance under
  the selected sign convention.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `HasStatedDistanceReadouts` records the unaided near point `30 cm`, unaided
  far point `1.5 m`, and requested reading distance `25 cm` as SI readouts of
  dimensionful lengths.
- `HasPhysicalDistanceOrdering` records that `25 cm < 30 cm < 1.5 m` and that
  the requested distance is positive.
- `MatchesBifocalFigure` records the primary image's upper/far and lower/near
  labels and identifies the requested correction as the lower segment.
- `answerPowerDiopters` transcribes all four answer values; choice D is
  `667/1000` diopters.

### Current target conclusions

- `reciprocalFocalLength_eq_two_thirds` concludes that the stated placement
  and lens law determine reciprocal focal length `2/3 m⁻¹`.
- `problem_phyx_mini_0029` concludes that the lower near-vision segment has
  exact power `+2/3` diopters and that choice D's `+0.667` diopter value is a
  nearest-thousandth readout of it.

## Goal-faithfulness audit

Neither exact power `2/3` nor the claim selecting D appears in
`BifocalFitting`, a setup predicate, or a theorem hypothesis. The hypotheses
only provide the independent source/figure readouts, sign convention,
eye-plane approximation, virtual-image prescription, and general thin-lens
and power laws. The reciprocal-focal-length statement is a derived lemma with
a `by sorry` body, not a premise. The answer table only transcribes all printed
choices, and the generic nearest-thousandth predicate does not select D by
unfolding.

Lengths and optical powers are not scalar aliases: they use
`Dimensionful (WithDim L𝓭 ℝ)` and `Dimensionful (WithDim L𝓭⁻¹ ℝ)`, respectively.
Real values occur only as named SI readouts, ratios, and answer-choice
measurements. No physical statement was replaced by `True`, reflexivity, or an
unrelated algebraic fact.

## Declarations created and blueprint labels

- `DimLength` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-dimlength`.
- `DimOpticalPower` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-dimopticalpower`.
- `lengthInMeters` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-lengthinmeters`.
- `powerInDiopters` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-powerindiopters`.
- `BifocalSegment` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-bifocalsegment`.
- `VisionRole` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-visionrole`.
- `ClearVisionRange` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-clearvisionrange`.
- `ThinCorrectiveLens` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-thincorrectivelens`.
- `BifocalFitting` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-bifocalfitting`.
- `HasStatedDistanceReadouts` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-hasstateddistancereadouts`.
- `HasPhysicalDistanceOrdering` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-hasphysicaldistanceordering`.
- `MatchesBifocalFigure` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-matchesbifocalfigure`.
- `UsesEyePlaneLensApproximation` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-useseyeplanelensapproximation`.
- `FormsVirtualImageAtUnaidedNearPoint` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-formsvirtualimageatunaidednearpoint`.
- `ObeysThinLensEquation` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-obeysthinlensequation`.
- `ObeysOpticalPowerLaw` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-obeysopticalpowerlaw`.
- `AnswerChoice` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-answerchoice`.
- `answerPowerDiopters` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-answerpowerdiopters`.
- `IsNearestThousandthReadout` — `def:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-isnearestthousandthreadout`.
- `reciprocalFocalLength_eq_two_thirds` — `lem:physics:phyx-mini-0029:phyxminiproblems-problemphyxmini0029-reciprocalfocallength-eq-two-thirds`.
- `problem_phyx_mini_0029` — `thm:physics:phyx_mini_0029:target`.

The chapter already existed and contained `% archon:physics`. It was not
edited because the task's explicit write permissions allow changes only to the
assigned Lean file and this task-result file; a later authorized blueprint
sync should add `\leanok` to the target environment.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- `thin lens equation focal length object distance image distance geometrical
  optics` returned `LengthUnit` plus unrelated category-theoretic thinness and
  Euclidean inversion results; no thin-lens law was usable.
- `optical power reciprocal focal length diopter corrective lens` returned
  reciprocal-power algebra and geometric power-of-a-point results; no optical
  power/diopter API was usable.
- `Dimensionful physical quantity with units` selected `Dimensionful`
  (id 394284).
- `WithDim` selected `WithDim` (id 394425).
- `Dimension.L𝓭` selected `Dimension.L𝓭` (id 394324).
- `WithDim inverse length SI unit choices` selected `UnitChoices.SI`
  (id 394270) and identified `Dimension.inv_length` as a related candidate.

Source, module, and docstring were fetched for the four declarations actually
used: `Dimensionful` (module `Physlib.Units.Basic`), `WithDim` (module
`Physlib.Units.WithDim.Basic`), `Dimension.L𝓭` (module
`Physlib.Units.Dimension`), and `UnitChoices.SI` (module
`Physlib.Units.Basic`).

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `WithDim.val`, `Dimension.L𝓭`, inverse
  dimension notation `L𝓭⁻¹`, and `UnitChoices.SI`.
- Mathlib: `ℝ`, integer-to-real coercion, absolute value, arithmetic, and order
  used by the SI equations and rounding predicate. The file now imports
  `Mathlib` explicitly, in addition to `Physlib.Units.WithDim.Basic`, to address
  the iteration-001 review reason and ensure checking in the real Lake/Mathlib
  environment.

## Local abstractions introduced

- `BifocalSegment` and `VisionRole` preserve the primary figure's distinct
  upper/far and lower/near labels.
- `ClearVisionRange`, `ThinCorrectiveLens`, and `BifocalFitting` keep eye
  distances, signed lens distances, focal length, optical power, and segment
  assignment distinct while giving physical lengths and power their correct
  dimensions.
- The approximation, virtual-image placement, thin-lens equation, and optical
  power law are explicit local predicates because no matching installed
  Mathlib/Physlib geometrical-optics declarations were found.
- `IsNearestThousandthReadout` captures the measurement-reporting relation
  between exact `2/3` and printed `0.667` without assuming the answer choice.

## Grounding gaps and redraft requests

- No installed thin-lens, focal-length, virtual-image, corrective-lens, or
  diopter API was found; the local predicates above are the faithful gap-filling
  interface.
- The requested `.archon/AGENTS.md` is absent. Role behavior was taken from the
  user instructions and `.archon/prover-modes/physics-formalize.md`.
- The `archon` executable is not on `PATH`, so the optional DAG queries could
  not run. The source report independently establishes that there are no
  previous parts.
- There were no `/- USER: ... -/` hints in the assigned Lean file.
- No physical-statement redraft is requested.

## Source/law/answer audit

- Source text supplies the clear-vision endpoints `30 cm` and `1.5 m`, the
  requested object distance `25 cm`, and all four printed answer readouts.
- Primary image `phyx_data/test_image/29.png` supplies only the upper/far and
  lower/near segment labeling; no numeric geometry was inferred from it.
- Physics laws are confined to the eye-plane approximation, virtual-image sign
  convention, signed thin-lens equation, and optical-power law hypotheses.
- The recorded answer D is retained as answer-table metadata. The theorem must
  derive both exact `2/3` diopters and the nearest-thousandth relation to
  `667/1000`; neither conclusion is a premise or structure field.

## Autoformalization verification (before iteration 012 prover work)

- At the autoformalization stage,
  `lake env lean PhyXMiniProblems/problem_phyx_mini_0029.lean` exited 0 with
  the two then-expected `sorry` warnings.
- The current post-prover verification is recorded below.

## Prover result — iteration 012

Status: complete. Both assigned placeholders were closed without changing any
declaration signature.

- `reciprocalFocalLength_eq_two_thirds`: unfolded the source-distance,
  eye-plane, virtual-image, and thin-lens hypotheses, then reduced
  `1 / 0.25 + 1 / (-0.30)` to `2 / 3` with `norm_num`.
- `problem_phyx_mini_0029`: transferred the reciprocal focal-length result
  through `ObeysOpticalPowerLaw`, supplied the integer-thousandths witness
  `667`, and proved the rounding error bound for `667 / 1000`.

Verification:

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0029.lean` exits 0.
- Lean LSP reports no errors or failed dependencies. Its only warnings are that
  frozen-contract hypotheses `h_order` and `h_figure` are not needed by the
  numerical derivation.
- A source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- The theorem axiom audit reports only Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound`.

No redraft is needed. The helper lemma and target theorem are ready for
deterministic blueprint `\leanok` synchronization; the blueprint was not
edited because prover write permissions reserve marker updates for the sync
phase.
