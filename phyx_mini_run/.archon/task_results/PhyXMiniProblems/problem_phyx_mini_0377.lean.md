# Autoformalization result: `problem_phyx_mini_0377.lean`

## Review-gate remediation

This iteration-003 report is genuine post-formalization evidence for the
current Lean model. The exact review-gate reason was evidence-only: the gate
did not accept the generic preflight as proof of the searches, grounding,
abstractions, and source/law/answer split actually used for the revised file.
I therefore preserved the physical statement, re-read the source JSON and
blueprint, inspected the primary image, reran the searches below with the
required package filters, fetched the selected declarations' source and
modules, and rechecked the current Lean file.

The primary sources audited were:

- `reports/phyx_mini/problem_phyx_mini_0377.source.json`;
- `phyx_data/test_image/377.png`;
- `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0377.tex`.

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
applies. There are no file-specific `/- USER: ... -/` comments.

## Assumption/target split

### Governing laws

- `SatisfiesRmsSpeedLaw.rms_speed_squared_is_mean` states the generic RMS law:
  the square of the RMS-speed SI readout equals the arithmetic mean of the six
  squared Euclidean speed readouts.
- The mean uses `Fintype.card MoleculeLabel`; the law contains no instance-
  specific sum, exact root, displayed answer value, or answer label.
- Nonnegativity is carried by Physlib's `DimSpeed`. Its fetched source is
  `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`, so its scalar carrier is `NNReal`.

### Previous-part results

- None. The source report's `previous_parts` array is empty, and there are no
  dependency claims in the problem source.

### Figure/data readouts

- The figure has axes represented by `i-hat` and `j-hat`, and molecule labels
  1 through 6.
- The image's signed velocity components in metres per second are molecule 1
  `(10, -10)`, molecule 2 `(2, 15)`, molecule 3 `(-8, 6)`, molecule 4
  `(-10, -2)`, molecule 5 `(6, 5)`, and molecule 6 `(0, -14)`.
- Direct image inspection confirms molecule 4's printed expression
  `-10 i-hat - 2 j-hat`. The auxiliary caption's phrase "slightly upwards"
  conflicts with the signed label and was not treated as data.
- Display metadata consists of A `12.2 m/s`, B `12.5 m/s`, C `18.2 m/s`, D
  `10.2 m/s`, with recorded label A.

### Current target conclusions

- `sumOfSquaredSpeeds_fromPrimaryFigure`: the sum of squared speed readouts is
  `890 m²/s²`.
- `rmsSpeed_exact`: the exact RMS-speed readout is `sqrt (445 / 3) m/s`.
- `problem_phyx_mini_0377`: the same exact result holds and is within
  `0.05 m/s` of recorded choice A's displayed `12.2 m/s`.

## Source/law/answer audit

- Source: `MatchesProblemAndPrimaryFigure` contains only the twelve signed
  component readouts visible in the image.
- Law: `SatisfiesRmsSpeedLaw` contains only the generic mean-square equation
  for an independent `DimSpeed` parameter.
- Answer: `890`, `sqrt (445 / 3)`, and agreement with A are derived
  conclusions. Recorded label A and all four displayed speeds are retained
  only as source metadata.

## Goal-faithfulness audit

`SixMoleculeGasSnapshot.velocity` stores six independent, unit-independent,
dimensionful planar velocity vectors. `MatchesProblemAndPrimaryFigure` has no
RMS-speed field, squared-speed sum, exact root, tolerance judgment, or answer
selection. `SatisfiesRmsSpeedLaw` has no occurrence of `890`, `445 / 3`,
`Real.sqrt`, `12.2`, or choice A.

The physical `rmsSpeed` is an independent theorem parameter. It is not locally
defined as the requested exact value. The exact value first appears in lemma
and theorem conclusions. Although the displayed answer values are necessarily
defined as metadata, unfolding `MatchesAnswerChoice` leaves a substantive
inequality involving the independently constrained RMS speed; it does not
select A or prove the inequality by definition. Thus no current target was
smuggled into a hypothesis, structure field, governing-law predicate, or local
definition.

## Declarations and blueprint labels

- `PlanarAxis` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-planaraxis`.
- `PlanarVelocity` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-planarvelocity`.
- `componentsInMetersPerSecond` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-componentsinmeterspersecond`.
- `speedSquaredInMetersSquaredPerSecondSquared` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-speedsquaredinmeterssquaredpersecondsquared`.
- `speedInMetersPerSecond` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-speedinmeterspersecond`.
- `MoleculeLabel` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-moleculelabel`.
- `SixMoleculeGasSnapshot` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-sixmoleculegassnapshot`.
- `MatchesProblemAndPrimaryFigure` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-matchesproblemandprimaryfigure`.
- `SatisfiesRmsSpeedLaw` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-satisfiesrmsspeedlaw`.
- `sumOfSquaredSpeeds_fromPrimaryFigure` —
  `lem:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-sumofsquaredspeeds-fromprimaryfigure`.
- `rmsSpeed_exact` —
  `lem:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-rmsspeed-exact`.
- `AnswerChoice` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-answerchoice`.
- `AnswerChoice.speedInMetersPerSecond` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-answerchoice-speedinmeterspersecond`.
- `recordedAnswerChoice` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-recordedanswerchoice`.
- `MatchesAnswerChoice` —
  `def:physics:phyx-mini-0377:phyxminiproblems-problemphyxmini0377-matchesanswerchoice`.
- `problem_phyx_mini_0377` —
  `thm:physics:phyx_mini_0377:target`.

No public declaration was added, removed, or renamed in iteration 003 because
the gate reported no semantic defect in this declaration topology.

## LeanExplore queries/candidates actually used

Every search in iteration 003 passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `physical velocity vector quantity with dimensions
  length per time` returned `Dimension`, `UnitExamples.SpeedEq`,
  `Dimension.L𝓭`, and `Lorentz.Velocity`, among others. The dimension API is
  applicable; relativistic `Lorentz.Velocity` is not a model of this finite
  nonrelativistic gas snapshot.
- Natural-language query `root mean square speed of a finite collection of
  velocity vectors` returned
  `CanonicalEnsemble.meanSquareEnergy_of_fintype`, variance lemmas, and
  `RigidBodyMotion.velocity`. None states the needed finite-ensemble RMS law.
- Natural-language query `EuclideanSpace squared norm equals sum of squared
  coordinates` returned `EuclideanSpace.norm_sq_eq` and
  `EuclideanSpace.real_norm_sq_eq`, validating the squared-norm model.
- Likely-name query `DimSpeed Dimensionful WithDim UnitChoices.SI` returned
  `Dimensionful` and `UnitChoices.SI`; separate likely-name searches
  `DimSpeed`, `WithDim`, `Dimension.T𝓭`, `EuclideanSpace`, and `Real.sqrt`
  returned those exact declarations.
- Natural-language query `Real.sqrt square nonnegative` returned
  `Real.sqrt_nonneg`, `Real.coe_sqrt`, and the `NNReal` square-root lemmas,
  grounding the nonnegative-root interpretation.

Source and module data were then fetched only for selected declarations used
to shape the file: `Dimensionful`, `WithDim`, `DimSpeed`, `Dimension.L𝓭`,
`Dimension.T𝓭`, `UnitChoices.SI`, `EuclideanSpace`,
`EuclideanSpace.norm_sq_eq`, and `Real.sqrt`.

The generated LeanExplore summary described `DimSpeed` as "Dimensionless
Speed", but its fetched source is authoritative and defines a dimensionful
speed with dimension `L𝓭 * T𝓭⁻¹`; the model follows the source rather than the
summary wording.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful` and `UnitChoices.SI` from `Physlib.Units.Basic`;
  `WithDim` from `Physlib.Units.WithDim.Basic`; `Dimension.L𝓭` and
  `Dimension.T𝓭` from `Physlib.Units.Dimension`; `DimSpeed` from
  `Physlib.Units.WithDim.Speed`.
- Mathlib: `EuclideanSpace` and `EuclideanSpace.norm_sq_eq` from
  `Mathlib.Analysis.InnerProductSpace.PiL2`; `Real.sqrt` from
  `Mathlib.Analysis.Real.Sqrt`; plus standard finite sums, `Fintype.card`, norm
  notation, and `NNReal` infrastructure supplied by those imports.

## Local abstractions introduced

- `PlanarAxis` and `MoleculeLabel` preserve the exact figure directions and
  labels instead of erasing them to anonymous scalar indices.
- `PlanarVelocity` combines Physlib's unit-independent dimensional semantics
  with Mathlib's two-coordinate Euclidean vector. It is the smallest model
  that retains signed vector components and velocity dimension.
- `SixMoleculeGasSnapshot` minimally associates each pictured molecule with
  its dimensionful velocity.
- `MatchesProblemAndPrimaryFigure` isolates source evidence from laws and
  conclusions.
- `SatisfiesRmsSpeedLaw` is local because no matching library declaration was
  found. Its sole field is the generic mean-square relation, not this
  problem's numerical result.
- `AnswerChoice` and `MatchesAnswerChoice` preserve the displayed-choice role
  and one-decimal rounding tolerance without redefining the physical speed.

## Grounding gaps

- Mathlib/Physlib has no direct declaration for RMS speed of a finite gas
  ensemble of dimensionful planar velocities. The local predicate preserves
  the standard law without embedding the answer.
- Physlib's `DimSpeed` is a nonnegative scalar speed, not a signed planar
  velocity; the local `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹)
  (EuclideanSpace ℝ PlanarAxis))` construction fills that modeling gap.
- `.archon/AGENTS.md` is absent, so the available
  `.archon/prover-modes/physics-formalize.md` supplied the role discipline.
- The prompt advertised `archon` on `PATH`, but `archon dag-query ...` failed
  with `command not found`. The source report independently establishes that
  `previous_parts` is empty.
- No blueprint redraft is requested. The chapter was not edited because this
  task's explicit write permissions restrict changes to the assigned Lean file
  and result report. A coordinator with blueprint write permission should add
  `\leanok` to the completed target environment.

## Verification

- `archon-lean-lsp` reports exactly three expected `declaration uses sorry`
  warnings, for the two derived lemmas and final theorem, with no errors or
  failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0377.lean` succeeds with
  the same three expected warnings.
- No-index `git diff --check` runs for the assigned Lean file and this report
  emit no whitespace diagnostics.
