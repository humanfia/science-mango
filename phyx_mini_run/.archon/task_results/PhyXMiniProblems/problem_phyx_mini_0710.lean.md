# Autoformalization result: `problem_phyx_mini_0710.lean`

## Assumption/target split

### Governing laws

- `SatisfiesCenteredCanGeometry`: the axial base width is the cylinder diameter, and a centered mass distribution puts the center of mass halfway across the base and halfway up the can. These are unsolved geometric relations stated in every `LengthUnit`.
- `SatisfiesLimitingLineOfActionGeometry`: at the tipping threshold, the vertical gravity line through the center of mass passes through the downhill pivot; its tangent/normal projection equation contains no solved height.
- `SatisfiesStaticStabilityLaw`: for an otherwise identical can of candidate height, the gravity line remains in the base footprint exactly when `height * sin θ ≤ b * cos θ`. This is a general law over all candidate heights and contains no numerical answer.
- `HasPhysicalCanParameters`: positivity of the physical lengths and gravity magnitude, together with the acute-angle branch condition.

### Previous-part results

- None. The source report records `previous_parts: []`.

### Figure/data readouts

- Prose input: cylinder diameter `7.5 cm` and incline angle `30°`.
- Primary image 710: axial can cross-section, inclined plane, central center-of-mass mark, downward `F_G`, dashed line of action through the center of mass and downhill pivot, base label `b`, height label `h_max`, incline label `30°`, and can-rotation label `30°`.
- `MatchesCanOnInclineScenario`, `MatchesCanProblemReadouts`, and `MatchesSuppliedCanFigure` encode those qualitative and numeric observations. The height label denotes the unknown physical height but supplies no numeric height.
- The four displayed options are `8`, `10`, `13`, and `15` centimeters; dataset metadata records label C separately.

### Current target conclusions

- Exact limiting height: `lengthInCentimeters setup.heightHMax = (15 / 2) * Real.sqrt 3`.
- Physical maximality: `IsTallestStableHeight setup setup.heightHMax`.
- Multiple-choice result: `IsUniqueClosestDisplayedHeight setup .C`, so `13 cm` is the unique closest displayed approximation to the exact threshold.

## Goal-faithfulness audit

No premise asserts the exact height, maximality, or unique selection of C. The readout assumptions contain only the given diameter and angle. The figure assumptions contain labels, arrow direction, and incidences, but explicitly no numerical height answer. The centered-cylinder and limiting-line structures state unsolved physical geometry, while the statics structure states a law for every candidate height. `IsTallestStableHeight`, `IsClosestDisplayedHeight`, and `IsUniqueClosestDisplayedHeight` are genuine target predicates rather than definitions that unfold to the requested answer. `recordedDatasetAnswer := .C` preserves source metadata but is not used to make the theorem conclusion true.

The helper lemma derives `h_max = b / tan θ`; it is not included in any premise. The final exact value, maximality, and option selection remain solely in the conclusion of `problem_phyx_mini_0710`.

## Declarations created

- Blueprint label `thm:physics:phyx_mini_0710:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0710.problem_phyx_mini_0710`.
- Supporting derived lemma: `limitingHeightInCentimeters_eq_base_div_tan`.
- Dimensionful quantities/readouts: `forceDimension`, `LengthQuantity`, `ForceMagnitudeQuantity`, `lengthReadout`, `lengthInCentimeters`, and `forceMagnitudeInNewtons`.
- Physical and figure vocabulary: `CanShape`, `CanMassDistribution`, `CanOrientation`, `SupportSurfaceKind`, `CanPoint`, `VerticalDirection`, `FigureObject`, `FigureLabel`, `GravitationalForce`, `SuppliedCanFigure`, and `CanOnInclineSetup`.
- Premise interfaces: `MatchesCanOnInclineScenario`, `MatchesCanProblemReadouts`, `MatchesSuppliedCanFigure`, `HasPhysicalCanParameters`, `SatisfiesCenteredCanGeometry`, `SatisfiesLimitingLineOfActionGeometry`, and `SatisfiesStaticStabilityLaw`.
- Target/choice vocabulary: `IsTallestStableHeight`, `AnswerChoice`, `displayedHeightCentimeters`, `recordedDatasetAnswer`, `IsClosestDisplayedHeight`, and `IsUniqueClosestDisplayedHeight`.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- `dimensionful physical length with named unit readout` and `LengthUnit Dimensionful WithDim`: selected `Dimensionful`, `LengthUnit`, `Dimension.L𝓭`, and `WithDim`.
- `LengthUnit.centimeters`, `UnitChoices.SI`, and `WithDim`: confirmed the exact Physlib names and representations used for named-unit readouts.
- `trigonometric values sine cosine pi over six`, `Real.sin_pi_div_six`, and `Real.cos_pi_div_six`: confirmed the Mathlib special-angle declarations supporting the later proof.
- `static stability tipping center of mass line of action`: returned general center-of-mass and rigid-body declarations such as `RigidBody.centerOfMass`, but no can-on-incline footprint/tipping theorem with a compatible signature.

Source, module, and docstring data were fetched for the candidates actually used: `Dimensionful`, `LengthUnit`, `LengthUnit.centimeters`, `UnitChoices.SI`, `WithDim`, `Real.sin_pi_div_six`, and `Real.cos_pi_div_six`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful` (`Physlib.Units.Basic`), `WithDim` (`Physlib.Units.WithDim.Basic`), `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`, `LengthUnit`, and `LengthUnit.centimeters`.
- Mathlib: `NNReal`, `Real.pi`, `Real.sin`, `Real.cos`, `Real.tan`, `Real.sqrt`, `Real.sin_pi_div_six`, and `Real.cos_pi_div_six`.

## Local abstractions introduced

- The shape, orientation, support, point, force-direction, and figure-label inductives retain roles that are not represented by a matching library object.
- `GravitationalForce` keeps dimensionful magnitude, application point, and direction separate instead of collapsing force to a scalar.
- `CanOnInclineSetup` stores the dimensionful geometry and the family of candidate-height stability propositions.
- The centered-cylinder geometry, limiting line-of-action geometry, and static-stability predicates are narrow law interfaces matching the source physics. They avoid defining the unknown height or requested answer.

## Grounding gaps

- LeanExplore exposed rigid-body center-of-mass infrastructure but no directly reusable theorem for static tipping of a cylinder on an incline. The local law interfaces preserve the missing physical content without guessing an unavailable API.
- The requested `.archon/AGENTS.md` was absent in this workspace; the matching archived project role document and the current `.archon/prover-modes/physics-formalize.md` were read instead.
- The prompt advertised `archon` on `PATH`, but `archon dag-query` was unavailable in the shell, so no dependency-graph result could be collected. The blueprint has no stated `\uses` dependencies and the source report has no previous parts.

## Verification and marker readiness

- `archon-lean-lsp` diagnostics report only two expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0710.lean` exits successfully with the same two warnings.
- The statement for `thm:physics:phyx_mini_0710:target` is ready for the deterministic `\leanok` synchronization. The blueprint was not edited because prover write permissions explicitly forbid blueprint changes.
- No blueprint redraft is requested.
