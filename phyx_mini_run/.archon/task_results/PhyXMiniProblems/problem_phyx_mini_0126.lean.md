## Review-3 disposition

The formalization-review gate rejected target `0126` only because it lacked a
genuine post-formalization report. I therefore re-read the revised Lean model,
the complete `% archon:physics` chapter, the source JSON, and the primary image;
reran LeanExplore grounding; and rechecked the file with both LSP and Lean.
That audit found no semantic defect, so the current physical statement was
preserved unchanged as required by the final retry protocol.

## Assumption/target split

### Governing laws

- `SatisfiesSingleSlitDiffractionLaws.firstMinimumLaw` states the general
  single-slit first-minimum relation `a |sin θ₁| = λ`, in every selected length
  unit and for both boundary rays.
- `exactScreenProjection` states the independent screen geometry law
  `x = L |tan θ₁|` for each half-width marked `x`.
- `firstMinimumIsDark` and `centralPointIsBrightest` identify the two boundary
  points as dark minima surrounding the central bright maximum.
- `centralMaximumAngularWidthLaw` states only the general composition rule:
  full angular width equals the sum of the two unsigned boundary-angle degree
  readouts. It contains neither `98` nor an answer label.
- `HasPhysicalParameters` supplies positivity and selects the acute branch for
  both boundary angles; it does not fix their numerical values or the answer.
- `UsesFraunhoferSingleSlitModel` records the diffraction regime separately
  from both figure evidence and the requested result.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesProblemReadouts` records wavelength `750 nm`, slit width
  `1/1000 mm`, and slit-to-screen distance `20 cm` through explicit projections
  of dimensionful lengths.
- Direct inspection of `phyx_data/test_image/126.png` confirms parallel incident
  rays, one slit, two dashed first-minimum boundary rays, two printed `49°`
  labels, `20 cm`, and matching upper/lower `x` half-width labels.
- `MatchesSingleSlitFigure` records precisely those qualitative and geometric
  readouts, including the slit/screen axial relation, central-axis coordinate,
  the two `x` segments, and their symmetry.
- `MatchesWholeDegreeReadout` interprets each printed `49°` to whole-degree
  precision as an error interval `|readout - 49| ≤ 1/2`. This is compatible
  with the ideal law: `λ/a = 750 nm / 1000 nm = 3/4`, whose acute angle is about
  `48.59°`, not exactly `49°`.
- `displayedAngularWidthDegrees` records all source choices as metadata:
  A `108°`, B `88°`, C `98°`, and D `93°`.

### Current target conclusions

- `centralMaximumAngularWidth_bounds` derives that the full central-maximum
  angular width is in `[97°, 99°]` from the two rounded angle readouts and the
  angular-width composition law.
- `problem_phyx_mini_0126` derives that same interval, proves that C is the
  unique closest displayed choice, and identifies C's displayed value as
  `98°`.

## Goal-faithfulness audit

`SingleSlitDiffractionSetup.centralMaximumAngularWidthDegrees` is an unknown
real degree readout. No premise equates it to `98`, assumes the derived
`[97, 99]` bounds, or says that C is closest. The numeral `98` occurs on the
assumption side only in the complete four-entry source answer table, alongside
all distractors. Selecting C remains a theorem conclusion.

The law interface contains general single-slit, projection, intensity, and
angle-composition relations only. The rounded `49°` values are explicitly
classified as figure evidence, not governing laws. The screen distance is
retained because it is part of the physical setup and determines linear
half-width `x`, even though it cancels out of the requested angular answer.
Thus no target conclusion is smuggled into a hypothesis, premise structure,
`Satisfies...` field, or unfolding definition.

## Declarations and blueprint correspondence

The chapter's declaration topology and the assigned file agree:

- Dimensionful quantities/readouts: `LengthQuantity`, `IrradianceQuantity`,
  `lengthReadout`, `lengthInMeters`, `lengthInCentimeters`,
  `lengthInMillimeters`, `lengthInNanometers`, and `irradianceInSI` correspond
  to the blueprint definition labels with suffixes `lengthquantity`,
  `irradiancequantity`, `lengthreadout`, `lengthinmeters`,
  `lengthincentimeters`, `lengthinmillimeters`, `lengthinnanometers`, and
  `irradianceinsi` under the common prefix
  `def:physics:phyx-mini-0126:phyxminiproblems-problemphyxmini0126-`.
- Angle/readout declarations: `degrees`, `angleInDegrees`, and
  `MatchesWholeDegreeReadout` correspond to suffixes `degrees`,
  `angleindegrees`, and `matcheswholedegreereadout`.
- Figure/model types: `ScreenSide`, `ScreenPoint`, `OpticalPlane`,
  `IncidentWavefront`, `ApertureGeometry`, `DiffractionRegime`,
  `MonochromaticLight`, `SingleSlitAperture`, and
  `SingleSlitDiffractionSetup` correspond respectively to suffixes
  `screenside`, `screenpoint`, `opticalplane`, `incidentwavefront`,
  `aperturegeometry`, `diffractionregime`, `monochromaticlight`,
  `singleslitaperture`, and `singleslitdiffractionsetup`.
- Premise-side declarations: `firstMinimumPoint`, `HasPhysicalParameters`,
  `MatchesProblemReadouts`, `MatchesSingleSlitFigure`,
  `UsesFraunhoferSingleSlitModel`, and `SatisfiesSingleSlitDiffractionLaws`
  correspond to suffixes `firstminimumpoint`, `hasphysicalparameters`,
  `matchesproblemreadouts`, `matchessingleslitfigure`,
  `usesfraunhofersingleslitmodel`, and
  `satisfiessingleslitdiffractionlaws`.
- Answer metadata: `AnswerChoice`, `displayedAngularWidthDegrees`,
  `IsClosestDisplayedAngularWidth`, and
  `IsUniqueClosestDisplayedAngularWidth` correspond to suffixes
  `answerchoice`, `displayedangularwidthdegrees`,
  `isclosestdisplayedangularwidth`, and
  `isuniqueclosestdisplayedangularwidth`.
- `centralMaximumAngularWidth_bounds` corresponds to
  `lem:physics:phyx-mini-0126:phyxminiproblems-problemphyxmini0126-centralmaximumangularwidth-bounds`.
- `problem_phyx_mini_0126` corresponds to
  `thm:physics:phyx_mini_0126:target`.

The lemma and theorem intentionally retain `by sorry` bodies because this is
the `physics-formalize` autoformalization stage. The blueprint was not edited
with `\\leanok`: the task's final write-permission section permits edits only
to the assigned Lean file and this task result, so a blueprint-authorized agent
must add that marker after acceptance.

## LeanExplore queries/candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language physics query:
  `Fraunhofer single slit diffraction first minimum slit width wavelength sine angle central maximum`.
  Results included `Real.Angle.sin` and trigonometric lemmas but no
  single-slit/Fraunhofer diffraction object or law.
- Dimensional API query:
  `Dimensionful WithDim physical quantity length dimension unit choices`.
  Used candidates: `Dimensionful` and `Dimension.L𝓭`.
- Exact-name queries: `WithDim` and `UnitChoices.SI`.
  Used candidates: `WithDim` and `UnitChoices.SI`.
- Length-unit queries:
  `LengthUnit nanometers millimeters centimeters meters` and
  `LengthUnit.meters`. Used candidates: `LengthUnit`,
  `LengthUnit.nanometers`, `LengthUnit.millimeters`, and
  `LengthUnit.centimeters`; `UnitChoices.SI` source also confirms
  `LengthUnit.meters`.
- Angle queries: `Real.Angle sin tan toReal physical angle` and
  `Real.Angle.toReal`. Used candidates: `Real.Angle.sin`,
  `Real.Angle.tan`, and `Real.Angle.toReal`.

Source and module information was fetched for all intended core candidates:

- `Dimensionful` — `Physlib.Units.Basic`; a subtype of unit-choice-indexed
  representations satisfying `HasDimension`.
- `WithDim` — `Physlib.Units.WithDim.Basic`; a dimension-tagged carrier.
- `UnitChoices.SI` — `Physlib.Units.Basic`; selects metres, seconds,
  kilograms, coulombs, and kelvin.
- `LengthUnit`, `.nanometers`, `.millimeters`, and `.centimeters` —
  `Physlib.SpaceAndTime.Space.LengthUnit`.
- `Real.Angle.sin`, `Real.Angle.tan`, and `Real.Angle.toReal` —
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`; `toReal` returns the
  canonical representative in `(-π, π]`.

LSP local search independently located `Dimensionful` in
`Physlib.Units.Basic` and `WithDim` in `Physlib.Units.WithDim.Basic`. Its local
index did not return qualified unit/angle members, but LeanExplore source data
and successful elaboration ground those names directly.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `UnitChoices`, `UnitChoices.SI`,
  `LengthUnit`, `LengthUnit.meters`, `LengthUnit.centimeters`,
  `LengthUnit.millimeters`, `LengthUnit.nanometers`, `L𝓭`, `M𝓭`, and `T𝓭`.
- Mathlib: `Real.Angle`, `Real.Angle.sin`, `Real.Angle.tan`,
  `Real.Angle.toReal`, `Real.pi`, and `NNReal`.

## Local abstractions introduced

- `SingleSlitDiffractionSetup` and the small finite label types preserve the
  optical objects, geometry, screen locations, and figure roles absent from the
  libraries; physical lengths and irradiance are not collapsed to bare reals.
- `SatisfiesSingleSlitDiffractionLaws` is the smallest local governing-law
  interface needed because no Mathlib/Physlib Fraunhofer single-slit API was
  found. Its fields are answer-independent laws.
- `MatchesWholeDegreeReadout` models the precision of a displayed scalar
  component while retaining `Real.Angle` for the physical angle itself.
- `AnswerChoice`, the displayed-value table, and closest-choice predicates
  preserve the multiple-choice source metadata without assuming the selected
  answer.

## Grounding gaps and redraft requests

- LeanExplore exposed no library declaration for Fraunhofer single-slit first
  minima, their screen projections, or central-maximum angular width. The
  answer-independent local law interface is therefore necessary.
- The chapter gives the physical source and declaration topology but not the
  useful informal numerical derivation `sin θ = λ/a = 3/4` and
  `2θ ≈ 97.18°`; a future plan-agent revision could add it.
- The requested `.archon/AGENTS.md` is absent in this checkout. The applicable
  `.archon/prover-modes/physics-formalize.md` role document was read instead.
- The assigned Lean file contains no `/- USER: ... -/` comment.
- The prompt advertises `archon` on `PATH`, but `archon dag-query ...` returned
  `command not found`; the source report independently establishes that there
  are no previous parts.

## Verification

- `archon-lean-lsp` reported no errors or failed dependencies and exactly two
  expected `declaration uses sorry` warnings, at the lemma and target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0126.lean` exited with code
  0 and emitted the same two expected warnings.
