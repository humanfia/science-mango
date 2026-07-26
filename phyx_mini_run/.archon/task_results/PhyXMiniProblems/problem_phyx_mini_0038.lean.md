# Autoformalization result: `problem_phyx_mini_0038.lean`

## Retry outcome

The iteration-002 gate rejected this target only because no genuine
post-formalization task result existed. I audited the revised Lean statement
against the cited source report and primary image and found no semantic defect,
so the physical statement was preserved. This report records the actual
post-formalization grounding and source/law/answer audit required by the final
retry protocol.

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was used. The primary image was inspected directly. It shows a concave mirror
at the right, the object and screen in front of it, a real inverted image on
the screen, a horizontal optic axis, the center of curvature `C`,
`s = 10.0 cm`, `s' = 3.00 m`, `h = 5.00 mm`, and unknowns `h'` and `R`.
Those observations agree with both the problem text and the source report.

## Physical model extracted

- Physical lengths: object distance `s`, image distance `s'`, object height
  `h`, image-height magnitude `h'`, focal length `f`, and curvature-radius
  magnitude `R`. Each is represented by a unit-coherent Physlib
  `Dimensionful (WithDim Dimension.L𝓭 ℝ)`, not by a bare real scalar.
- Scalar measurement projections: metres, centimetres, and millimetres are
  explicit readouts of the same dimensionful length under a selected
  `UnitChoices` value.
- Figure labels and qualitative roles: concave versus convex mirror, real
  versus virtual image, wall/screen receiver, upright versus inverted image,
  horizontal principal axis, and the point `C` represented through the
  vertex-to-center radius field.
- Governing relations: the paraxial spherical-mirror equation and the
  spherical-mirror relation `R = 2f`.
- Requested result: the exact focal length `300/31 cm` and the fact that its
  nearest-hundredth display is choice B, `9.68 cm`.

## Assumption/target split

### Governing laws

- `ObeysSphericalMirrorEquation` states the generic paraxial law
  `f * (s + s') = s * s'` for every unit system. This is the division-free,
  dimensionally homogeneous form of `1/f = 1/s + 1/s'`.
- `ObeysRadiusFocalLengthLaw` states the independent spherical-mirror law
  `R = 2f` for every unit system. It captures the unknown `R` and point `C`
  shown in the figure; it does not prescribe a focal-length value.
- `HasPhysicalLengthSigns` records the positive-magnitude branch appropriate
  to the depicted real-image configuration.

### Previous-part results

- None. The source report has `previous_parts: []`, and the problem is
  standalone.

### Figure/data readouts and answer metadata

- `MatchesFigureReadouts` records a concave mirror, a real inverted image on
  the wall/screen, a horizontal principal axis, `s = 10 cm`, `s' = 3 m`, and
  `h = 5 mm`.
- The setup retains the unknown `h'`, focal length, and curvature radius as
  independent physical fields. `MatchesFigureReadouts` deliberately does not
  assign any of them a value.
- `AnswerChoice.focalLengthCentimeters` records every displayed choice:
  A `8.68 cm`, B `9.68 cm`, C `9.66 cm`, and D `9.05 cm`.
- `IsNearestHundredthReadout` is a generic decimal-grid/error predicate: the
  reported value is an integer number of hundredths and lies within half of
  `0.01` of the exact value.

### Current target conclusions

- `focalLengthCentimeters_eq_threeHundred_div_thirtyOne` concludes from the
  two distance readouts and the mirror equation that `f = 300/31 cm`.
- `problem_phyx_mini_0038` concludes that exact physical readout and that
  choice B's `9.68 cm` is its nearest-hundredth report.

## Goal-faithfulness audit

Neither `300/31` nor the assertion that B is the nearest answer occurs in any
theorem hypothesis, setup field, governing-law predicate, sign predicate, or
figure-readout predicate. The focal-length field is independent, and the
mirror equation relates it symbolically to the independently named object and
image distances. The source answer `9.68 cm` occurs only in the complete table
of all four printed answer choices; merely unfolding that table does not prove
that B matches the derived focal length. `IsNearestHundredthReadout` is generic
in both its exact and reported values.

The substantive target is not `True`, a reflexive equality, or a target-shaped
definition. `OpticalLength` is an abbreviation only for Physlib's genuine
unit-dependent dimensional type, not for `ℝ` or a local one-field scalar
wrapper. Real numbers appear only as named unit readouts and exact numerical
display values.

Numerically, the symbolic result follows from
`f = ss'/(s+s') = (10*300)/(10+300) = 300/31 cm`, and
`|300/31 - 9.68| = 2/775 cm < 1/200 cm`. Thus the source's recorded answer B
is consistent with the law and readouts, while remaining a conclusion rather
than an assumption.

## Declarations and blueprint correspondence

- `OpticalLength` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-opticallength`.
- `choicesWithLengthUnit` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-choiceswithlengthunit`.
- `lengthReadout` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-lengthreadout`.
- `metersValue` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-metersvalue`.
- `centimetersValue` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-centimetersvalue`.
- `millimetersValue` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-millimetersvalue`.
- `SphericalMirrorKind` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-sphericalmirrorkind`.
- `MirrorImageNature` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-mirrorimagenature`.
- `ImageReceiver` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-imagereceiver`.
- `ImageOrientation` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-imageorientation`.
- `PrincipalAxisOrientation` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-principalaxisorientation`.
- `ConcaveMirrorImagingSetup` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-concavemirrorimagingsetup`.
- `MatchesFigureReadouts` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-matchesfigurereadouts`.
- `HasPhysicalLengthSigns` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-hasphysicallengthsigns`.
- `ObeysSphericalMirrorEquation` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-obeyssphericalmirrorequation`.
- `ObeysRadiusFocalLengthLaw` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-obeysradiusfocallengthlaw`.
- `AnswerChoice` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-answerchoice`.
- `AnswerChoice.focalLengthCentimeters` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-answerchoice-focallengthcentimeters`.
- `IsNearestHundredthReadout` —
  `def:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-isnearesthundredthreadout`.
- `focalLengthCentimeters_eq_threeHundred_div_thirtyOne` —
  `lem:physics:phyx-mini-0038:phyxminiproblems-problemphyxmini0038-focallengthcentimeters-eq-threehundred-div-thirtyone`.
- `problem_phyx_mini_0038` —
  `thm:physics:phyx_mini_0038:target`.

The blueprint environments were not edited because the explicit prover write
permissions make blueprint chapters read-only. The synchronization/plan lane
should add `\leanok` to these audited environments.

## LeanExplore queries and candidates actually used

Every query passed `packages: ["Mathlib", "Physlib"]`.

- Natural language: `dimensionful physical quantity with dimensions and unit
  choices`. This recovered `Dimensionful` (id 394284) and nearby Physlib
  dimensional infrastructure.
- Natural language: `length units meters centimeters millimeters`. This
  recovered `LengthUnit` (id 393137), `LengthUnit.centimeters` (id 393160),
  `LengthUnit.millimeters` (id 393159), and `UnitChoices.SI_length`.
- Likely names: `UnitChoices SI length unit` and exact `UnitChoices`. These
  recovered `UnitChoices` (id 394255) and `UnitChoices.SI` (id 394270).
- Likely names: `WithDim Dimension.L𝓭 real physical length`. This recovered
  `Dimension.L𝓭` (id 394324), `WithDim` (id 394425), and the multiplication
  instance `WithDim.instHMulRealHMulDimension` (id 394453).
- Natural language: `paraxial spherical mirror equation focal length radius
  of curvature`. Results concerned cosmological/metric spheres and polynomial
  mirroring; no Mathlib/Physlib geometrical-optics mirror equation was found.

Source, module, and docstring were fetched for every selected candidate. They
confirm:

- `Dimensionful` is a coherent subtype of functions from `UnitChoices`, in
  `Physlib.Units.Basic`;
- `UnitChoices` and `UnitChoices.SI` are the unit-system structure and SI
  choice (whose length unit is metres), in `Physlib.Units.Basic`;
- `LengthUnit`, `LengthUnit.centimeters`, and `LengthUnit.millimeters` are in
  `Physlib.SpaceAndTime.Space.LengthUnit`, with scales `10^-2` and `10^-3`
  metre;
- `Dimension.L𝓭` is the length dimension, in `Physlib.Units.Dimension`;
- `WithDim` and its dimension-combining real multiplication instance are in
  `Physlib.Units.WithDim.Basic`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `UnitChoices`, `UnitChoices.SI`, `LengthUnit`,
  `LengthUnit.centimeters`, `LengthUnit.millimeters`, `Dimension.L𝓭`,
  `WithDim`, `WithDim.val`, and
  `WithDim.instHMulRealHMulDimension`.
- Mathlib: `ℝ`, `ℤ`, exact real division and order, and real absolute value,
  made available by the direct `import Mathlib`.

Lean LSP local search additionally confirmed `Dimensionful` in
`Physlib.Units.Basic`; diagnostics successfully elaborated all selected names
and dimensional operations.

## Local abstractions introduced

- `ConcaveMirrorImagingSetup` is the smallest scene structure retaining all
  physical lengths and qualitative labels shown in the figure, including the
  otherwise unused height and radius quantities.
- The five qualitative inductives preserve mirror kind, image nature,
  receiver, transverse orientation, and principal-axis orientation instead
  of erasing them into scalar flags.
- `MatchesFigureReadouts` and `HasPhysicalLengthSigns` separate calibrated
  source observations from the physical laws and requested result.
- `ObeysSphericalMirrorEquation` and `ObeysRadiusFocalLengthLaw` are faithful
  local governing-law predicates because the searches found no usable
  geometrical-optics mirror API.
- `AnswerChoice` and `IsNearestHundredthReadout` preserve the complete answer
  display and its precision semantics without assuming the selected answer.

## Grounding gaps and redraft requests

- No Mathlib/Physlib spherical-mirror imaging API was found. The local law
  predicates should remain unless such infrastructure is later added.
- No semantic Lean redraft is requested: the primary image, source report,
  governing laws, exact result, and recorded answer agree.
- The requested `.archon/AGENTS.md` does not exist. The active role discipline
  was recovered from `.archon/prover-modes/physics-formalize.md` and the
  invocation itself. There were no `/- USER: ... -/` hints in the assigned
  Lean file.
- The `archon` executable was not available on `PATH`, so the optional DAG
  query could not run. The source report independently establishes that there
  are no previous parts.

## Verification

- Lean LSP diagnostics report no errors or failed dependencies and exactly
  two expected `sorry` warnings, for the derived lemma and final theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0038.lean` exited 0 with
  exactly those same two warnings.
