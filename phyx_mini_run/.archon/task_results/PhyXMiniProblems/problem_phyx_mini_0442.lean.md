# Autoformalization result: `problem_phyx_mini_0442.lean`

Status: complete. The target now imports both Mathlib and the installed Physlib
unit infrastructure, directly resolving the iteration-001 review reason:
`physics target does not import Mathlib`. It compiles in the project Lake
environment with only the two expected `sorry` warnings.

The requested `.archon/AGENTS.md` does not exist at the stated project path. I
used the supplied agent instructions and the complete project-local
`.archon/prover-modes/physics-formalize.md` role document. The chapter is marked
`% archon:physics`, and the assigned Lean file contains no `/- USER: ... -/`
comments.

## Assumption/target split

### Governing laws

- `GraphAsymptoteRepresentsFocalDistance` states the paraxial spherical-mirror
  graph law that the vertical asymptote in an `i`-versus-`p` graph is at
  `p = f`.
- `SatisfiesGaussianSphericalMirrorEquation` states
  `f * (p + i) = p * i`, the denominator-free form of
  `1/f = 1/p + 1/i`, for every nonsingular object distance and every unit
  choice. It is general and contains no value specific to `p = 70 cm`.
- `HasPhysicalMirrorDistances` records positivity conditions selecting the
  physical concave-mirror branch and excluding nonphysical scales.

### Previous-part results

- None. The source report has an empty `previous_parts` list.
- `focalLengthInCentimeters_eq_twenty` is a newly declared derived lemma, not
  an assumed previous-part result. It derives `f = 20 cm` from the scale and
  asymptote hypotheses.

### Figure/data readouts and calibrations

- Problem-text data: the object initially has `p = 0`, moves `70 cm` along the
  horizontal principal axis, and the intended graph has scale mark
  `p_s = 40 cm`.
- Caption-level intended graph data: horizontal `p` and vertical `i` axes,
  centimeter units, visible origin and `p_s` labels, and a rectangular grid.
- Conditional intended-graph calibration: the vertical asymptote bisects the
  `p_s` scale. This is made explicit in
  `MatchesProblemAndIntendedGraph.asymptote_bisects_horizontal_scale`; it is
  the upstream calibration needed to recover the recorded answer, not a value
  of the requested image distance.
- Primary-raster audit: `442.png` actually depicts two belt/pulley assemblies
  labeled A and B and a lamp-like symbol. It does not depict the mirror graph.
  No mirror geometry or numeric datum is inferred from that raster.
- Display metadata: choices A--D record `22`, `24`, `26`, and `28` centimeters.
  Merely storing this table does not select a choice.

### Current target conclusions

- `focalLengthInCentimeters_eq_twenty` concludes the useful intermediate
  `lengthInCentimeters setup.focalLength = 20`.
- `problem_phyx_mini_0442` concludes that the image-distance readout at the
  independently stored requested object distance is exactly `28 cm` and that
  this physical image distance matches displayed choice D.

## Goal-faithfulness audit

The requested image distance is stored independently as
`setup.graph.imageDistanceAt setup.requestedObjectDistance`. No premise field,
law predicate, helper definition, or answer-table definition assigns its value
at `p = 70 cm`. In particular,
`MatchesProblemAndIntendedGraph` fixes the initial position, displacement,
requested object position, graph scale, and upstream asymptote location, but it
never constrains `imageDistanceAt` at the requested position.

The half-scale asymptote premise determines only the focal calibration when
combined with the generic `p = f` asymptote law. The requested `i = 28 cm`
still requires the independent displacement relation and the general Gaussian
mirror equation. `AnswerChoice.imageDistanceInCentimeters` records all four
printed candidates; unfolding it cannot prove the physical equality. Choice D
and the requested numeric image distance occur only in the main theorem's
conclusion.

## Declarations created and blueprint correspondence

- Dimension/readout layer: `OpticalLength`, `centimeterUnitChoices`, and
  `lengthInCentimeters`.
- Mirror/graph vocabulary: `SphericalMirrorKind`,
  `PrincipalAxisOrientation`, `GraphAxis`, `DistanceGraphQuantity`,
  `MirrorDistanceGraph`, and `SphericalMirrorExperiment`.
- Premise interfaces: `MatchesProblemAndIntendedGraph`,
  `HasPhysicalMirrorDistances`, `GraphAsymptoteRepresentsFocalDistance`, and
  `SatisfiesGaussianSphericalMirrorEquation`.
- Answer layer: `AnswerChoice`,
  `AnswerChoice.imageDistanceInCentimeters`, and `MatchesAnswerChoice`.
- Derived helper: `focalLengthInCentimeters_eq_twenty`.
- Target theorem: `problem_phyx_mini_0442`, corresponding to blueprint label
  `thm:physics:phyx_mini_0442:target`.

The helper declarations are public because they occur in, or document the
typed physical interface of, the target theorem. The blueprint currently has
only the target label; a later blueprint synchronization pass can add entries
for public helpers if desired.

## LeanExplore queries and candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query
  `dimensionful physical length quantity evaluated in chosen units centimeters`
  found and motivated the exact candidates `Dimensionful` (ID 394284) and
  `LengthUnit.centimeters` (ID 393160), as well as `UnitChoices.dimScale`.
- Likely-name query `Dimensionful UnitChoices LengthUnit.centimeters` found
  `UnitChoices` (ID 394255), `Dimension.L𝓭` (ID 394324),
  `LengthUnit.centimeters`, and the function coercion for `Dimensionful`.
- Likely-name query `WithDim UnitChoices.SI` found `UnitChoices.SI`
  (ID 394270). LeanExplore did not return `WithDim` for this query, so installed
  project LSP local search was used to confirm `WithDim` in
  `Physlib.Units.WithDim.Basic` before retaining it.
- Natural-language query
  `Gaussian spherical mirror equation focal length object distance image distance`
  returned only near misses such as Euclidean sphere-power results and
  probability Gaussian declarations. No compatible optics law was found.

Source and module information was fetched for every LeanExplore candidate used:

- `Dimensionful`: subtype of unit-choice functions satisfying a dimension law,
  module `Physlib.Units.Basic`.
- `UnitChoices`: structure containing length, time, mass, charge, and
  temperature units, module `Physlib.Units.Basic`.
- `UnitChoices.SI`: coherent SI choice, module `Physlib.Units.Basic`.
- `Dimension.L𝓭`: physical length dimension, module
  `Physlib.Units.Dimension`.
- `LengthUnit.centimeters`: `10⁻²` metre length unit, module
  `Physlib.SpaceAndTime.Space.LengthUnit`.

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `UnitChoices`, `UnitChoices.SI`,
  `Dimension.L𝓭`, `LengthUnit`, and `LengthUnit.centimeters` from Physlib.
- Mathlib supplies `ℝ`, arithmetic/order support, finite inductive derivations,
  and the actual Lake/Mathlib compilation environment required by the review
  gate.

Lean LSP local search independently confirmed `WithDim`, `Dimensionful`, and
`UnitChoices` in the installed PhysLean checkout. LeanExplore and successful
compilation confirmed the remaining qualified names.

## Local abstractions introduced

- `OpticalLength := Dimensionful (WithDim L𝓭 ℝ)` is a genuine
  unit-independent physical length, not a transparent scalar alias. Real
  values appear only through the explicitly named centimeter projection.
- The mirror kind, principal-axis orientation, graph axes, and plotted physical
  quantities are distinct categorical types so figure semantics are not
  collapsed into strings or scalars.
- `MirrorDistanceGraph` preserves a physical scale, an asymptote position, and
  a physical image-distance response rather than replacing the graph with the
  final number.
- The local asymptote and Gaussian-equation predicates preserve the two
  governing optical laws directly. They were necessary because no compatible
  Physlib spherical-mirror API was found.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration for the Gaussian spherical-mirror equation or
  a spherical-mirror image-distance graph was found. The faithful typed local
  abstractions above fill that API gap.
- The supplied primary image is unrelated to the problem, and neither it nor
  the auxiliary caption visibly establishes that the intended graph's
  asymptote is at `p_s / 2`. The numeric D result is therefore stated
  conditionally on that explicit intended-graph calibration. The source should
  be redrafted with the correct graph, or explicitly state the asymptote
  location, before treating the calibration as observed evidence.
- The advertised `archon` executable is not available on `PATH`, so the DAG
  node and ancestor queries could not run. The chapter itself exposes no
  previous theorem dependencies.
- `.archon/AGENTS.md` is absent, as noted above.
- The blueprint theorem was not marked `\leanok` because this task's explicit
  write permissions prohibit blueprint edits. A coordinating agent with
  blueprint write authority should add the marker after accepting this result.

## Verification

- Lean LSP diagnostics: success, with only the expected two
  `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0442.lean`: exit code 0,
  with only those same expected warnings.
