# Prover result — iteration 011

## Status

- Closed
  `PhyXMiniProblems.ProblemPhyxMini0006.prismRefractiveIndexIsAnswerC`
  without changing its declaration header.
- Derived the hypotenuse incidence and refraction angles as `45°` and `60°`
  from the figure and geometry records, then specialized Snell's law and used
  the exact Mathlib values of `sin (π / 4)` and `sin (π / 3)`.
- Identified the prism index as `Real.sqrt (3 / 2)` via `Real.sqrt_div`.
  Rational bounds
  `153 / 125 < Real.sqrt (3 / 2) < 49 / 40` certify nearest-hundredth
  rounding to `1.22` and the strict comparison with each finite answer choice.
- No `sorry`, `admit`, new axiom, `sorryAx`, `native_decide`, or other proof
  escape remains.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0006.lean`: exit code 0.
  The only diagnostic is the harmless existing-signature linter warning that
  `hParameters` is not required by the final proof.
- `lean_verify` reports no source warnings. Its theorem dependencies are only
  the standard `propext`, `Classical.choice`, and `Quot.sound`.
- A direct source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.

## Blueprint marker readiness

- The statement and proof environments for
  `thm:physics:phyx_mini_0006:target` are ready for `\leanok`.
- The blueprint was not edited because prover write permissions reserve
  marker synchronization for the automated sync/review phase.

## Redraft needed

None. The frozen theorem faithfully formalizes the blueprint's Snell-law
calculation and uniquely selects answer C.

---

# Autoformalization result: `problem_phyx_mini_0006.lean`

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was applied. The existing physical statement was preserved because the review
gate's exact failure was missing post-formalization evidence, not a semantic
defect. The assigned file has no `/- USER: ... -/` comment.

The requested `.archon/AGENTS.md` is absent from this checkout. I used the role
instructions supplied with the task and read
`.archon/prover-modes/physics-formalize.md` as the checked-in fallback.

## Assumption/target split

### Governing laws

- `SnellsLawAt` states `n₁ sin θ₁ = n₂ sin θ₂` for a labeled interface, using
  the incident and transmitted media associated with that interface.
- `ObeysSnellsLaw.atInterface` assumes this law at both the entry face and the
  hypotenuse.
- `HasPhysicalOpticalParameters.refractiveIndexPositive` assumes positive air
  and prism indices.
- The remaining `HasPhysicalOpticalParameters` fields put incidence,
  refraction, and deviation angles on the nonnegative, nongrazing branch.
  These branch restrictions resolve the relevant `Real.Angle` representative;
  they do not determine the prism index.

### Previous-part results

- None. The source report has `previous_parts: []`, and the theorem assumes no
  prior result.

### Figure/data readouts and setup relations

- `MatchesPrismFigure` records the depicted ray segments, prism faces, dashed
  incident-direction reference, normal incidence at entry, `θ = 15°`, the
  acute prism angle `45°`, the right angle `90°`, and the ambient-air index
  readout `1`.
- `MatchesPrismRayGeometry` records the geometric consequences used by the
  informal proof: zero entry angles, straight continuation after normal entry,
  exit incidence equal to the acute `45°` prism angle, and exit refraction
  angle equal to incidence plus the `15°` downward deviation.
- The primary image was inspected directly. It places `θ` between the outgoing
  ray and the horizontal dashed continuation of the incident direction. The
  auxiliary caption's claim that this dashed line is the normal is inaccurate;
  the Lean model follows the image, source question, and chapter proof.
- `PrismRefractionDiagram` distinguishes media, interfaces, faces, ray
  segments, physical angles, nonzero ray/normal directions, and dimensionless
  refractive-index readouts.

### Current target conclusions

Only the conclusion of `prismRefractiveIndexIsAnswerC` asserts:

- `diagram.refractiveIndex .prism = Real.sqrt ((3 : ℝ) / 2)`;
- `RoundsToNearestHundredth` for the displayed value `1.22`;
- `IsNearestAnswerChoice` for choice C against all other displayed choices.

## Goal-faithfulness audit

No target conclusion occurs in `MatchesPrismFigure`,
`HasPhysicalOpticalParameters`, `MatchesPrismRayGeometry`, `SnellsLawAt`, or
`ObeysSnellsLaw`. In particular, no premise fixes the prism index, states its
rounding, or selects C. `recordedAnswerChoice := .C` is dataset metadata only
and is not a theorem premise. `RoundsToNearestHundredth` and
`IsNearestAnswerChoice` define substantive numerical predicates rather than
preselected true propositions.

The exact index must therefore follow from the independent air calibration,
figure geometry, and Snell law at the hypotenuse. Refractive indices and answer
values are reals because they are dimensionless scalar readouts; directions
use nonzero `RayVector`s, and physical angles use `Real.Angle` with explicit
branch conditions.

## Source/law/answer audit

- Source-supported readouts: normal entry, right-isosceles prism, `45°`,
  `15°`, ambient air, and the four printed answer values.
- Governing law: Snell's law is an explicit hypothesis independent of the
  requested index.
- Derived answer: `sqrt (3/2)`, nearest-hundredth `1.22`, and unique choice C
  occur only in the theorem conclusion.
- The source report, primary image, and blueprint informal proof agree on the
  modeled path and answer. No semantic redraft is requested.

## Declarations and blueprint labels

All Lean names below have namespace
`PhyXMiniProblems.ProblemPhyxMini0006`.

- `angleFromDegrees` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-anglefromdegrees`
- `DiagramPlane` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-diagramplane`
- `RaySegment` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-raysegment`
- `PrismFace` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-prismface`
- `RefractingInterface` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-refractinginterface`
- `OpticalMedium` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-opticalmedium`
- `FigureAngleLabel` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-figureanglelabel`
- `incidentMedium` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-incidentmedium`
- `transmittedMedium` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-transmittedmedium`
- `PrismRefractionDiagram` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-prismrefractiondiagram`
- `MatchesPrismFigure` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-matchesprismfigure`
- `IsPhysicalRayAngle` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-isphysicalrayangle`
- `HasPhysicalOpticalParameters` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-hasphysicalopticalparameters`
- `SnellsLawAt` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-snellslawat`
- `ObeysSnellsLaw` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-obeyssnellslaw`
- `MatchesPrismRayGeometry` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-matchesprismraygeometry`
- `AnswerChoice` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-answerchoice`
- `AnswerChoice.refractiveIndexReadout` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-answerchoice-refractiveindexreadout`
- `recordedAnswerChoice` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-recordedanswerchoice`
- `RoundsToNearestHundredth` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-roundstonearesthundredth`
- `IsNearestAnswerChoice` —
  `def:physics:phyx-mini-0006:phyxminiproblems-problemphyxmini0006-isnearestanswerchoice`
- `prismRefractiveIndexIsAnswerC` —
  `thm:physics:phyx_mini_0006:target`

## LeanExplore queries/candidates actually used

Every LeanExplore query used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `Snell's law for refraction, refractive indices, and
  incidence/refraction angles` returned angle/sine and Euclidean sine-law
  declarations, but no Snell/refraction law.
- Likely-name query `SnellsLaw refraction refractiveIndex optics` likewise
  returned no compatible optics declaration.
- Query `directed ray represented by a nonzero vector` returned `RayVector`,
  `Module.Ray.someRayVector`, `Module.Ray.someVector`, and related ray
  declarations. `RayVector` was adopted because the diagram stores named
  nonzero direction representatives.
- Query `Real.Angle sin angle modulo two pi` returned `Real.Angle`,
  `Real.Angle.sin`, and related periodic-angle lemmas. `Real.Angle` and
  `Real.Angle.sin` were adopted.
- Query `Real.sqrt square root of a real number` returned `Real.sqrt`, which is
  used for the exact dimensionless index.
- Query `Real.Angle.toReal canonical real representative of an angle` returned
  `Real.Angle.toReal_mem_Ioc`, `Real.Angle.coe_toReal`, and related API.
  LSP hover then confirmed `Real.Angle.toReal : Real.Angle → ℝ` and its
  representative interval `Ioc (-π) π`.

Source/module data were fetched for the adopted declarations:

- `RayVector` from `Mathlib.LinearAlgebra.Ray`, defined as a nonzero vector;
- `Real.Angle` and `Real.Angle.sin` from
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`;
- `Real.sqrt` from `Mathlib.Analysis.Real.Sqrt`.

## Physlib/Mathlib names grounded

- Physlib module: `Physlib.Optics.Basic`.
- Mathlib: `Real.Angle`, `Real.Angle.sin`, `Real.Angle.toReal`, `RayVector`,
  `Real.pi`, and `Real.sqrt`.

`Physlib.Optics.Basic` was inspected locally after LeanExplore. Its module
documentation says that optics is currently a placeholder, and it contains no
Snell-law, refractive-index, optical-medium, or refraction declaration. The
relevant module remains imported while the missing governing law is modeled
locally.

## Local abstractions introduced

- Finite inductive types for media, interfaces, faces, ray segments, figure
  labels, and answer choices preserve distinctions in the source.
- `PrismRefractionDiagram` is a compact interface carrying the dimensionless
  index readout, physical angles, nonzero directions, and depiction facts.
- `MatchesPrismFigure` separates raw image/data evidence from interpreted
  geometry in `MatchesPrismRayGeometry`.
- `SnellsLawAt` and `ObeysSnellsLaw` faithfully supply the unavailable
  governing optics law without assuming the requested formula.
- The rounding and nearest-choice predicates make the numerical reporting
  conclusion precise without building the answer into a hypothesis.

## Grounding gaps and redraft requests

- No compatible Snell/refraction API was found in LeanExplore or the inspected
  `Physlib.Optics.Basic` placeholder, so the local law interface is necessary.
- `archon` is not on `PATH` in this runtime, so the advertised read-only DAG
  query could not run. The source report independently establishes that there
  are no previous parts.
- The auxiliary caption should be corrected to identify the dashed line as the
  incident-direction continuation, not the hypotenuse normal.
- The blueprint was not edited with `\leanok`: the task's explicit write
  permissions prohibit blueprint edits. A plan agent with blueprint write
  permission should mark `thm:physics:phyx_mini_0006:target` after acceptance.

## Verification

- `archon-lean-lsp` diagnostics: one expected `declaration uses sorry` warning
  at the target theorem and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0006.lean`: exit code 0,
  with the same single expected `sorry` warning.
