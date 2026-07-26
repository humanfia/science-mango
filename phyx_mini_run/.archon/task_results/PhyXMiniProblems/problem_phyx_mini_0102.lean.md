# Prover result — Archon iteration 014

## Status

- Closed the sole `sorry` in
  `PhyXMiniProblems/problem_phyx_mini_0102.lean`.
- The frozen theorem signature and all hypotheses were preserved.
- No `sorry`, `admit`, `axiom`, `native_decide`, or `sorryAx`-style
  mechanism remains in the assigned file.

## Proof summary

The proof rewrites the given incidence angle as
`66° = π / 6 + π / 5`.  It uses Mathlib's exact identity
`Real.cos_pi_div_five`, certified rational bounds for `√3`, `√5`, and
`sin (π / 5)`, and the addition formulas to bound the incident sine and
cosine.  Entry-face Snell's law then bounds the refracted sine; the supplied
acute-angle hypothesis and `Real.sin_sq_add_cos_sq` bound its positive cosine.
These intervals are propagated through the supplied parallel-plate
displacement relation to prove that the centimeter readout lies between
`1.615` and `1.625`, which is exactly the requested nearest-hundredth
tolerance around answer A's `1.62`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0102.lean` — exit code
  `0`, with no diagnostics.
- `lean_verify` source scan — no warnings; theorem axioms are only the
  standard imported `propext`, `Classical.choice`, and `Quot.sound`.
- Direct source scan found no proof placeholders or prohibited escape
  hatches.

## Project metadata notes

- `.archon/AGENTS.md` is absent in this checkout; the available
  `.archon/prover-modes/physics.md` was read and followed as the project-local
  role specification.
- The blueprint chapter exists, but it was not edited to add `\leanok`
  because the explicit prover write permissions restrict edits to the
  assigned Lean file and this task-results file.  Marker synchronization
  remains for the authorized blueprint/sync role.
- No redraft is needed.

---

# Post-formalization result: `phyx_mini_0102`

The existing revised Lean model was audited against the source report and the
primary image and was preserved.  Review iteration 3 reports only missing
post-formalization evidence for this target; the audit found no source,
physical-law, answer, or elaboration defect requiring a statement change.

## Assumption/target split

### Governing laws

- `SatisfiesSnellsLawAt setup face` states Snell's law at an interface as
  `n₁ sin θ₁ = n₂ sin θ₂`; `ObeysSnellsLaw.atFace` requires it at both the
  entry and exit faces.
- `SatisfiesParallelPlateGeometry.parallelFaceNormals` records that the two
  plate faces have the same normal direction.
- `incidenceAngleFromDirections` and `refractionAngleFromDirections` connect
  all four scalar angle readouts to the corresponding nonzero ray and normal
  directions.
- `internalAnglePreservedByParallelFaces` records the equality between the
  entry refraction angle and the exit incidence angle caused by parallel
  faces.
- `pointPReachedAlongInternalRay`,
  `pointQOnUnrefractedIncidentExtension`,
  `pqPerpendicularToIncidentExtension`, and `lateralDisplacementIsPQ` encode
  the construction visible in the primary image: `P` is the actual lower-face
  exit point, `Q` is on the dashed unrefracted continuation, and `PQ` is the
  perpendicular lateral displacement.
- `parallelPlateDisplacementRelation` is the general plane-parallel-plate
  geometry law
  `d = t * sin (θ_a - θ'_b) / cos θ'_b`.  It is stated for arbitrary setup
  readouts and contains no answer-choice or requested numerical value.
- `HasPhysicalOpticalParameters` supplies positivity and the acute principal
  branches needed to select the physical Snell-law solution.

### Previous-part results

- None.  The source report has `previous_parts: []`; this is a standalone
  multiple-choice problem.

### Figure/data readouts

- `MatchesProblemData` records a transparent plate, thickness `2.40 cm`,
  entry incidence angle `66.0°`, glass refractive index `1.80`, and air index
  `1` on both sides.
- `ParallelGlassPlateSetup` retains the figure quantities `t` and `d`, the
  three optical regions, two plate faces, three directed ray segments, the
  four face/side angle roles (`θ_a`, `θ'_b`, `θ_b`, `θ'_a`), and points
  `entry`, `P`, and `Q`.
- `AnswerChoice.displacementCentimeters` records the displayed choices
  `1.62`, `1.54`, `1.75`, and `1.59 cm`.  `recordedAnswerChoice := .A` is
  dataset metadata and is not a theorem premise.
- The auxiliary prose caption reverses/misplaces `P` and `Q`; the project says
  to use the image as primary evidence, and direct inspection of `102.png`
  confirms the Lean model's labels described above.

### Current target conclusion

- `lateralDisplacementIsAnswerA` concludes only that the dimensionful lateral
  displacement's centimeter readout is within `0.005 cm` of choice A's
  displayed `1.62 cm`, via
  `MatchesAnswerToNearestHundredthCentimeter setup.lateralDisplacement .A`.
- A numerical sanity check gives the entry refraction angle
  `30.499128313313°` and displacement `1.617522240141 cm`; its distance from
  `1.62 cm` is `0.002477759859 cm`, inside the stated rounding interval.

## Goal-faithfulness audit

- The requested answer does not occur in `MatchesProblemData`,
  `HasPhysicalOpticalParameters`, `SatisfiesParallelPlateGeometry`, or
  `ObeysSnellsLaw`.
- The only answer-determining numerical source data in the premises are the
  stated `2.40 cm`, `66.0°`, refractive indices `1` and `1.80`, together with
  the governing optical and geometric laws.
- The general displacement relation is a law of arbitrary parallel-plate
  configurations, not a restatement of the current numerical conclusion: it
  contains neither `1.62`, choice `.A`, nor the nearest-hundredth predicate.
- `recordedAnswerChoice` is not passed to the theorem and does not unfold into
  its conclusion.  The answer table is metadata used by the conclusion to say
  what choice `.A` displays.
- `MatchesAnswerToNearestHundredthCentimeter` defines a genuine reporting
  tolerance; it does not define the physical displacement or force the target
  relation by unfolding.
- No current target conclusion is a hypothesis, premise-structure field,
  governing-law field, or local definition.  The theorem therefore leaves the
  numerical optical calculation as the later proof obligation.

## Declarations and blueprint labels

The formalization contains the following public declarations, each pinned by
the matching environment in the chapter:

- `lateralDisplacementIsAnswerA` —
  `thm:physics:phyx_mini_0102:target`.
- `DimLength` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-dimlength`.
- `centimeterUnitChoices` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-centimeterunitchoices`.
- `valueInCentimeters` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-valueincentimeters`.
- `degreesToRadians` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-degreestoradians`.
- `DiagramPlane` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-diagramplane`.
- `RayDirection` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-raydirection`.
- `OpticalRegion` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-opticalregion`.
- `PlateFace` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-plateface`.
- `RaySegment` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-raysegment`.
- `FigurePoint` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-figurepoint`.
- `incidentRegion` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-incidentregion`.
- `transmittedRegion` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-transmittedregion`.
- `incidentSegment` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-incidentsegment`.
- `transmittedSegment` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-transmittedsegment`.
- `ParallelGlassPlateSetup` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-parallelglassplatesetup`.
- `angleBetweenDirections` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-anglebetweendirections`.
- `IsPhysicalAcuteAngle` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-isphysicalacuteangle`.
- `MatchesProblemData` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-matchesproblemdata`.
- `HasPhysicalOpticalParameters` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-hasphysicalopticalparameters`.
- `SatisfiesParallelPlateGeometry` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-satisfiesparallelplategeometry`.
- `SatisfiesSnellsLawAt` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-satisfiessnellslawat`.
- `ObeysSnellsLaw` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-obeyssnellslaw`.
- `AnswerChoice` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-answerchoice`.
- `AnswerChoice.displacementCentimeters` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-answerchoice-displacementcentimeters`.
- `recordedAnswerChoice` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-recordedanswerchoice`.
- `MatchesAnswerToNearestHundredthCentimeter` — `def:physics:phyx-mini-0102:phyxminiproblems-problemphyxmini0102-matchesanswertonearesthundredthcentimeter`.

No public declaration was added or removed during this evidence-only retry.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `dimensionful physical length centimeter unit
  readout` returned and supported `Dimensionful` (id `394284`),
  `Dimension.L𝓭` (`394324`), and `LengthUnit` (`393137`).
- Natural-language query `RayVector nonzero Euclidean vector angle between
  directions` returned and supported `RayVector` (`251775`); it also returned
  the point-based `EuclideanGeometry.angle`, which is a near miss for the
  vector-direction model.
- Natural-language query `Snell's law refraction refractive index sine
  incidence angle` returned trigonometric angle and triangle-law declarations
  (`Real.Angle.sin`, `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm`,
  and `EuclideanGeometry.law_sin`) but no Snell-law optics declaration.
- Exact-name queries `LengthUnit.centimeters`, `UnitChoices`,
  `InnerProductGeometry.angle`, `EuclideanSpace`, and `WithDim` returned the
  exact declarations used in the file.
- Source and module data were fetched for `Dimensionful`, `Dimension.L𝓭`,
  `WithDim`, `LengthUnit.centimeters`, `UnitChoices`, `RayVector`,
  `InnerProductGeometry.angle`, and `EuclideanSpace` before retaining them.

## PhysLean/Mathlib names grounded

- Physlib/PhysLean: `Dimensionful`, `Dimension.L𝓭`, `WithDim`,
  `UnitChoices`, `UnitChoices.SI`, and `LengthUnit.centimeters`.
- Mathlib: `EuclideanSpace`, `RayVector`, and
  `InnerProductGeometry.angle`.
- Core Mathlib real-analysis/vector operations used compatibly by the model:
  `Real.pi`, `Real.sin`, `Real.cos`, `Set.Ioo`, `inner`, vector subtraction,
  scalar multiplication, and norm.

## Local abstractions introduced

- `OpticalRegion`, `PlateFace`, `RaySegment`, and `FigurePoint` preserve the
  distinct physical and diagram roles instead of encoding them as bare
  scalars.
- `ParallelGlassPlateSetup` bundles dimensionful lengths, dimensionless
  refractive-index readouts, radian angle readouts, nonzero propagation
  directions, surface normals, and figure positions.  The length type is an
  abbreviation of Physlib's dimensionful infrastructure, not `ℝ`.
- `MatchesProblemData`, `HasPhysicalOpticalParameters`, and
  `SatisfiesParallelPlateGeometry` separate source readouts, physical branch
  conditions, and governing geometry.
- `SatisfiesSnellsLawAt` and `ObeysSnellsLaw` are required because the focused
  library search found no optics Snell-law API.  Their equation is the physical
  law itself, not the final numerical result.
- `AnswerChoice` and `MatchesAnswerToNearestHundredthCentimeter` preserve the
  multiple-choice reporting semantics separately from the physical model.

## Grounding gaps and redraft requests

- No Mathlib/Physlib Snell-law declaration was found; the faithful local
  interface above remains necessary.
- The `archon` executable was not on `PATH` in this runtime, so the optional
  read-only DAG queries could not run.  The source report independently states
  that there are no previous parts, and the chapter supplies the complete
  declaration topology.
- `.archon/AGENTS.md` was absent.  The available
  `.archon/prover-modes/physics-formalize.md` was read as the project-local role
  discipline.
- No physics-statement redraft is requested.  The chapter exists and is
  `% archon:physics`.  It was not edited or marked `\leanok` because the
  explicit task write permissions forbid editing blueprint chapters; marker
  synchronization must be performed by the authorized blueprint/sync role.

## Verification

- `archon-lean-lsp` diagnostics: successful elaboration, no errors, and exactly
  one expected warning (`declaration uses sorry`) at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0102.lean`: exit code `0`
  with the same single expected warning.
