# Prover result — iteration 011

## Status

- Closed `PhyXMiniProblems.ProblemPhyXMini0061.problem_phyx_mini_0061`
  without changing its declaration header.
- Repaired the reviewed elaboration failure by explicitly converting the
  affine-angle displacement vectors to their two scalar coordinates.
- The proof then takes cosine of the equal-angle law, cross-multiplies the
  nonzero vector norms, squares the resulting equality, and uses the physical
  branch inequalities `5 < y ∧ y < 15` to select the unique solution `y = 9`.
- No `sorry`, `admit`, new axiom, or other proof escape hatch remains.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0061.lean`: exit code 0,
  with no diagnostics.
- `lean_verify` for the fully qualified theorem reports only the standard
  `propext`, `Classical.choice`, and `Quot.sound` dependencies and no source
  warnings.
- Source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- The standalone generated file is not registered as a named Lake target
  (`lake build PhyXMiniProblems.problem_phyx_mini_0061` reports “unknown
  target”), so direct Lean compilation is the applicable module check.

## Blueprint marker readiness

- The statement and proof environments for
  `thm:physics:phyx_mini_0061:target` are ready for `\leanok`.
- The blueprint was not edited because prover write permissions reserve marker
  synchronization for the later sync/review phase.

## Redraft needed

None. The current theorem faithfully proves the image-derived strike depth of
`9 cm`; the source report remains
`reports/phyx_mini/problem_phyx_mini_0061.source.json`.

---

# Autoformalization result: `problem_phyx_mini_0061.lean`

## Summary

- Audited the revised Lean model against the blueprint, source report,
  final-review gate reason, and primary image. The gate failure was
  evidence-only, so the physically faithful Lean statement was preserved.
- The image fixes the mirror top at `(0, 0)` cm, A at `(-10, 5)` cm, and B at
  `(-15, 15)` cm. Specular reflection gives a strike depth of `9 cm` below the
  top, while the dataset's recorded `4.0 cm` is only the drop below A's level.
- Regenerated genuine post-formalization evidence using package-filtered
  LeanExplore searches and source/module inspection of every selected API.
- The assigned Lean file compiles with exactly the one expected `sorry`
  warning required by the `physics-formalize` autoformalization stage.

## Assumption/target split

### Governing laws

- `SatisfiesLawOfReflection setup` states the law of specular reflection as
  equality of the incident and reflected undirected angles with the horizontal
  normal at the strike point. Both angles use Mathlib's
  `EuclideanGeometry.angle`. The predicate contains no numerical strike depth.
- `FollowsSingleReflectionBranch setup` selects the physical single-bounce
  branch by requiring the strike level to lie strictly between the levels of A
  and B. This excludes the continuation branch admitted by undirected-angle
  equality without assigning the requested coordinate.

### Previous-part results

- None. The source report's `previous_parts` array is empty, and the optional
  `archon dag-query` could not run because the `archon` executable is absent
  from this runtime's `PATH`.

### Figure/data readouts

- `MatchesMirrorRayFigure.coordinateUnitIsCentimeters` fixes the coordinate
  calibration to Physlib's `LengthUnit.centimeters`.
- The primary image fixes the mirror top at `(0, 0)`, source A at `(-10, 5)`,
  and receiver B at `(-15, 15)`. Thus A is 10 cm from the mirror and 5 cm
  below its top, while B is 15 cm from the mirror and 15 cm below its top.
- The same figure predicate states that the top edge belongs to the mirror,
  every mirror point has its horizontal coordinate, the top edge is topmost,
  and the unknown strike point belongs to the mirror surface.
- `AnswerChoice.distanceCentimeters` records the printed choices A = 1.4,
  B = 5.6, C = 4.0, and D = 2.4. `recordedAnswerChoice` retains the dataset's
  label C as metadata. Neither declaration is a theorem premise.

### Current target conclusions

- `problem_phyx_mini_0061` concludes that the strike point's downward
  displacement from the mirror's actual top edge is `9 cm`.
- The dataset's recorded `4.0 cm` is deliberately not asserted as the asked
  top-edge distance. It is the derived vertical drop from A to the strike.

## Goal-faithfulness audit

No theorem premise, structure field, governing-law predicate, branch
predicate, or local definition contains the target equality or fixes the
strike depth at 9. `strikeDepthBelowTopEdgeCentimeters` is only the difference
of the strike and top-edge downward coordinate readouts. The figure predicate
assigns A, B, and the mirror top but leaves `setup.ray.mirrorStrike` free apart
from mirror membership. The branch predicate supplies only strict
inequalities.

Consequently the target still requires the later prover to combine the image
coordinates, vertical-mirror geometry, branch condition, and equal-angle law.
The printed answer table is isolated as source metadata and cannot discharge
the physical conclusion by unfolding.

## Declarations and blueprint labels

- `FigurePoint` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-figurepoint`.
- `pointFromReadouts` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-pointfromreadouts`.
- `horizontalReadout` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-horizontalreadout`.
- `downwardReadout` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-downwardreadout`.
- `VerticalMirror` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-verticalmirror`.
- `ReflectedLightRay` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-reflectedlightray`.
- `MirrorRaySetup` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-mirrorraysetup`.
- Private helper `leftNormalReferencePoint` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-leftnormalreferencepoint`.
- `MatchesMirrorRayFigure` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-matchesmirrorrayfigure`.
- `FollowsSingleReflectionBranch` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-followssinglereflectionbranch`.
- `SatisfiesLawOfReflection` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-satisfieslawofreflection`.
- `strikeDepthBelowTopEdgeCentimeters` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-strikedepthbelowtopedgecentimeters`.
- `AnswerChoice` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-answerchoice`.
- `AnswerChoice.distanceCentimeters` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-answerchoice-distancecentimeters`.
- `recordedAnswerChoice` —
  `def:physics:phyx-mini-0061:phyxminiproblems-problemphyxmini0061-recordedanswerchoice`.
- `problem_phyx_mini_0061` —
  `thm:physics:phyx_mini_0061:target`.

The chapter already exists. It was not edited because this task's final write
permissions forbid blueprint changes; the synchronization/review phase may add
the target's `\leanok` marker after checking this report and compilation.

## LeanExplore queries/candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Query `two-dimensional Euclidean space indexed by Fin 2` returned
  `finrank_euclideanSpace`, `EuclideanSpace.single`, and related Euclidean-space
  infrastructure. A follow-up likely-name query `EuclideanSpace` selected
  `EuclideanSpace` (id 133893). Its source explicitly recommends
  `EuclideanSpace 𝕜 (Fin n)` and documents the `!₂[...]` constructor notation.
- Query `EuclideanGeometry.angle angle between three affine points` selected
  `EuclideanGeometry.angle` (id 228103), described as the undirected angle
  between three points. Its fetched source confirms that the angle is at the
  second point and is computed from the two displacement vectors.
- Query `LengthUnit centimeters` selected `LengthUnit.centimeters`
  (id 393160). Its fetched source defines centimeters as `10⁻²` of a meter.
- Query `law of specular reflection equal angle light ray mirror` returned
  near-misses including `EuclideanGeometry.reflection`,
  `EuclideanGeometry.angle_pointReflection_right`, and `SameRay`, but no
  ready-made physical specular-reflection law for a light ray and mirror.

Source and module data were fetched for each declaration actually selected:

- `EuclideanSpace` — `Mathlib.Analysis.InnerProductSpace.PiL2`.
- `EuclideanGeometry.angle` —
  `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine`.
- `LengthUnit.centimeters` —
  `Physlib.SpaceAndTime.Space.LengthUnit`.

## PhysLean/Mathlib names grounded

- `EuclideanSpace ℝ (Fin 2)` is the two-dimensional coordinate plane, and
  `!₂[horizontal, downward]` constructs its coordinate points.
- `EuclideanGeometry.angle` supplies both geometric angle readouts in the
  reflection law.
- Physlib's `LengthUnit` and `LengthUnit.centimeters` preserve the dimensional
  calibration of all scalar figure coordinates.
- Standard `Set` membership represents the mirror surface.

## Local abstractions introduced

- LeanExplore exposed no dedicated Physlib plane-mirror or reflected-light-ray
  object, so `VerticalMirror`, `ReflectedLightRay`, and `MirrorRaySetup` retain
  those distinct physical roles explicitly.
- `SatisfiesLawOfReflection` is the smallest faithful local law interface: it
  equates the two actual geometric angles and does not assume any coordinate or
  requested answer.
- `MatchesMirrorRayFigure` separates source/image readouts from the governing
  law and conclusion. `FollowsSingleReflectionBranch` separately records the
  qualitative path branch.
- Coordinate values are named scalar readouts rather than aliases for basic
  physical length quantities. The setup's Physlib `LengthUnit`, fixed to
  centimeters by the figure predicate, preserves their dimensional meaning.

## Grounding gaps and redraft requests

- No library declaration matching a physical law of specular reflection for a
  mirror/light-ray setup was found; the local equal-angle predicate fills this
  gap without encoding the target answer.
- The primary source image and recorded multiple-choice answer are
  inconsistent with the wording. Reflecting B across the vertical mirror, or
  solving the equal-angle proportions, gives
  `5 + 10 / (10 + 15) * (15 - 5) = 9 cm` below the top. This is 4 cm below A,
  explaining choice C, but none of the printed choices gives the asked depth.
  The current blueprint topology documents the corrected interpretation; the
  recorded answer remains metadata only.
- The chapter pins `leftNormalReferencePoint` with an ordinary `\lean{...}`
  name even though the helper is intentionally private. Review should omit
  that implementation-detail environment or otherwise avoid requiring a
  public helper solely for topology bookkeeping.
- The requested run-local `.archon/AGENTS.md` file is absent. The applicable
  role rules were therefore taken from the injected instructions and the
  complete `.archon/prover-modes/physics-formalize.md` file.
- No `/- USER: ... -/` comment is present in the assigned Lean file.

## Verification

- `archon-lean-lsp` diagnostics: no errors and exactly one expected
  `declaration uses sorry` warning at `problem_phyx_mini_0061`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0061.lean`: exit code 0
  with exactly the same expected warning.
