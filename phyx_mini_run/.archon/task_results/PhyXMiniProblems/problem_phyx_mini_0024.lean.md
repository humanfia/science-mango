# Autoformalization result: `problem_phyx_mini_0024.lean`

## Gate disposition

The iteration-2 review reason was evidence-only: no genuine post-formalization
task result existed for the revised Lean model.  I re-read the revised Lean
file, source report, primary image, physics blueprint, and gate reason, then
reran the searches and checks recorded below.  The semantic audit found no
defect, so the public declaration names and physical statement were preserved
as required by the final retry protocol.

## Assumption/target split

### Governing laws

- `SpecularReflectionAt` states the general specular law for two consecutive
  nondegenerate ray legs: the outgoing unit tangent vector equals Mathlib's
  `Submodule.reflection` of the incoming unit tangent vector in the mirror's
  tangent subspace.
- `hReflectRight`, `hReflectTop`, and `hReflectLeft` apply that law at the
  right, top, and left mirrors respectively.  No reflection is imposed at the
  aperture, where the ray enters and exits.

### Previous-part results

- None.  The source report has `previous_parts: []`, and this target has no
  mathematical ancestor declaration supplying a previous-part result.

### Figure/data readouts

- `sideLength : ℝ` and `hSideLength : 0 < sideLength` give the square's side
  length as a positive coordinate readout in one fixed length unit.
- `OpticalPoint := Space 2` uses Physlib's two-dimensional flat physical space,
  whose documentation explicitly carries an arbitrary fixed length unit and
  arbitrary origin.  `OpticalVector := EuclideanSpace ℝ (Fin 2)` is the
  translation-vector model used by Physlib's affine `Space` torsor.
- `hAperture` places the aperture at `(sideLength / 2, 0)`, the midpoint of the
  bottom mirror shown in the primary image.
- `ThreeMirrorRayRoute` names the aperture and the successive `rightHit`,
  `topHit`, and `leftHit` contact points.  `hRight`, `hTop`, and `hLeft` put
  those contacts in the relative interiors of the intended mirror sides and
  exclude corner ambiguity.
- `hLeg₀` through `hLeg₃` say that each open segment between consecutive
  contacts lies strictly inside the square.  These readouts exclude an
  unlabelled boundary collision between the three prescribed reflections.
- `inwardNormalAtAperture = !₂[0, 1]` is the upward dashed normal in the image.
  `entryAngle` is the undirected angle, in radians, from this normal to the
  initial in-enclosure ray direction.

### Current target conclusions

- `entryAngle_eq_pi_div_four` concludes
  `entryAngle route = Real.pi / 4`, i.e. `45°`, recorded answer choice C.

## Goal-faithfulness audit

The value `Real.pi / 4` occurs only in the conclusion of the target theorem
(apart from explanatory comments); it is absent from every hypothesis,
structure field, law predicate, and helper definition.  `ThreeMirrorRayRoute`
contains only four physical contact points.  The side-contact and open-segment
predicates encode geometry and collision order only.  `SpecularReflectionAt`
is the general reflection law and contains no numerical angle.  Finally,
`entryAngle` computes Mathlib's genuine inner-product angle from a normalized
affine displacement and the aperture normal; it is not defined to be the
desired answer.  Thus no current conclusion is smuggled into the premises or
made true by unfolding.

## Source/law/answer audit

- **Source:** the primary image shows a square mirrored enclosure, a centered
  bottom opening, a vertical inward normal labelled with `θ`, and the ray path.
  The problem text supplies the decisive route condition: one reflection from
  each of the other three mirrors followed by exit through the same opening.
  No numerical side length is supplied or needed.
- **Law:** the three reflection hypotheses implement equality of incidence and
  reflection directions through reflection in the relevant tangent subspace;
  open interior legs formalize the word “once” by excluding intermediate hits.
- **Answer:** the target is the source-recorded `45°`/choice-C answer, expressed
  as the exact radian value `Real.pi / 4`.  The recorded answer is used only to
  select the conclusion, never as evidence or a premise.

## Declarations and blueprint labels

- `OpticalPoint` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-opticalpoint`.
- `OpticalVector` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-opticalvector`.
- `horizontalMirrorTangent` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-horizontalmirrortangent`.
- `verticalMirrorTangent` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-verticalmirrortangent`.
- `unitDirection` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-unitdirection`.
- `SpecularReflectionAt` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-specularreflectionat`.
- `InOpenSquare` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-inopensquare`.
- `OpenSegmentInside` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-opensegmentinside`.
- `OnRightMirror` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-onrightmirror`.
- `OnTopMirror` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-ontopmirror`.
- `OnLeftMirror` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-onleftmirror`.
- `bottomCenterAperture` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-bottomcenteraperture`.
- `inwardNormalAtAperture` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-inwardnormalataperture`.
- `ThreeMirrorRayRoute` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-threemirrorrayroute`.
- `entryAngle` —
  `def:physics:phyx-mini-0024:phyxminiproblems-problemphyxmini0024-entryangle`.
- `entryAngle_eq_pi_div_four` —
  `thm:physics:phyx_mini_0024:target`.

## LeanExplore queries and candidates actually used

All selecting searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query
  `specular reflection of a vector across a plane mirror tangent subspace` and
  exact-name query `Submodule.reflection` selected `Submodule.reflection`
  (id `134311`).  Its source and module were fetched.  The source for
  `Submodule.reflection_apply` (id `134312`) was also fetched to confirm the
  action `2 • projection - vector`.  The affine-point candidate
  `EuclideanGeometry.reflection` was not selected because this law acts on ray
  tangent vectors at an already named contact point.
- Natural-language query
  `angle between two vectors in a real inner product space` and exact-name
  query `InnerProductGeometry.angle` selected
  `InnerProductGeometry.angle` (id `228174`).  Its source confirms the genuine
  `Real.arccos`-of-normalized-inner-product definition.
- Natural-language query
  `two dimensional physical Euclidean space Space` and exact-name query
  `Space` selected Physlib's `Space` (id `392723`) for points and Mathlib's
  `EuclideanSpace` (id `133893`) for tangent vectors.  Source, module, and
  docstring were fetched for both.
- Natural-language query
  `unit travel direction of a ray in Euclidean space` and exact-name query
  `Space.Direction` inspected `Space.Direction` (id `393250`) and
  `Space.toDirection` (id `393251`).  They were not used: their `unit` field is
  a `Space d` value relative to a chosen origin, whereas this ray direction is
  canonically the affine translation vector `finish -ᵥ start`.  The current
  normalization retains Physlib's intended point/vector distinction and is
  directly accepted by Mathlib's submodule reflection.

## Physlib/Mathlib names grounded

- Physlib: `Space` from `Physlib.SpaceAndTime.Space.Basic`, together with its
  `NormedAddTorsor (EuclideanSpace ℝ (Fin d)) (Space d)` model and affine
  subtraction/addition operations.
- Mathlib: `EuclideanSpace` from
  `Mathlib.Analysis.InnerProductSpace.PiL2`, `Submodule.reflection` from
  `Mathlib.Analysis.InnerProductSpace.Projection.Reflection`, and
  `InnerProductGeometry.angle` and `Real.pi` from the Euclidean-angle API.
- Language-server hover checks independently confirmed the signatures and
  imported modules for `Space`, `EuclideanSpace`, `Submodule.reflection`, and
  `InnerProductGeometry.angle` in the actual project environment.

## Local abstractions introduced

- `horizontalMirrorTangent` and `verticalMirrorTangent` are concrete coordinate
  submodules representing the two mirror orientations.  They supply exactly
  the tangent planes required by the grounded reflection operation.
- `unitDirection` normalizes an affine displacement between physical points.
  This avoids treating the ray itself as a scalar or choosing an origin for a
  point in `Space 2`.
- `SpecularReflectionAt` is a thin physical predicate over Mathlib's reflection
  and also records nondegenerate incoming and outgoing legs.
- `ThreeMirrorRayRoute`, the three side-contact predicates, `InOpenSquare`, and
  `OpenSegmentInside` are the smallest local objects needed to retain the
  labelled route, square geometry, and “once each” collision semantics that no
  dedicated library declaration provides.

## Grounding gaps and redraft requests

- LeanExplore returned no dedicated Mathlib/Physlib geometric-optics ray,
  aperture, square-mirror route, or multi-bounce specular-path API.  The local
  route and collision predicates therefore remain necessary, grounded on
  Physlib affine space and Mathlib inner-product geometry.
- `.archon/AGENTS.md` is absent in this checkout.  The available
  `.archon/prover-modes/physics-formalize.md` and `PROGRESS.md` supplied the
  role and retry protocol.  The Lean file contains no `/- USER: ... -/` hint.
- The `archon` executable is not on `PATH`, so optional DAG queries could not
  run.  The blueprint declaration topology and source report were available
  directly, and the latter confirms there are no previous parts.
- The chapter already exists and contains `% archon:physics`.  It was not
  edited to add `\leanok` because this task's explicit write permissions allow
  changes only to the assigned Lean file and task-result file.  The blueprint
  owner should add that marker after accepting this formalization.
- No Lean statement redraft is requested.

## Verification

- `archon-lean-lsp` diagnostics on the assigned file reported exactly one
  expected warning: `entryAngle_eq_pi_div_four` uses `sorry`.  It reported no
  errors or failed dependencies.
- Final shell compilation with
  `lake env lean PhyXMiniProblems/problem_phyx_mini_0024.lean` exited
  successfully with the same single expected `sorry` warning.
