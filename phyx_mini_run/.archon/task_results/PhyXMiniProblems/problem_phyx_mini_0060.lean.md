# Prover result (Archon iteration 008)

## Status

Complete. The sole proof obligation,
`PhyXMiniProblems.ProblemPhyXMini0060.problem_phyx_mini_0060`, is closed
without changing its signature.

## Proof summary

- Extracted the exact figure readouts
  `incidentAngleFromHorizontalRadians = 0` and
  `reflectedAngleFromHorizontalRadians = degrees 60` from
  `MatchesFigureReadouts`.
- Rewrote the angle-form conjunct of `ObeysSpecularReflectionLaw` to obtain
  `degrees 60 = 2 * setup.phiRadians - 0`.
- Normalized the definition of `degrees` and used real linear arithmetic to
  derive `setup.phiRadians = degrees 30`.
- Closed the choice-A conjunct by unfolding through definitional reduction:
  `MatchesAnswer setup.phiRadians .A` is the same equality.

The qualitative geometric calibration hypothesis `hAngles` is not needed
after the exact scalar figure readouts and governing angle law are supplied.

## Verification

- Lean LSP diagnostics report no errors. The sole diagnostic is the
  unused-variable linter warning for the frozen `hAngles` theorem parameter.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0060.lean` exits with
  status 0 and the same linter warning.
- The root `lake build` completes successfully with 4 jobs.
- `lean_verify` reports only Lean's standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no suspicious source patterns.
- A source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide` in the assigned Lean file.
- `git diff --check` reports no whitespace errors.

## Blueprint readiness

The theorem environment
`thm:physics:phyx_mini_0060:target` is ready for deterministic `\leanok`
synchronization. The blueprint was not edited because the explicit prover
write permissions allow changes only to the assigned Lean file and this task
result.

## Redraft needed

None. The physically corrected target (`φ = 30°`, choice A) follows from the
current premises exactly as stated.

## Role-instruction note

The requested `.archon/AGENTS.md` is absent, as `PROGRESS.md` also records.
The user-provided prover contract and `.archon/prover-modes/physics.md` were
followed.

---

# PhyXMiniProblems/problem_phyx_mini_0060.lean

## Summary

- Created the missing Lean file for the physics blueprint chapter.
- Modeled the laser rays and mirror as geometric objects in
  `EuclideanSpace ℝ (Fin 2)` rather than replacing them with scalar aliases.
- Added the source-recorded theorem target with a `by sorry` body, as required
  by the `physics-formalize` autoformalization stage.
- Verified with
  `lake env lean PhyXMiniProblems/problem_phyx_mini_0060.lean`.  The only
  diagnostic is the expected `declaration uses sorry` warning.

## Assumption/target split

### Governing laws

- `ObeysSpecularReflectionLaw` states that the outgoing ray direction is
  `EuclideanGeometry.reflection` of the incident direction in the affine
  mirror.
- Its angle-readout conjunct states the general branch relation
  `reflectedAngle = 2 * phi - incidentAngle`.  This is the specular-reflection
  law for direction angles measured from the common horizontal reference; it
  does not assign a numerical value to `phi`.

### Previous-part results

- None.  The source report has an empty `previous_parts` list.

### Figure/data readouts

- `HasGeometricAngleReadouts` connects the three scalar radian labels to
  Mathlib's `InnerProductGeometry.angle` on the unit geometric directions.
- `MatchesFigureReadouts` records that the incident ray reaches the mirror, the
  reflected ray begins at the impact point, the incident ray points along the
  named horizontal direction, its horizontal angle is zero, the outgoing beam
  is marked `60°` above horizontal, and the depicted `phi` branch is acute.
- `answerAngleRadians` records all four printed choices: A = `30°`,
  B = `90°`, C = `60°`, and D = `120°`.
- `recordedDatasetAnswer` records the supplied metadata label C.  It is not a
  theorem premise.

### Current target conclusions

- `problem_phyx_mini_0060` concludes the source-recorded claim
  `setup.phiRadians = degrees 60` and that this value matches choice C.
- Neither conclusion occurs in `HasGeometricAngleReadouts`,
  `MatchesFigureReadouts`, `ObeysSpecularReflectionLaw`, or a theorem
  hypothesis.

## Goal-faithfulness audit

The theorem preserves the supplied answer/context (`φ = 60°`, choice C) only
on the conclusion side.  The setup contains physical rays, an affine mirror,
an impact point, unit direction invariants, and separate scalar angle readouts.
No premise field, validity predicate, governing-law predicate, or local
definition assumes `φ = 60°`.

`MatchesAnswer` merely interprets a displayed multiple-choice label; it does
not establish the first conjunct of the theorem.  Likewise,
`recordedDatasetAnswer` records metadata and is not supplied as a hypothesis.

## Declarations created and blueprint alignment

- `Plane` — two-dimensional Euclidean optical plane.
- `degrees` — degree-to-radian conversion for dimensionless angle readouts.
- `LightRay` and `LightRay.pointAt` — oriented unit laser ray and its path.
- `PlaneMirror` and `PlaneMirror.reflectDirection` — affine reflecting surface,
  oriented unit tangent, and geometric reflected direction.
- `MirrorDeflectionSetup` — the physical objects and figure labels.
- `HasGeometricAngleReadouts` — calibration of labels against geometric angles.
- `MatchesFigureReadouts` — figure and numerical readouts.
- `ObeysSpecularReflectionLaw` — governing vector and angular reflection law.
- `AnswerChoice`, `answerAngleRadians`, `MatchesAnswer`, and
  `recordedDatasetAnswer` — displayed multiple-choice data.
- `problem_phyx_mini_0060` corresponds to
  `thm:physics:phyx_mini_0060:target`.

The blueprint chapter was not edited because the task's explicit write
permissions allow edits only to the assigned Lean file and this result file.
The review agent should add `\leanok` to the theorem environment after
reviewing the source inconsistency below.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `angle between two vectors in an inner product space`:
  selected `InnerProductGeometry.angle` (declaration id 228174).
- Likely-name query `InnerProductGeometry.angle`: confirmed the same
  declaration and related angle lemmas.
- Natural-language/likely-name query
  `reflection across an affine subspace EuclideanGeometry.reflection`:
  selected `EuclideanGeometry.reflection` (declaration id 228711).
- Natural-language query
  `law of specular reflection equal incidence and reflection angles`:
  found `EuclideanGeometry.reflection` as the useful geometric primitive but
  no dedicated PhysLean geometric-optics law.
- Fetched source, module, and docstring for the two selected declarations.

## PhysLean/Mathlib names grounded

- `EuclideanSpace` from Mathlib supplies the two-dimensional vector space.
- `InnerProductGeometry.angle` from
  `Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic` supplies undirected
  nonzero-vector angle readouts in radians.
- `EuclideanGeometry.reflection` from
  `Mathlib.Geometry.Euclidean.Projection` supplies affine-subspace reflection.
- `AffineSubspace`, `Real.pi`, norms, scalar multiplication, and vector
  addition/subtraction are standard Mathlib infrastructure used compatibly
  with those declarations.
- No matching PhysLean plane-mirror or specular-reflection API was found.

## Local abstractions introduced

- `LightRay` preserves a laser ray's origin, geometric direction, and unit
  normalization.
- `PlaneMirror` preserves the affine reflecting surface and an oriented unit
  tangent needed to interpret `phi`.
- `MirrorDeflectionSetup` keeps physical objects distinct from their
  dimensionless scalar angle readouts.
- `ObeysSpecularReflectionLaw` combines Mathlib's geometric reflection with the
  standard scalar direction-angle law for the acute branch shown.  This
  abstraction is needed because LeanExplore found no dedicated PhysLean
  geometric-optics interface.

## Grounding gaps and redraft requests

- The blueprint contains the `% archon:physics` marker but no informal proof
  beyond the generic autoformalization instruction.
- `.archon/AGENTS.md` was absent, so the embedded role instructions and the
  available `.archon/prover-modes/physics-formalize.md` were used.
- The `archon` executable was not available on `PATH`, so the optional DAG
  navigation commands could not be run.
- Most importantly, the source image and recorded answer conflict.  From
  `incidentAngle = 0`, `reflectedAngle = 60°`, and the governing law
  `reflectedAngle = 2 * phi - incidentAngle`, Lean checks that
  `phi = 30°`.  A read-only `lean_run_code` example proving this implication
  compiled successfully.  Therefore the recorded target `phi = 60°` / choice C
  is not provable from the faithful physical premises; the physically
  consistent choice is A.  The blueprint should be redrafted or the figure
  interpretation clarified before the physics prover stage.

## Why I stopped

Real progress: one complete physics declaration set and one target theorem stub
were introduced and compile with only the expected `sorry` warning.  The
remaining `sorry` is required by the autoformalization stage and, independently,
the supplied target needs source correction before an honest proof can exist.
