# Autoformalization result: `problem_phyx_mini_0002.lean`

This is the post-formalization evidence report requested by Archon iteration
002.  It replaces the preflight-only evidence cited in the retry reason and
audits the declarations that are actually present in the assigned Lean file.

## Assumption/target split

### Governing laws

- `LightRay` has a nonzero unit propagation direction, so the parameter of
  `LightRay.pointAt` is a travelled SI-metre readout.
- `PlaneMirror.mem_direction_iff_inner_normal_zero` says that each ideal
  mirror is precisely the affine plane orthogonal to its unit normal.
- `IsIncidentAt` says the incoming ray reaches the marked impact point on
  Mirror 1 at a nonnegative ray parameter.
- `IsSpecularReflectionAt` uses Mathlib's
  `EuclideanGeometry.reflection` in Mirror 1's affine plane to determine the
  reflected direction; it does not state a path length.
- `StrikesAt` says that the reflected ray reaches the marked point on Mirror 2
  at a strictly positive ray parameter.
- `MeetAtRightAngle` says that the mirrors share the marked corner and their
  unit normals are orthogonal.
- `Configuration.vertical_section_dimension` and the vertical-section
  membership fields model the two-dimensional dashed plane containing the
  ray, corner, and both mirror normals. The cross-section angle at the common
  corner is recorded as a right angle.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- The physical distance from the common corner to the impact point on Mirror
  1 is `1.25 m`, represented as the dimensionful quantity `metres (5 / 4)`.
- The image, used as primary evidence as directed by the chapter, places the
  `40.0°` mark between the incident ray and the dashed normal to Mirror 1.
  `incidence_angle_readout` records that angle in radians using
  `EuclideanGeometry.angle`.
- `mirror1`, `mirror2`, `corner`, `impact`, `strike`, `incoming`, `reflected`,
  and `verticalSection` preserve the labels and geometric roles in the image.
- `AnswerChoice` and `answerMetres` preserve all four printed metre readouts:
  1.30, 3.34, 1.94, and 2.08.

### Current target conclusions

- `reflected_light_distance_is_choice_C` first concludes the exact
  dimensionful relation
  `distance = 1.25 m / sin (40°)`.
- It then concludes that the SI-metre readout differs from choice C, `1.94 m`,
  by less than `0.005 m`. This expresses rounding to the printed hundredth of
  a metre rather than asserting a false exact decimal equality.

## Goal-faithfulness audit

Neither target conclusion occurs in `Configuration`, `PlaneMirror`, any
incidence/strike/reflection predicate, or any theorem hypothesis. In
particular, no premise gives the impact-to-strike distance, the sine quotient,
a bound around `1.94`, or the correct answer label.

`physicalDistance` is the generic dimensionful Euclidean distance between any
two points; unfolding it does not establish the requested value.
`answerMetres` is only the complete printed answer table and does not select a
correct entry. Choice C is selected only in the theorem conclusion. The
`1.25 m`, `40°`, perpendicularity, and cross-section facts are source/figure
inputs, not the requested path length. Thus the theorem still requires the
specular-reflection and right-triangle derivation.

## Declarations created and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0002:target` corresponds to
  `PhyXMiniProblems.Problem0002.reflected_light_distance_is_choice_C`.
- Physical/unit declarations: `LengthQuantity`, `metres`, `siMetres`, and
  `physicalDistance`.
- Geometric/physical declarations: `Space`, `LightRay`,
  `LightRay.pointAt`, `PlaneMirror`, and `PlaneMirror.reflectDirection`.
- Governing relations: `IsIncidentAt`, `StrikesAt`,
  `IsSpecularReflectionAt`, and `MeetAtRightAngle`.
- Scenario and answer declarations: `Configuration`, `AnswerChoice`, and
  `answerMetres`.

The blueprint chapter was not edited to add `\leanok`: the task's explicit
write-permission section limits edits to the assigned Lean file and this task
result. An authorized blueprint synchronization step should add the marker.

## LeanExplore queries/candidates actually used

All searches passed `packages: ["Mathlib", "Physlib"]`.

- `law of specular reflection angle of incidence equals angle of reflection light ray mirror`
  returned `EuclideanGeometry.reflection` (id 228711) and
  `EuclideanGeometry.angle` (id 228103), the two candidates used in the
  optical geometry.
- The likely-name searches `EuclideanGeometry.reflection` and
  `EuclideanGeometry.angle` confirmed those exact declarations and exposed
  the surrounding reflection and angle APIs.
- `physical dimension length SI quantity meters` returned `Dimension`
  (id 394292), `UnitChoices.SI` (id 394270), and `Dimension.L𝓭`
  (id 394324), among other unit declarations.
- `Dimensionful WithDim toDimensionful` confirmed `Dimensionful`
  (id 394284), `WithDim` (id 394425), and
  `CarriesDimension.toDimensionful` (id 394290).
- `LightRay optics mirror specular reflection PhysLean` found no optical ray
  or specular-reflection API; its geometrically relevant hits were again
  Mathlib's affine-reflection declarations.
- `EuclideanSpace AffineSubspace reflection hyperplane` confirmed
  `EuclideanGeometry.reflection` as the compatible affine-subspace operation
  and also returned the related linear `Submodule.reflection`.

Source, module, and docstring details were fetched for the candidates retained
in the model: `EuclideanGeometry.reflection` (id 228711),
`EuclideanGeometry.angle` (228103), `CarriesDimension.toDimensionful`
(394290), `Dimensionful` (394284), `WithDim` (394425), `UnitChoices.SI`
(394270), and `Dimension.L𝓭` (394324).  In particular, the retrieved source
confirms that affine reflection is an affine isometry of a nonempty affine
subspace, that `angle p₁ p₂ p₃` has vertex `p₂`, and that the Physlib
construction represents one physical quantity coherently across unit choices.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `CarriesDimension.toDimensionful`, and `UnitChoices.SI`.
- Mathlib: `EuclideanSpace`, `AffineSubspace`,
  `EuclideanGeometry.reflection`, `EuclideanGeometry.angle`, `dist`, `inner`,
  `Module.finrank`, `Real.sin`, and `Real.pi`.

## Local abstractions introduced

- `LengthQuantity` is an abbreviation of Physlib's unit-independent,
  dimension-carrying `Dimensionful (WithDim L𝓭 ℝ)`, not an alias of `ℝ`.
- `Space` is Mathlib's genuine three-dimensional Euclidean coordinate space.
  Raw reals occur only as SI coordinate/readout values, ray parameters,
  dimensionless angle values in radians, and printed answer readouts.
- `LightRay` preserves origin, propagation direction, and unit-speed
  parametrization as distinct optical data because no library optical-ray
  type was found.
- `PlaneMirror` couples an affine reflecting surface to a unit normal and the
  law characterizing its tangent directions. `reflectDirection` delegates the
  actual reflection operation to Mathlib.
- `Configuration` keeps governing laws, figure geometry, and measured data
  explicit while leaving the requested distance unconstrained.

## Grounding gaps and redraft requests

- LeanExplore found no Physlib geometrical-optics `LightRay`, ideal mirror, or
  specular-reflection law. The local ray/mirror interfaces preserve those
  physical roles while reusing Mathlib's exact affine reflection.
- Physlib has no dedicated dimensionful-length alias analogous to some of its
  other quantity aliases. The formalization therefore composes its public
  `Dimensionful`, `WithDim`, and `Dimension.L𝓭` APIs directly.
- The prose caption says the 40° angle is "with respect to Mirror 1," while the
  image visibly draws it from the dashed surface normal. Because the chapter
  says to use the image as primary evidence and the recorded answer 1.94 m is
  obtained from the normal-relative interpretation, the Lean readout uses the
  normal. A blueprint redraft should state this unambiguously.
- The blueprint theorem contains the generic autoformalization directive but
  no informal physics proof.  A plan-agent redraft should record the intended
  derivation: reflection preserves the `40°` normal-relative angle, the
  impact-to-Mirror-2 projection is `1.25 m`, and therefore the travelled
  distance is `1.25 / sin (40°) m`, which is within `0.005 m` of `1.94 m`.
- The requested `.archon/AGENTS.md` file is absent. The available
  `.archon/prover-modes/physics-formalize.md` and the user-provided role
  instructions were followed instead.
- The advertised `archon` executable is not available on `PATH`, so the
  read-only DAG query could not be run. The chapter itself declares no prior
  theorem dependencies.

## Verification

- `archon-lean-lsp` diagnostics report success with exactly one expected
  `declaration uses sorry` warning.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0002.lean` exits with code
  0 and the same single expected warning.
- `git diff --check` reports no whitespace errors.
