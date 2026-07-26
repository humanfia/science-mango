# Prover result: `problem_phyx_mini_0033.lean`

## Outcome

Closed all three assigned proof obligations without changing any declaration
header, hypothesis, or conclusion:

- `internalBeam_is_parallel_and_axial`: the flat-face vergence equality and
  incident zero vergence give zero in-glass vergence; paraxial Snell refraction
  with zero incidence angle and glass index `1.560` gives zero in-glass angle.
- `focusDistanceQ_eq`: after substituting the readouts and the preceding
  zero-vergence result into the spherical-interface law, the equation is
  `7/75 = 1/q`. Positivity of the physical focus distance makes `q` nonzero,
  so clearing the denominator gives `q = 75/7`.
- `problem_phyx_mini_0033`: reuses the exact-distance lemma and verifies
  arithmetically that `|75/7 - 10.7| = 1/70 ≤ 0.05`, selecting answer D.

There are no remaining `sorry` placeholders and no redraft is needed.

## Verification

- Lean LSP diagnostics: no errors or failed dependencies; only the pre-existing
  unused-hypothesis linter warning for the frozen `h_physical` argument of
  `internalBeam_is_parallel_and_axial`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0033.lean`: exit code 0,
  with the same single linter warning.
- Axiom/source verification of
  `PhyXMiniProblems.ProblemPhyXMini0033.problem_phyx_mini_0033`: no suspicious
  source patterns; only Lean's standard `propext`, `Classical.choice`, and
  `Quot.sound` axioms.

## Blueprint readiness

The environments for `internalBeam_is_parallel_and_axial`,
`focusDistanceQ_eq`, and `problem_phyx_mini_0033` are proof-closed and ready
for deterministic `\leanok` synchronization. The blueprint was not edited
because the active prover role instructions reserve blueprint marker changes
for the synchronization/review lane.

---

# Physics autoformalization result: `problem_phyx_mini_0033.lean`

Iteration 002 directly repairs the recorded `missing-mathlib-import` rejection
by importing both `Mathlib` and the Physlib unit module used by the model.

## Assumption/target split

### Governing laws

- `SatisfiesFlatFaceParaxialRefraction` states the zero-power plane-interface
  law: optical vergence is preserved at the flat face, together with paraxial
  Snell refraction `n₁ θ₁ = n₂ θ₂` for the normal-based angle readouts.
- `SatisfiesSphericalFaceParaxialRefraction` states the Gaussian spherical
  interface law `L' = L + (n₂ - n₁) / r`, with
  `L' = n_air / q` and the signed exit radius `r = -R` dictated by the
  left-to-right axis convention in the figure.
- `HasPhysicalHemisphericalConfiguration` supplies only branch and positivity
  conditions: positive radius, hemisphere thickness equal to `R`, positive
  outgoing focus distance, and positive refractive indices.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `radiusR` is the dimensionful figure label `R`; its centimeter readout is
  `6.00`.
- The dimensionless refractive indices are `n_glass = 1.560` and `n_air = 1`.
- The incident beam is parallel (`incidentVergencePerCentimeter = 0`) and
  perpendicular to the flat face (`flatFaceIncidenceAngleRadians = 0`).
- The selected approximation is explicitly `.paraxial`.
- `flatFaceToExitVertex = radiusR` records that the body is a hemisphere.
- `focusDistanceQ` is a genuine dimensionful length representing the figure's
  signed axial distance `q` from the spherical exit vertex to point `I`.

### Current target conclusions

- `internalBeam_is_parallel_and_axial`: the plane entry law derives zero
  in-glass vergence and zero in-glass axial angle.
- `focusDistanceQ_eq`: the governing laws and numerical data derive the exact
  result `q = 75/7 cm`.
- `problem_phyx_mini_0033`: the focus lies `75/7 cm` beyond the exit vertex and
  therefore agrees, to the nearest tenth centimeter, with answer choice D
  (`10.7 cm`).

## Goal-faithfulness audit

No hypothesis, setup field, law predicate, or helper definition contains the
numeric focus `75/7`, the displayed value `10.7`, or answer choice D. The
unknown `focusDistanceQ` is a setup quantity constrained only by positivity,
the generic figure role of `q`, and the paraxial spherical-interface law. The
law retains the variable radius, both variable refractive indices, the
variable incoming in-glass vergence, and the variable focus distance; it is
not a restatement of the requested numerical answer. `signedExitRadiusInCentimeters`
only fixes the standard sign convention `r = -R` from the pictured center of
curvature and does not determine `q`.

The answer-choice table is data from the multiple-choice prompt, but agreement
with `.D` occurs only in the main theorem conclusion. The figure relation
`flatFaceToExitVertex = radiusR` and the positivity of `focusDistanceQ` do not
fix its magnitude.

## Declarations and blueprint labels

- Physical/unit model: `LengthQuantity`, `lengthInCentimeters`.
- Optical labels: `OpticalMedium`, `OpticalSurfaceLabel`, `incidentMedium`,
  `transmittedMedium`, `OpticalApproximation`.
- Figure setup: `HemisphericalLensSetup`,
  `signedExitRadiusInCentimeters`,
  `HasPhysicalHemisphericalConfiguration`, `MatchesFigureReadouts`.
- Governing laws: `SatisfiesFlatFaceParaxialRefraction`,
  `SatisfiesSphericalFaceParaxialRefraction`.
- Answer model: `AnswerChoice`, `answerDistanceInCentimeters`,
  `MatchesAnswerToNearestTenth`.
- Derived declarations: `internalBeam_is_parallel_and_axial`,
  `focusDistanceQ_eq`.
- `problem_phyx_mini_0033` corresponds to
  `thm:physics:phyx_mini_0033:target`.

The helper declarations above currently have no individual blueprint labels;
they are listed here so a later topology pass can link any helpers it elects to
keep public.

All three lemma/theorem bodies are `by sorry`, as required for the
`physics-formalize` autoformalization stage.

## LeanExplore queries/candidates actually used

Every query used the package filter `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `paraxial refraction at a spherical surface
  refractive index focal distance`: returned sphere-geometry and unrelated
  focal-quotient declarations, with no optics law suitable for this problem.
- Likely-name query `sphericalSurface refraction focalLength refractiveIndex`:
  no suitable optics declaration.
- Natural-language query `Snell law refraction optics`: returned Mathlib's
  Euclidean law-of-sines declarations, not Snell's law.
- Likely-name query `Optics.Basic`: returned unrelated basic-open declarations;
  local inspection confirmed that the installed `Physlib.Optics.Basic` module
  is only a placeholder.
- Unit queries `physical quantity with dimensions length SI centimeter`,
  `Dimensionful`, `WithDim`, and `LengthUnit.centimeters` grounded the unit
  representation.
- Source/module records fetched and used:
  `Dimensionful` (`Physlib.Units.Basic`), `WithDim`
  (`Physlib.Units.WithDim.Basic`), `Dimension.L𝓭`
  (`Physlib.Units.Dimension`), `UnitChoices.SI`
  (`Physlib.Units.Basic`), and `LengthUnit.centimeters`
  (`Physlib.SpaceAndTime.Space.LengthUnit`).

## PhysLean/Mathlib names grounded

- `Dimensionful`
- `WithDim`
- `Dimension.L𝓭`
- `UnitChoices.SI`
- `LengthUnit.centimeters`

No specialized Mathlib optics declaration was used because the searches found
none compatible with the physical law in the chapter.

## Local abstractions introduced

- `OpticalMedium` and `OpticalSurfaceLabel` keep air/glass and plane/spherical
  interface roles distinct; `incidentMedium` and `transmittedMedium` preserve
  propagation direction at each interface.
- `OpticalApproximation` records that the requested model is paraxial rather
  than exact ray tracing.
- `HemisphericalLensSetup` keeps physical lengths dimensionful while storing
  only dimensionless indices/angles and explicitly named inverse-centimeter
  vergence readouts as real scalars.
- The two local refraction predicates faithfully state the plane and spherical
  governing laws missing from Physlib. They are variable physical relations,
  not aliases for the target answer.
- `AnswerChoice` and its readout table preserve all four choices and the
  rounding precision represented by the prompt.

## Grounding gaps and redraft requests

- The installed `Physlib.Optics.Basic` module is a placeholder and supplies no
  Snell-law, optical-vergence, paraxial-ray, or spherical-interface API.
  Faithful local predicates were therefore necessary.
- The requested `.archon/AGENTS.md` does not exist in this project checkout.
  The identical-SHA canonical archived role file named by the iteration plan,
  the available `.archon/prover-modes/physics-formalize.md`, and the explicit
  task instructions were followed instead.
- The prompt says `archon` is on `PATH`, but the executable was unavailable, so
  DAG queries for `thm:physics:phyx_mini_0033:target` could not be run. The
  source report independently confirms that there are no previous parts.
- The blueprint chapter is present and already contains `% archon:physics`, but
  its theorem environment has no `\lean{...}` link and its proof is only the
  generic autoformalization instruction rather than the short optical
  derivation. A plan/review topology pass should link
  `PhyXMiniProblems.ProblemPhyXMini0033.problem_phyx_mini_0033`; deterministic
  marker synchronization can then add `\leanok`. This prover did not edit the
  chapter because the task's write permissions explicitly allow edits only to
  the assigned Lean file and this result report.

## Verification

- Direct imports now include both `Mathlib` and
  `Physlib.Units.WithDim.Basic`, resolving the exact iteration-001 gate reason.
- `archon-lean-lsp` diagnostics: success; only three expected `sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0033.lean`: exit code 0;
  only the same three expected `sorry` warnings.
