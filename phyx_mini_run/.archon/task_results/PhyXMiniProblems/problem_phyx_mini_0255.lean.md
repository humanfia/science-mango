# Autoformalization result: `problem_phyx_mini_0255.lean`

## Assumption/target split

### Governing laws

- `SatisfiesIdealMechanicalLaws.oscillatorUsesBlock2Mass` and
  `oscillatorUsesAttachedSpring` link Physlib's scalar harmonic-oscillator
  model to the coherent SI readouts of the dimensionful block-2 mass and
  spring stiffness.
- `oscillatorPeriodMatchesObservation` links
  `ClassicalMechanics.HarmonicOscillator.period` to the measured physical
  period. Physlib supplies `omega = sqrt (k / m)` and
  `period = 2 * pi / omega`.
- `collisionMomentumConservation` is the one-dimensional momentum law for the
  two blocks during the negligible-duration collision.
- `collisionKineticEnergyConservation` is the kinetic-energy law that makes
  the collision elastic.
- `verticalFreeFallLaw` gives constant-gravity vertical fall from rest:
  `h = (1/2) g t^2`.
- `uniformHorizontalFlightLaw` gives the magnitude of the horizontal range:
  `d = |v_x| t`.
- `UsesStandardNearEarthGravity` supplies the standard SI readout
  `g = 9.80 m/s^2`; this environmental parameter is needed because the source
  does not print a separate value of `g`.

### Previous-part results

- None. The source report has an empty `previous_parts` list, and the target
  theorem does not assume the derived block-2 mass, outgoing velocity, flight
  time, exact landing distance, or answer choice.

### Figure/data readouts

- Block 1 has mass `0.200 kg` and initial signed velocity `+8.00 m/s`.
- Block 2 is initially stationary.
- The attached spring has stiffness `1208.5 N/m`.
- Block 2's SHM period is `0.140 s`.
- The vertical drop marked `h` is `4.90 m`.
- The surface is frictionless, the collision is elastic, the spring's effect
  during collision is negligible, and block 2 subsequently undergoes SHM.
- The prose statement that block 1 leaves from the opposite end is represented
  only by a negative post-collision velocity, not by its derived magnitude.
- `MatchesPrimaryFigure` records the left-to-right ordering of the drop edge,
  blocks, spring, and right wall; the lower landing point; block 1's rightward
  arrow; the spring attachment to block 2; the dashed projectile path; and the
  visible labels `k`, `h`, and `d`.

### Current target conclusions

- `landingDistance_eq_exactExpression` concludes that the independent
  physical landing-distance readout equals
  `exactLandingDistanceInMeters`, the exact expression derived from the stated
  period, elastic-collision laws, and projectile laws.
- `exactLandingDistance_matches_choice_C` concludes that the exact expression
  is within `0.05 m` of the displayed `4.0 m` value.
- `problem_phyx_mini_0255` concludes both the exact physical readout and
  `MatchesDisplayedDistance ... .C`, formalizing answer choice C.

The reported `4.0 m` is modeled as a nearest-tenth display rather than an
exact real equality. With exact Lean real arithmetic, the rounded source
values give approximately `3.9999429 m`, not exactly `4`. This avoids making
the physical assumptions inconsistent merely to force the recorded choice.

## Goal-faithfulness audit

- `ElasticCollisionSpringFallSetup.landingDistance` is an independent
  dimensionful field. It is not defined from the desired answer or from
  `exactLandingDistanceInMeters`.
- No premise contains the numerical conclusion `d = 4.0`, the exact closed
  form, `MatchesDisplayedDistance ... .C`, or a selected answer choice.
- `SatisfiesIdealMechanicalLaws` contains only general physical laws. Its
  horizontal-distance field is the general kinematic relation `d = |v_x| t`,
  not the requested numerical result.
- The post-collision sign assumption is directly stated by the source phrase
  "slides off the opposite end" and merely selects the physical, nontrivial
  branch of the one-dimensional elastic-collision equations.
- `exactLandingDistanceInMeters` names a scalar expression made from the
  stated readouts. It does not identify that expression with the setup's
  independent distance; that equality remains a lemma conclusion with a
  `by sorry` body.
- The categorical fields for a frictionless surface, elastic collision,
  negligible spring influence, and SHM preserve qualitative physical roles
  without reducing them to unrelated Boolean or scalar tautologies.

## Declarations created and blueprint correspondence

- Dimension infrastructure and types:
  `velocityDimension`, `accelerationDimension`,
  `springStiffnessDimension`, `MassQuantity`, `LengthQuantity`,
  `TimeQuantity`, `VelocityQuantity`, `AccelerationQuantity`, and
  `SpringStiffnessQuantity`.
- Coherent SI projections:
  `massInKilograms`, `lengthInMeters`, `timeInSeconds`,
  `velocityInMetersPerSecond`,
  `accelerationInMetersPerSecondSquared`, and
  `stiffnessInNewtonsPerMeter`.
- Physical/figure roles:
  `BlockLabel`, `HorizontalDirection`, `SurfaceCondition`, `CollisionKind`,
  `SpringInfluenceDuringCollision`, `PostCollisionMotion`, `FigureElement`,
  `FigureQuantityLabel`, and `CollisionSpringFigure`.
- Apparatus and premise split:
  `ElasticCollisionSpringFallSetup`, `MatchesPrimaryFigure`,
  `MatchesProblemDescription`, `UsesStandardNearEarthGravity`,
  `HasPhysicalParameters`, and `SatisfiesIdealMechanicalLaws`.
- Target/readout declarations:
  `exactLandingDistanceInMeters`, `AnswerChoice`,
  `AnswerChoice.distanceInMeters`, `recordedAnswerChoice`,
  `MatchesDisplayedDistance`, `landingDistance_eq_exactExpression`, and
  `exactLandingDistance_matches_choice_C`.
- `problem_phyx_mini_0255` corresponds to blueprint label
  `thm:physics:phyx_mini_0255:target`.

The blueprint chapter was not edited to add `\leanok`, because the task's
write-permission section explicitly permits edits only to the assigned Lean
file and this result file. The plan/orchestration stage should add the marker.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query: `physical quantity with SI dimensions and units mass
  length time velocity acceleration spring stiffness`.
  Relevant candidates: `UnitChoices.SI`, `Dimension`, and `Dimensionful`.
- Likely-name query: `Dimensionful WithDim UnitChoices.SI Dimension.M𝓭
  Dimension.L𝓭 Dimension.T𝓭`. Relevant candidates: `Dimensionful` and
  `UnitChoices.SI`; the short result list did not rank every base dimension.
- Natural-language query: `simple harmonic oscillator period spring constant
  mass`.
  Relevant candidates: `ClassicalMechanics.HarmonicOscillator`,
  `ClassicalMechanics.HarmonicOscillator.ω`, and
  `ClassicalMechanics.HarmonicOscillator.period`.
- Natural-language query: `one dimensional elastic collision momentum kinetic
  energy conservation projectile horizontal range constant gravity`. Near
  misses were the free-particle momentum and kinetic-energy conservation
  results; these are not an instantaneous two-body elastic-collision or
  constant-gravity projectile interface.
- Follow-up likely-name queries: `WithDim`, `Dimension.M𝓭`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, and
  `ClassicalMechanics.HarmonicOscillator.period`. These directly grounded the
  identifiers used after the combined query's short result list omitted some
  of them.
- Likely-name query: `Real.sqrt Real.pi`. It returned square-root lemmas rather
  than the definitions themselves; LSP hover then verified the used
  `Real.sqrt` signature and import.

Source/module/docstring details were fetched for `Dimension`, `Dimensionful`,
`WithDim`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`,
`ClassicalMechanics.HarmonicOscillator`, its Unicode angular-frequency
definition `ω`, and its `period`. LSP hover also verified
`Dimensionful`, `WithDim`, `UnitChoices.SI`,
`ClassicalMechanics.HarmonicOscillator.period`, and `Real.sqrt` in the final
file.

## Physlib/Mathlib names grounded

- `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, and `Dimension.T𝓭`
- `WithDim`
- `Dimensionful`
- `UnitChoices.SI`
- `ClassicalMechanics.HarmonicOscillator`
- `ClassicalMechanics.HarmonicOscillator.ω`
- `ClassicalMechanics.HarmonicOscillator.period`
- `Real.sqrt` and `Real.pi`

## Source/law/answer audit

- Source prose/data: all printed numerical inputs (`0.200 kg`, `8.00 m/s`,
  `1208.5 N/m`, `0.140 s`, and `4.90 m`) are transcribed as readout premises
  in `MatchesProblemDescription`; the standard near-Earth value `9.80 m/s²`
  is isolated in `UsesStandardNearEarthGravity` as an environmental modeling
  choice. The same source constants appear in the closed expression whose
  equality to the independent physical distance remains a lemma conclusion.
- Primary image: direct inspection confirms the rightward arrow on block 1,
  block ordering, block-2 spring attachment/right-wall anchor, leftward
  projectile landing, and the displayed `k`, `h`, and `d` labels captured by
  `MatchesPrimaryFigure`.
- Governing laws: the oscillator period comes from Physlib; missing library
  interfaces are stated as momentum conservation, kinetic-energy conservation,
  vertical free fall, and uniform horizontal flight—not as the requested
  numerical range.
- Recorded answer: metadata says choice C (`4.0 m`). The exact expression from
  the rounded source measurements is approximately `3.9999429 m`, so the
  formalization concludes agreement within `0.05 m` rather than the false
  exact real equality `d = 4`.

## Local abstractions introduced

- Dimension products for signed velocity, acceleration magnitude, and spring
  stiffness use Physlib's `Dimension` algebra and `Dimensionful (WithDim ...)
  ...`; they are not transparent aliases to bare reals.
- `CollisionSpringFigure` and the associated finite role types preserve the
  source image's object labels, geometry, motion arrow, spring attachment, and
  `k/h/d` annotations.
- `SatisfiesIdealMechanicalLaws` is the smallest local interface needed for
  the missing two-body collision and horizontal-projectile APIs. It states
  momentum, kinetic energy, and kinematic laws directly over named SI
  readouts.
- `MatchesDisplayedDistance` represents reporting to the nearest tenth of a
  metre, which is necessary because the source data are rounded measurements.

## Grounding gaps

- LeanExplore exposed no ready-made Physlib declaration for a one-dimensional
  two-body elastic collision with pre/post velocities.
- LeanExplore exposed no ready-made elementary horizontal-projectile law
  combining constant-gravity fall time and horizontal range.
- The `archon` executable advertised for DAG queries was not available on
  `PATH`, so no dependency-graph result could be consulted. The chapter lists
  no explicit prior Lean dependencies.
- `.archon/AGENTS.md` was absent from the supplied project directory. The
  checked-in `.archon/prover-modes/physics-formalize.md` and the full role
  instructions in the task prompt were used instead.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0255.lean` exited with
  status 0.
- Lean LSP diagnostics reported only three expected `declaration uses sorry`
  warnings and no failed dependencies.
- A trailing-whitespace scan reported no issues in the assigned Lean file or
  this result report.
