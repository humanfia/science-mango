# Autoformalization result: `problem_phyx_mini_0234.lean`

The final-review gate reason was evidence-only: it said that no genuine
post-formalization result documented the revised Lean model.  The source,
primary image, blueprint, declarations, and hypotheses were therefore audited
again.  No semantic defect requiring another Lean redraft was found, so the
existing exact-sine/linearized-surrogate model was preserved.

## Assumption/target split

### Governing laws

- `SatisfiesBalloonPendulumLaws` states the light-envelope inertial-mass law,
  equality of helium and displaced-air volumes, Archimedes' buoyant-force law,
  helium weight, net upward force, the taut-string constraint, and the exact
  nonlinear tangential law `m L theta'' = -F_net sin theta`.
- The same exact-law structure identifies the released finite-amplitude period
  with `motionPeriodAtAmplitude |theta_release|` and states that the positive-
  amplitude family tends to the independent quantity
  `smallAmplitudeLimitPeriod` as amplitude tends to zero.
- `sine_sub_id_isLittleO_at_zero` is a proved-later analytic declaration whose
  conclusion is `sin theta - theta = o(theta)` at zero.  It is a theorem, not a
  premise field of the physical setup.
- `SatisfiesFirstOrderSmallOscillationModel` governs the separately named
  linearized acceleration.  It contains the linearized tangential Newton law,
  the harmonic-acceleration law, an exact residual identity connecting the
  nonlinear and linearized accelerations through `sin theta - theta`, and the
  generic phase relation `T_limit * omega_small = 2*pi`.

### Previous-part results

- None.  The source report has `previous_parts: []`.

### Figure/data readouts

- `MatchesVerbalBalloonScenario` records helium fill, a ground anchor, the
  inverted balloon-above-anchor equilibrium, negligible tether/envelope mass,
  and buoyancy-only/no-drag interaction with air.
- `MatchesProblemData` records `L = 3.00 m`, helium density
  `0.179 kg/m^3`, air density `1.20 kg/m^3`, a nonzero release displacement,
  and release from rest.
- `UsesStandardGravity` separately records the conventional calibration
  `g = 9.8 m/s^2`.  This number is needed to select a numerical answer but is
  not presented as printed source data.
- `HasPhysicalBalloonParameters` states positivity/nondegeneracy, including
  positive volume, mass, force, length, period, and frequency readouts and the
  fact that air is denser than helium.
- Direct inspection of `phyx_data/test_image/234.png` confirms that the primary
  image shows two walls, two spheres, two inclined strings, one horizontal
  string, two horizontal labels `L`, and a vertical separation label `y`.
  `MatchesSuppliedFigure` retains those labels without asserting that this
  inconsistent two-wall apparatus governs the verbal ground-tethered balloon.

### Current target conclusions

- `smallOscillationAngularFrequency_sq` concludes
  `omega_small^2 = g * (rho_air - rho_He) / (L * rho_He)`.
- `balloonSmallAmplitudeLimitPeriod_formula` concludes
  `T_limit = 2*pi*sqrt (L*rho_He / (g*(rho_air-rho_He)))`.
- `balloonMotionPeriod_is_answer_D` concludes that the first-order
  small-amplitude limiting prediction rounds to `1.46 s`, the displayed value
  for answer D.

## Goal-faithfulness audit

- The exact physical acceleration retains `Real.sin`; no premise asserts the
  globally false equality `sin theta = theta`.
- `smallOscillationAngularFrequency`, `smallAmplitudeLimitPeriod`, and
  `motionPeriodAtAmplitude` are independent dimensionful fields.  None is
  defined by the density formula, the closed-form period, or `1.46`.
- No scenario, data, positivity, exact-law, or linearized-law premise states
  the frequency formula, period formula, rounding conclusion, or correctness
  of answer D.  The generic `T_limit * omega_small = 2*pi` law alone does not
  determine a numerical period.
- The amplitude-limit law supplies the physical meaning of the limiting
  period but not its value.  The finite-amplitude `motionPeriod` is not equated
  to the first-order formula.  Thus the qualitative word “slightly” is modeled
  by a local little-o/limit contract rather than by an unsupported exact
  finite-amplitude equality.
- `RoundsToNearestHundredth` is the generic strict error test
  `|value - rounded| < 1/200`; it does not unfold to make D true.  All four
  printed choices are retained by `answerChoiceInSeconds`.
- No target is `True`, a reflexive equality, or a conclusion hidden in a local
  definition or premise structure.

## Declarations and blueprint labels

- Main target:
  `PhyXMiniProblems.ProblemPhyXMini0234.balloonMotionPeriod_is_answer_D` ↔
  `thm:physics:phyx_mini_0234:target`.
- Analytic helper:
  `sine_sub_id_isLittleO_at_zero` ↔
  `thm:physics:phyx-mini-0234:phyxminiproblems-problemphyxmini0234-sine-sub-id-islittleo-at-zero`.
- Derived frequency:
  `smallOscillationAngularFrequency_sq` ↔
  `lem:physics:phyx-mini-0234:phyxminiproblems-problemphyxmini0234-smalloscillationangularfrequency-sq`.
- Derived limiting period:
  `balloonSmallAmplitudeLimitPeriod_formula` ↔
  `lem:physics:phyx-mini-0234:phyxminiproblems-problemphyxmini0234-balloonsmallamplitudelimitperiod-formula`.
- Physical boundaries `BalloonPendulumSetup`, `MatchesVerbalBalloonScenario`,
  `MatchesSuppliedFigure`, `MatchesProblemData`, `UsesStandardGravity`,
  `HasPhysicalBalloonParameters`, `SatisfiesBalloonPendulumLaws`, and
  `SatisfiesFirstOrderSmallOscillationModel` correspond to the homonymous
  `def:physics:phyx-mini-0234:phyxminiproblems-problemphyxmini0234-*` entries in
  the chapter topology.
- The dimension aliases, SI projections, figure enumerations/readout, and
  answer declarations likewise have one-for-one `\lean{...}` entries in the
  chapter topology.  The target and all three supporting theorem/lemma bodies
  remain `by sorry`, as required for the autoformalize stage.
- These environments are ready for `\leanok`.  The blueprint was not edited
  because this prover's explicit write permissions restrict writes to the
  assigned Lean file and this result file; the project role instructions also
  reserve marker synchronization for the loop.

## LeanExplore queries/candidates actually used

Every search in this audit passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `small-angle sine residual is little-o of angle at
  zero` found `Asymptotics.IsLittleO`, `HasDerivAt.isLittleO`, and related
  derivative/little-o declarations.
- Likely-name queries `Asymptotics.IsLittleO Real.hasDerivAt_sin`,
  `Real.hasDerivAt_sin`, and `HasDerivAt.isLittleO` confirmed the exact names.
  Source/module retrieval confirmed:
  `Asymptotics.IsLittleO` in `Mathlib.Analysis.Asymptotics.Defs`,
  `HasDerivAt.isLittleO` in `Mathlib.Analysis.Calculus.Deriv.Basic`, and
  `Real.hasDerivAt_sin (x) : HasDerivAt Real.sin (Real.cos x) x` in
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv`.
- Natural-language query `dimensionful physical quantity coherent SI units
  length mass density force` and likely-name queries `Dimensionful WithDim
  UnitChoices.SI` and `WithDim` found the dimensional API used by the file.
  Source/module retrieval confirmed `Dimensionful` and `UnitChoices.SI` in
  `Physlib.Units.Basic` and `WithDim` in
  `Physlib.Units.WithDim.Basic`.
- Query `Filter.Tendsto nhdsWithin Set.Ioi` confirmed the one-sided-limit API
  used for positive amplitudes; query `Real.sqrt Real.pi` confirmed the square-
  root/period vocabulary used in the conclusion.
- Query `Archimedes buoyant force equals fluid density times displaced volume
  times gravitational acceleration` returned dimensional Newton-law examples,
  `FluidDynamics.FluidState`, and `FluidDynamics.MassDensity`, but no buoyancy
  law having the required displaced-volume signature.
- Query `ClassicalMechanics.HarmonicOscillator.period angular frequency` found
  `ClassicalMechanics.HarmonicOscillator.period` and `period_eq`.  They describe
  a scalar spring oscillator and do not encode this dimensionful buoyant
  rotational model, so they were treated as near-misses rather than imported.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `Dimension.M𝓭`, and `UnitChoices.SI`.
- Mathlib: `Asymptotics.IsLittleO`, `HasDerivAt.isLittleO`,
  `Real.hasDerivAt_sin`, `Filter.Tendsto`, `nhds`, `nhdsWithin`, `Set.Ioi`,
  `Real.sin`, `Real.sqrt`, and `Real.pi`.
- Near-matches checked but not used as replacements:
  `FluidDynamics.FluidState`, `FluidDynamics.MassDensity`, and
  `ClassicalMechanics.HarmonicOscillator.period`.

## Local abstractions introduced

- The quantity aliases use Physlib's
  `Dimensionful (WithDim dimension scalar)` rather than transparent scalar
  aliases.  Length, time, volume, mass, density, acceleration, force, angular
  frequency, angular velocity, and angular acceleration retain distinct
  dimensions; only explicit SI readouts are real numbers.
- `BalloonPendulumSetup` keeps the verbal apparatus, dynamical state, exact and
  linearized accelerations, finite-amplitude period family, limiting period,
  and supplied-figure readout distinct.
- `SatisfiesBalloonPendulumLaws` is the local interface for Archimedes'
  principle and the nonlinear inverted-pendulum dynamics because no matching
  library law was found.
- `SatisfiesFirstOrderSmallOscillationModel` is the smallest separate interface
  that records the surrogate harmonic model and its exact residual without
  smuggling in the requested density formula or answer.

## Grounding gaps and redraft requests

- No dedicated Physlib declaration was found for Archimedes' buoyant force or
  a helium-balloon inverted pendulum; the dimension-preserving local laws are
  therefore necessary.
- The supplied primary image is not the verbal ground-tethered apparatus.  A
  source redraft should provide the intended image or state explicitly that
  the two-wall/two-sphere image belongs to another problem.
- The numerical choice needs an unstated terrestrial `g`; the Lean model makes
  this extra calibration visible through `UsesStandardGravity`.
- `.archon/AGENTS.md` is absent at the path named in the assignment.  The
  injected prover-role instructions were followed, and the archived same-
  project role file confirms that provers must not edit blueprint chapters.
- The assigned Lean file contains no `/- USER: ... -/` comment.
- `archon` is not installed on `PATH` in this checkout, so the optional DAG
  queries could not run (`command not found`).

## Verification

- `archon-lean-lsp` diagnostics succeeded with no errors and exactly four
  expected `declaration uses sorry` warnings, at the analytic helper, two
  derived lemmas, and main theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0234.lean` exited 0 with the
  same four expected warnings.
