# Autoformalization result: `problem_phyx_mini_0263.lean` (iteration 003)

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was used. The requested `.archon/AGENTS.md` does not exist; the injected role
instructions and the complete `.archon/prover-modes/physics-formalize.md` were
used. The file-specific `/- USER: ... -/` comment says only that the Lean file
did not exist when the original autoformalization began.

The formalization-review gate's exact reason is evidence-only: it says no
genuine post-formalization report existed for the revised Lean model. After
checking the source report, primary image, chapter, and Lean statement, no
semantic defect was found, so iteration 003 preserves the revised statement
and supplies the following fresh post-formalization evidence.

## Physical model extracted

- Quantities: component and total masses; component lengths; component and
  assembly center-of-mass distances below the pivot; central and pivot moments
  of inertia; gravitational acceleration; restoring-torque coefficient;
  signed nonlinear torque as a function of angle; finite-amplitude period;
  linearized angular frequency; and linearized period.
- Dimensional roles: mass `M`, length `L`, time `T`, angular frequency `T⁻¹`,
  acceleration `L T⁻²`, moment of inertia `M L²`, and torque/restoring
  coefficient `M L² T⁻²`. Radian angle is dimensionless.
- Figure labels: horizontal blue stick, vertical red stick, pivot `A`, the
  horizontal midpoint, the vertical top endpoint, the three outer endpoints,
  perpendicular T geometry, and downward orientation of the vertical stick.
- Source data: each stick is `1 m` long; the four displayed periods are
  `1.68`, `1.74`, `1.83`, and `1.92` seconds; the recorded label is C.
- Modeling calibrations, kept separate from literal source readouts: equal
  uniform slender sticks and terrestrial `g = 9.8 m/s²`.
- Final relation: derive the zero-amplitude period
  `T₀ = 2π √(5 L / (6 g))`, show it rounds to the displayed `1.83 s`, and show
  choice C is closest. No equality with every finite-amplitude period is
  asserted.

## Assumption/target split

### Governing laws

- Total mass is the sum of component masses, and the assembly center of mass
  obeys the mass-weighted balance law.
- The horizontal component center is at the pivot; the vertical component
  center is half a vertical-stick length below it.
- A uniform slender stick has central inertia `m L² / 12`.
- The parallel-axis law gives each component's pivot inertia, and the two
  pivot inertias add to the total pivot inertia.
- The gravitational restoring coefficient is `M g d`.
- The exact signed nonlinear torque is `-κ sin θ`.
- At equilibrium the torque readout has derivative `-κ`, and its difference
  from `-κ θ` is little-o of `θ` as `θ → 0`.
- The independent linearized frequency satisfies `ω² = κ / I`, and the
  independent linearized period satisfies `T₀ = 2π / ω`.
- Finite-amplitude period readouts tend to `T₀` along
  `nhdsWithin 0 (Set.Ioi 0)`. This is the local approximation contract.

### Previous-part results

- None. `reports/phyx_mini/problem_phyx_mini_0263.source.json` has
  `previous_parts: []`.

### Figure/data readouts and calibrations

- `MatchesPrimaryTStickFigure` records only the visible T geometry, colors,
  endpoints, pivot, and point-`A` label. Direct image inspection confirms a
  blue horizontal bar, red downward stem, black central pin, and label `A`.
- `MatchesTStickProblemData` records the two printed `1 m` lengths.
- `UsesEqualUniformSlenderStickIdealization` separately records equal masses
  and the conventional uniform-slender-rod model needed for a unique answer.
- `UsesStandardGravity` separately records `49/5 = 9.8 m/s²`, which is not
  printed in the source.
- `HasPhysicalTStickParameters` records positivity and nondegeneracy.
- The four choices and recorded C label are answer metadata only.

### Current target conclusions

- The assembly center-of-mass distance is `L/4`.
- The total pivot inertia is `5 m L² / 12`.
- The restoring coefficient is `m g L / 2`.
- The linearized period is `2π √(5 L / (6 g))`.
- Under the source lengths and standard gravity, that period matches `1.83 s`
  within the two-decimal rounding interval and C is closest among the four
  displayed choices.

## Goal-faithfulness audit

The setup stores independent physical quantities and functions. In
particular, `linearizedSmallOscillationPeriod` is not defined by the desired
closed form, and `nonlinearOscillationPeriodAtPeakAngleRadians` is not defined
to equal it. The data, figure, idealization, standard-gravity, and positivity
predicates contain neither the closed-form period nor `1.83 s`.

`SatisfiesTStickCompoundPendulumLaws` contains generic component mechanics and
local oscillator laws in terms of independent `I`, `κ`, and `ω`. It does not
contain the T-specific simplifications `L/4`, `5 m L² / 12`, `m g L / 2`, or
`5 L / (6 g)`, and it does not mention a displayed answer. The derived lemma
and target theorem must combine the component laws, use the equal-length and
equal-mass data, cancel the positive mass, select the positive square root,
and establish the numerical rounding and closest-choice inequalities.

Exact equality is used for rigid-body laws, the sinusoidal torque, and the
separately named linearized oscillator. The relation to finite-amplitude
motion is only a one-sided `Filter.Tendsto` statement, supported by derivative
and little-o contracts. Thus the current answer is not smuggled into a
hypothesis, premise structure, or unfolding definition.

## Declarations and blueprint labels

All declarations below are in namespace
`PhyXMiniProblems.ProblemPhyXMini0263`. Definition-label suffixes share the
prefix `def:physics:phyx-mini-0263:phyxminiproblems-problemphyxmini0263-`.

- Quantity types: `MassQuantity` → `massquantity`, `LengthQuantity` →
  `lengthquantity`, `TimeQuantity` → `timequantity`,
  `AngularFrequencyMagnitudeQuantity` → `angularfrequencymagnitudequantity`,
  `AccelerationMagnitudeQuantity` → `accelerationmagnitudequantity`,
  `MomentOfInertiaQuantity` → `momentofinertiaquantity`,
  `RestoringTorqueCoefficientQuantity` →
  `restoringtorquecoefficientquantity`, and `TorqueQuantity` →
  `torquequantity`.
- SI projections: `massInKilograms` → `massinkilograms`, `lengthInMeters` →
  `lengthinmeters`, `timeInSeconds` → `timeinseconds`,
  `angularFrequencyInRadiansPerSecond` →
  `angularfrequencyinradianspersecond`,
  `accelerationInMetersPerSecondSquared` →
  `accelerationinmeterspersecondsquared`,
  `momentOfInertiaInKilogramMetersSquared` →
  `momentofinertiainkilogrammeterssquared`,
  `restoringCoefficientInNewtonMeters` →
  `restoringcoefficientinnewtonmeters`, and `torqueInNewtonMeters` →
  `torqueinnewtonmeters`.
- Figure/apparatus declarations: `StickComponent` → `stickcomponent`,
  `StickMassDistribution` → `stickmassdistribution`, `FigureColor` →
  `figurecolor`, `FigureLocation` → `figurelocation`, `JointGeometry` →
  `jointgeometry`, `VerticalOrientation` → `verticalorientation`,
  `TStickFigure` → `tstickfigure`, and `TStickPendulumSetup` →
  `tstickpendulumsetup`.
- Premise predicates: `MatchesPrimaryTStickFigure` →
  `matchesprimarytstickfigure`, `MatchesTStickProblemData` →
  `matcheststickproblemdata`, `UsesEqualUniformSlenderStickIdealization` →
  `usesequaluniformslenderstickidealization`, `UsesStandardGravity` →
  `usesstandardgravity`, `HasPhysicalTStickParameters` →
  `hasphysicaltstickparameters`, and `SatisfiesTStickCompoundPendulumLaws` →
  `satisfieststickcompoundpendulumlaws`.
- Derived lemma: `tStickDerivedMechanicalParameters` corresponds to
  `lem:physics:phyx-mini-0263:phyxminiproblems-problemphyxmini0263-tstickderivedmechanicalparameters`.
- Answer metadata: `AnswerChoice` → `answerchoice`, `AnswerChoice.seconds` →
  `answerchoice-seconds`, `recordedAnswerChoice` → `recordedanswerchoice`,
  `MatchesDisplayedPeriod` → `matchesdisplayedperiod`, and
  `IsClosestDisplayedPeriod` → `isclosestdisplayedperiod`.
- Target theorem: `tStickLinearizedPeriod_matches_recordedAnswerC`
  corresponds to `thm:physics:phyx_mini_0263:target`.

The lemma and target theorem retain the `by sorry` bodies required by the
autoformalization stage.

## LeanExplore queries and candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `physical pendulum small amplitude period` returned
  `RigidBody.small_oscillations_about_equilibrium` and
  `ClassicalMechanics.HarmonicOscillator.period`.
- Natural-language query
  `uniform slender rod moment of inertia parallel axis theorem` returned
  `RigidBody.parallel_axis_theorem` and `RigidBody.inertiaTensor`, but no
  executable scalar slender-rod inertia result.
- Likely-name query `Dimensionful WithDim UnitChoices.SI physical units`
  returned `UnitChoices.SI` and `Dimensionful`; an exact `WithDim` query
  returned `WithDim`.
- Likely-name query
  `Filter.Tendsto nhdsWithin HasDerivAt Asymptotics.IsLittleO`, followed by
  exact `HasDerivAt` and `Filter.Tendsto` queries, grounded all three analytic
  predicates used by the model.

Source, module, and docstring details were fetched only for the selected
candidates: `RigidBody.small_oscillations_about_equilibrium`,
`ClassicalMechanics.HarmonicOscillator.period`,
`RigidBody.parallel_axis_theorem`, `Dimensionful`, `WithDim`,
`UnitChoices.SI`, `HasDerivAt`, `Asymptotics.IsLittleO`, and
`Filter.Tendsto`.

## Mathlib/Physlib names grounded

- `Dimensionful` (`Physlib.Units.Basic`) is a unit-choice-dependent physical
  quantity satisfying a dimension law.
- `WithDim` (`Physlib.Units.WithDim.Basic`) tags an underlying numeric type
  with a `Dimension`.
- `UnitChoices.SI` (`Physlib.Units.Basic`) selects metres, seconds, kilograms,
  coulombs, and kelvin; it is used for coherent SI projections.
- `HasDerivAt` (`Mathlib.Analysis.Calculus.Deriv.Basic`) expresses the local
  derivative of torque at equilibrium.
- `Asymptotics.IsLittleO` (`Mathlib.Analysis.Asymptotics.Defs`) expresses the
  nonlinear remainder relative to angle.
- `Filter.Tendsto` (`Mathlib.Order.Filter.Defs`), with `nhdsWithin`, `nhds`,
  and `Set.Ioi`, expresses convergence from positive peak amplitudes.
- `Real.sin`, `Real.sqrt`, and `Real.pi` express the nonlinear restoring law
  and final linearized formula.

## Local abstractions introduced

- Dimensionful specializations preserve the distinct physical roles of mass,
  length, duration, angular frequency, acceleration, inertia, restoring
  coefficient, and signed torque. They are not aliases to bare `ℝ`.
- `TStickPendulumSetup` preserves both component roles, independent mass
  distributions, centers of mass, inertias, exact torque, amplitude-dependent
  period, linearized response quantities, and the figure.
- `SatisfiesTStickCompoundPendulumLaws` states the necessary dimension-aware
  scalar readout laws. It is needed because the retrieved Physlib rigid-body
  results are `informal_lemma` documentation placeholders, while
  `ClassicalMechanics.HarmonicOscillator.period` is a scalar definition for a
  separate oscillator object rather than a dimensionful physical-pendulum
  theorem.
- Figure enums and `TStickFigure` preserve visible labels, colors, locations,
  and geometry without encoding dynamics or an answer.
- Answer-choice definitions preserve the supplied multiple-choice metadata
  while leaving matching and closest-choice claims to the theorem conclusion.

## Source/law/answer audit

- The source report and chapter agree on two `1 m` sticks, pivot `A`, the four
  displayed choices, recorded C, and the absence of previous parts.
- Primary-image inspection confirms the modeled T geometry and colors.
- For equal uniform sticks of mass `m` and length `L`, the component laws give
  `I = mL²/12 + (mL²/12 + m(L/2)²) = 5mL²/12` and
  `κ = (2m)g(L/4) = mgL/2`, hence `I/κ = 5L/(6g)`.
- With `L = 1 m` and `g = 9.8 m/s²`, an independent numerical check gives
  `T₀ ≈ 1.832214043088 s`; its difference from `1.83 s` is approximately
  `0.002214043088 s`, below the formal `0.005 s` rounding tolerance.
- The recorded answer is supported only as the zero-amplitude limit. The model
  does not globalize the small-angle approximation to arbitrary amplitude.

## Grounding gaps and redraft requests

- `RigidBody.small_oscillations_about_equilibrium` and
  `RigidBody.parallel_axis_theorem` are Physlib `informal_lemma`s and cannot be
  used as executable proof premises. No executable scalar uniform-slender-rod
  inertia theorem or nonlinear physical-pendulum zero-amplitude period theorem
  was found, so faithful local governing-law fields are retained.
- The source does not explicitly state equal masses, uniform slender density,
  an oscillation amplitude, or `g`; these conventional assumptions are
  explicitly isolated rather than misclassified as figure/source readouts. A
  future source-authorized redraft should state them and call the answer a
  small-amplitude or zero-amplitude period.
- The chapter has model descriptions and topology but no detailed informal
  derivation. A future blueprint redraft should include the component inertia,
  center-of-mass, restoring-coefficient, and limiting-period calculation.
- The advertised `archon` executable is not available on this shell's `PATH`,
  so the optional read-only DAG query could not run.
- The blueprint was not edited or marked `\\leanok` because the explicit write
  permissions prohibit editing blueprint chapters. A blueprint-authorized
  coordinator should add the marker after accepting the formalization.

## Verification

- `archon-lean-lsp` diagnostics: no errors; exactly two expected
  `declaration uses sorry` warnings at the derived lemma and target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0263.lean`: exit code 0,
  with exactly the same two expected warnings.
