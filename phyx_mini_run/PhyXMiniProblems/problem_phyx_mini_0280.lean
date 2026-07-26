import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Energy

/-!
# Maximum kinetic energy of a spring--block oscillator

This file formalizes problem `phyx_mini_0280`.  A block attached to a spring
of stiffness `200 N/m` moves on a frictionless horizontal surface with
equilibrium position `x = 0` and amplitude `0.20 m`.  The supplied velocity--
time graph is sinusoidal, has extrema `2π m/s` and `-2π m/s`, and shows one
complete cycle ending at the scale marker `t_s = 0.20 s`.

Mass, length, time, velocity, stiffness, and energy remain dimensionful
physical quantities.  Real numbers below are used only for coherent SI
readouts, graph coordinates, and displayed answer values.  PhysLean's
`ClassicalMechanics.HarmonicOscillator` supplies the one-dimensional
oscillator trajectory and its kinetic and potential energies.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0280

open Dimension

/-! ## Dimensionful physical quantities and SI readouts -/

/-- Physical mass, with dimension `M`. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- Signed one-dimensional position or displacement, with dimension `L`. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Physical duration, with dimension `T`. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- Signed one-dimensional velocity, with dimension `L T⁻¹`. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Spring stiffness, with dimension force per length, equivalently `M T⁻²`. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Mechanical energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- SI metre readout of a signed position or displacement. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- SI second readout of a physical duration. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- SI metre-per-second readout of a signed velocity component. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- SI newton-per-metre readout of a spring stiffness. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  (springConstant UnitChoices.SI).val

/-- SI joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Labels and measurements from the supplied velocity--time graph -/

/-- Physical quantity assigned to a graph axis. -/
inductive AxisQuantity where
  | velocity
  | time
  deriving DecidableEq, Repr

/-- Unit printed beside a graph axis. -/
inductive AxisUnit where
  | metersPerSecond
  | seconds
  deriving DecidableEq, Repr

/-- Qualitative shape of the plotted velocity trace. -/
inductive WaveformShape where
  | sinusoidal
  | other
  deriving DecidableEq, Repr

/-- Portion of an oscillation displayed between `0` and `t_s`. -/
inductive DisplayedCycle where
  | oneCompleteCycle
  | partialCycle
  deriving DecidableEq, Repr

/-- Meaning of the dashed vertical marker carrying the label `t_s`. -/
inductive TimeMarkerMeaning where
  | cycleEnd
  | intermediateTime
  deriving DecidableEq, Repr

/-!
The raw graph data.  The argument of `velocityTraceAtSeconds` is the scalar
time coordinate printed in seconds, while its value is a dimensionful signed
velocity.  The numerical extrema are stated separately in
`MatchesSuppliedFigure`, not built into this structure.
-/
structure VelocityTimeFigure where
  verticalAxisQuantity : AxisQuantity
  horizontalAxisQuantity : AxisQuantity
  verticalAxisUnit : AxisUnit
  horizontalAxisUnit : AxisUnit
  waveformShape : WaveformShape
  displayedCycle : DisplayedCycle
  timeMarkerMeaning : TimeMarkerMeaning
  timeScale : TimeQuantity
  velocityTraceAtSeconds : ℝ → VelocityQuantity

/-!
Primary-image evidence.  The velocity trace begins and ends at zero during
the displayed interval, reaches both labeled extrema `±2π m/s`, remains
between them, and the `t_s` marker denotes the end of one complete cycle.
-/
def MatchesSuppliedFigure (figure : VelocityTimeFigure) : Prop :=
  figure.verticalAxisQuantity = .velocity ∧
    figure.horizontalAxisQuantity = .time ∧
    figure.verticalAxisUnit = .metersPerSecond ∧
    figure.horizontalAxisUnit = .seconds ∧
    figure.waveformShape = .sinusoidal ∧
    figure.displayedCycle = .oneCompleteCycle ∧
    figure.timeMarkerMeaning = .cycleEnd ∧
    velocityInMetersPerSecond (figure.velocityTraceAtSeconds 0) = 0 ∧
    velocityInMetersPerSecond
        (figure.velocityTraceAtSeconds (timeInSeconds figure.timeScale)) = 0 ∧
    (∃ t : ℝ,
      0 < t ∧ t < timeInSeconds figure.timeScale ∧
        velocityInMetersPerSecond (figure.velocityTraceAtSeconds t) =
          2 * Real.pi) ∧
    (∃ t : ℝ,
      0 < t ∧ t < timeInSeconds figure.timeScale ∧
        velocityInMetersPerSecond (figure.velocityTraceAtSeconds t) =
          -(2 * Real.pi)) ∧
    (∀ t : ℝ,
      0 ≤ t → t ≤ timeInSeconds figure.timeScale →
        -(2 * Real.pi) ≤
            velocityInMetersPerSecond (figure.velocityTraceAtSeconds t) ∧
          velocityInMetersPerSecond (figure.velocityTraceAtSeconds t) ≤
            2 * Real.pi)

/-! ## Physical setup, problem data, and governing oscillator laws -/

/-- Contact model for the block and its support surface. -/
inductive SurfaceFriction where
  | frictionless
  | dissipative
  deriving DecidableEq, Repr

/-- Dynamical regime asserted in the problem statement. -/
inductive MotionRegime where
  | simpleHarmonic
  | other
  deriving DecidableEq, Repr

/-!
The physical spring--block system.

`oscillatorSIReadout`, `initialConditions`, and `amplitudeVectorInMeters` are
the one-dimensional SI-coordinate data used by PhysLean.  The requested
maximum kinetic energy remains an unconstrained dimensionful field here; its
meaning and numerical value are supplied separately.
-/
structure SpringBlockOscillatorSetup where
  figure : VelocityTimeFigure
  blockMass : MassQuantity
  springConstant : SpringConstantQuantity
  equilibriumPosition : LengthQuantity
  amplitude : LengthQuantity
  maximumKineticEnergy : EnergyQuantity
  surfaceFriction : SurfaceFriction
  motionRegime : MotionRegime
  oscillatorSIReadout : ClassicalMechanics.HarmonicOscillator
  initialConditions :
    ClassicalMechanics.HarmonicOscillator.InitialConditions
  amplitudeVectorInMeters : EuclideanSpace ℝ (Fin 1)

/-!
Measurements and qualitative conditions stated in the prose.  Both
`0.20 m` and `0.20 s` are represented exactly as `1/5` in SI readouts.
No mass or kinetic-energy answer is assumed.
-/
def MatchesProblemStatement (setup : SpringBlockOscillatorSetup) : Prop :=
  springConstantInNewtonsPerMeter setup.springConstant = 200 ∧
    lengthInMeters setup.equilibriumPosition = 0 ∧
    lengthInMeters setup.amplitude = 1 / 5 ∧
    timeInSeconds setup.figure.timeScale = 1 / 5 ∧
    setup.surfaceFriction = .frictionless ∧
    setup.motionRegime = .simpleHarmonic

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalParameters (setup : SpringBlockOscillatorSetup) : Prop where
  blockMassPositive : 0 < massInKilograms setup.blockMass
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant
  amplitudePositive : 0 < lengthInMeters setup.amplitude
  timeScalePositive : 0 < timeInSeconds setup.figure.timeScale

/-!
The governing simple-harmonic-oscillator model and the bridge from the graph
to the physical trajectory.

The PhysLean oscillator uses the coherent SI mass and stiffness readouts.  At
the graph's time origin the block is at the negative turning point and is at
rest, which gives the displayed initially positive sinusoidal velocity.  The
graph scale is the oscillator period.  The final field states the generic
kinetic-energy law for the graph velocity and PhysLean trajectory; it contains
no problem-specific energy value or answer label.
-/
structure SatisfiesSpringBlockOscillatorLaws
    (setup : SpringBlockOscillatorSetup) : Prop where
  oscillatorMassIsBlockMass :
    setup.oscillatorSIReadout.m = massInKilograms setup.blockMass
  oscillatorStiffnessIsSpringConstant :
    setup.oscillatorSIReadout.k =
      springConstantInNewtonsPerMeter setup.springConstant
  amplitudeCoordinateIsPhysicalAmplitude :
    setup.amplitudeVectorInMeters 0 = lengthInMeters setup.amplitude
  initialPositionIsNegativeTurningPoint :
    setup.initialConditions.x₀ = -setup.amplitudeVectorInMeters
  initialVelocityIsZero : setup.initialConditions.v₀ = 0
  graphTimeScaleIsOscillatorPeriod :
    timeInSeconds setup.figure.timeScale = setup.oscillatorSIReadout.period
  graphVelocityGivesTrajectoryKineticEnergy :
    ∀ t : ℝ,
      setup.oscillatorSIReadout.kineticEnergy
          (setup.initialConditions.trajectory setup.oscillatorSIReadout)
          (t : Time) =
        (1 / 2 : ℝ) * massInKilograms setup.blockMass *
          velocityInMetersPerSecond
              (setup.figure.velocityTraceAtSeconds t) ^ 2

/-!
The named dimensionful energy is the attained maximum of the standard
PhysLean kinetic-energy trace.  This predicate gives the word "maximum" its
mathematical meaning but does not state its value or identify an answer.
-/
def IsMaximumKineticEnergy (setup : SpringBlockOscillatorSetup) : Prop :=
  (∃ t : Time,
    energyInJoules setup.maximumKineticEnergy =
      setup.oscillatorSIReadout.kineticEnergy
        (setup.initialConditions.trajectory setup.oscillatorSIReadout) t) ∧
    ∀ t : Time,
      setup.oscillatorSIReadout.kineticEnergy
          (setup.initialConditions.trajectory setup.oscillatorSIReadout) t ≤
        energyInJoules setup.maximumKineticEnergy

/-!
For a frictionless oscillator released from a turning point, conservation of
mechanical energy makes the maximum kinetic energy equal to the spring
potential energy at the amplitude.  This is a derived physical relation, not
a field of the governing-law interface.
-/
lemma maximumKineticEnergy_eq_amplitudePotentialEnergy
    (setup : SpringBlockOscillatorSetup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesSpringBlockOscillatorLaws setup)
    (_maximum : IsMaximumKineticEnergy setup) :
    energyInJoules setup.maximumKineticEnergy =
      setup.oscillatorSIReadout.potentialEnergy
        setup.amplitudeVectorInMeters := by
  rcases _maximum with ⟨⟨tMax, hAttained⟩, hMaximal⟩
  let trajectory :=
    setup.initialConditions.trajectory setup.oscillatorSIReadout
  have hEnergy (t : Time) :
      setup.oscillatorSIReadout.energy trajectory t =
        setup.oscillatorSIReadout.potentialEnergy
          setup.amplitudeVectorInMeters := by
    rw [show
      setup.oscillatorSIReadout.energy trajectory t =
        1 / 2 *
          (setup.oscillatorSIReadout.m * ‖setup.initialConditions.v₀‖ ^ 2 +
            setup.oscillatorSIReadout.k * ‖setup.initialConditions.x₀‖ ^ 2) by
          exact congrFun
            (ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_energy
              setup.oscillatorSIReadout setup.initialConditions) t]
    rw [_laws.initialVelocityIsZero,
      _laws.initialPositionIsNegativeTurningPoint]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, zero_add, norm_neg]
    simp only [ClassicalMechanics.HarmonicOscillator.potentialEnergy,
      smul_eq_mul, real_inner_self_eq_norm_sq]
  have hPotentialNonnegative (x : EuclideanSpace ℝ (Fin 1)) :
      0 ≤ setup.oscillatorSIReadout.potentialEnergy x := by
    simp only [ClassicalMechanics.HarmonicOscillator.potentialEnergy,
      smul_eq_mul]
    exact mul_nonneg (by norm_num)
      (mul_nonneg setup.oscillatorSIReadout.k_pos.le
        real_inner_self_nonneg)
  have hMaximum_le :
      energyInJoules setup.maximumKineticEnergy ≤
        setup.oscillatorSIReadout.potentialEnergy
          setup.amplitudeVectorInMeters := by
    rw [hAttained]
    have h := hEnergy tMax
    simp only [ClassicalMechanics.HarmonicOscillator.energy] at h
    linarith [hPotentialNonnegative (trajectory tMax)]
  let crossingTime : Time :=
    ((Real.pi / (2 * setup.oscillatorSIReadout.ω) : ℝ) : Time)
  have hCrossing : trajectory crossingTime = 0 := by
    rw [show trajectory crossingTime =
        Real.cos (setup.oscillatorSIReadout.ω * crossingTime.val) •
            setup.initialConditions.x₀ +
          (Real.sin (setup.oscillatorSIReadout.ω * crossingTime.val) /
              setup.oscillatorSIReadout.ω) • setup.initialConditions.v₀ by
      exact congrFun
        (ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_eq
          setup.oscillatorSIReadout setup.initialConditions) crossingTime]
    rw [_laws.initialVelocityIsZero]
    simp only [smul_zero, add_zero]
    have hω : setup.oscillatorSIReadout.ω ≠ 0 :=
      setup.oscillatorSIReadout.ω_ne_zero
    have hAngle :
        setup.oscillatorSIReadout.ω * crossingTime.val = Real.pi / 2 := by
      dsimp [crossingTime]
      field_simp
    rw [hAngle, Real.cos_pi_div_two]
    simp
  have hPotential_le :
      setup.oscillatorSIReadout.potentialEnergy
          setup.amplitudeVectorInMeters ≤
        energyInJoules setup.maximumKineticEnergy := by
    have hAtCrossing := hEnergy crossingTime
    simp only [ClassicalMechanics.HarmonicOscillator.energy,
      hCrossing, ClassicalMechanics.HarmonicOscillator.potentialEnergy,
      inner_zero_left, smul_zero, add_zero] at hAtCrossing
    rw [ClassicalMechanics.HarmonicOscillator.potentialEnergy,
      ← hAtCrossing]
    exact hMaximal crossingTime
  exact le_antisymm hMaximum_le hPotential_le

/-! ## Displayed choices and final formalization target -/

/-- Labels printed beside the four candidate energies. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Energy in joules printed beside each answer label. -/
def AnswerChoice.energyInJoules : AnswerChoice → ℝ
  | .A => 7 / 2
  | .B => 19 / 5
  | .C => 9 / 2
  | .D => 4

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Exact agreement of the physical energy with a displayed choice. -/
def MatchesDisplayedEnergy
    (setup : SpringBlockOscillatorSetup) (choice : AnswerChoice) : Prop :=
  energyInJoules setup.maximumKineticEnergy = choice.energyInJoules

/-- The selected displayed value is strictly closest to the physical energy. -/
def IsUniqueClosestDisplayedChoice
    (setup : SpringBlockOscillatorSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |energyInJoules setup.maximumKineticEnergy - choice.energyInJoules| <
      |energyInJoules setup.maximumKineticEnergy - other.energyInJoules|

/-!
For `k = 200 N/m` and amplitude `A = 0.20 m`, conservation of energy gives
`K_max = (1/2) k A² = 4.0 J`.  Thus the physical maximum kinetic energy
agrees with recorded answer D and D is uniquely closest among the displayed
choices.

The velocity graph is retained as primary evidence and is connected to the
same oscillator trajectory, although the numerical energy can already be
computed from `k` and `A`.

This formalizes blueprint label `thm:physics:phyx_mini_0280:target`.
-/
theorem problem_phyx_mini_0280
    (setup : SpringBlockOscillatorSetup)
    (hStatement : MatchesProblemStatement setup)
    (hFigure : MatchesSuppliedFigure setup.figure)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesSpringBlockOscillatorLaws setup)
    (hMaximum : IsMaximumKineticEnergy setup) :
    energyInJoules setup.maximumKineticEnergy = 4 ∧
      MatchesDisplayedEnergy setup recordedAnswerChoice ∧
      IsUniqueClosestDisplayedChoice setup recordedAnswerChoice := by
  rcases hStatement with
    ⟨hSpringConstant, _hEquilibrium, hAmplitude, _hTimeScale,
      _hFriction, _hMotion⟩
  have hInner :
      inner ℝ setup.amplitudeVectorInMeters setup.amplitudeVectorInMeters =
        lengthInMeters setup.amplitude ^ 2 := by
    rw [PiLp.inner_apply]
    simp [← hLaws.amplitudeCoordinateIsPhysicalAmplitude]
  have hEnergy :
      energyInJoules setup.maximumKineticEnergy = 4 := by
    rw [maximumKineticEnergy_eq_amplitudePotentialEnergy
      setup hPhysical hLaws hMaximum]
    rw [ClassicalMechanics.HarmonicOscillator.potentialEnergy_eq,
      hInner, hLaws.oscillatorStiffnessIsSpringConstant,
      hSpringConstant, hAmplitude]
    norm_num
  refine ⟨hEnergy, ?_, ?_⟩
  · simpa [MatchesDisplayedEnergy, recordedAnswerChoice,
      AnswerChoice.energyInJoules] using hEnergy
  · unfold IsUniqueClosestDisplayedChoice
    intro other hOther
    rw [hEnergy]
    cases other with
    | A =>
        norm_num [recordedAnswerChoice, AnswerChoice.energyInJoules]
    | B =>
        norm_num [recordedAnswerChoice, AnswerChoice.energyInJoules]
    | C =>
        norm_num [recordedAnswerChoice, AnswerChoice.energyInJoules]
    | D =>
        exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0280
