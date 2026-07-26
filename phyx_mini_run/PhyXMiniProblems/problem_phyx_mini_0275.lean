import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0275

open Dimension

/-!
# Maximum kinetic energy from a force--position graph

A `0.50 kg` block attached to a spring moves on a frictionless horizontal
surface.  The equilibrium position is `x = 0`, and at the displayed initial
time the block passes through equilibrium in the positive `x` direction.

The primary image is interpreted as a graph of the signed `x`-component of
the net force: it is a straight descending segment through the origin, from
`(-0.30 m, F_s)` to `(0.30 m, -F_s)`, where `F_s = 75.0 N`.  This signed
interpretation is forced by the negative ordinate printed in the image even
though the prose calls the graphed quantity a magnitude.

Physical masses, lengths, times, velocities, force components, spring
stiffnesses, and energies retain their dimensions through Physlib.  Real
numbers occur only as coherent SI readouts and displayed answer values.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A signed one-dimensional position or positive amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time coordinate. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A signed velocity component along the oscillator's `x` axis. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A signed force component along the oscillator's `x` axis. -/
abbrev ForceComponentQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Spring stiffness, with dimension force divided by length. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Metre readout of a signed position or amplitude. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Second readout of a physical time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Metres-per-second readout of a signed velocity component. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Newton readout of a signed force component. -/
def forceComponentInNewtons (force : ForceComponentQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- Newton-per-metre readout of a physical spring stiffness. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  (stiffness UnitChoices.SI).val

/-- Joule readout of Physlib's dimensionful energy quantity. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Scenario and primary-figure vocabulary -/

/-- The component that provides the restoring force. -/
inductive RestoringElement where
  | spring
  | other
  deriving DecidableEq, Repr

/-- Contact condition for the horizontal surface. -/
inductive SurfaceCondition where
  | frictionless
  | dissipative
  deriving DecidableEq, Repr

/-- The motion model stated in the problem. -/
inductive MotionRegime where
  | simpleHarmonic
  | other
  deriving DecidableEq, Repr

/-- Direction of motion along the one-dimensional coordinate axis. -/
inductive CoordinateDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- The two axes of the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity carried by a graph axis. -/
inductive AxisQuantity where
  | positionInMeters
  | signedNetForceInNewtons
  deriving DecidableEq, Repr

/-- Text and symbolic labels visible in the primary image. -/
inductive FigureLabel where
  | xMeters
  | forceNewtons
  | negativePointThree
  | positivePointThree
  | positiveForceScale
  | negativeForceScale
  deriving DecidableEq, Repr

/-!
The calibrated scalar readout of the supplied force--position graph.  The
function records the plotted signed force component in newtons at a position
read in metres; it is a measurement projection, not the physical force type.
-/
structure ForcePositionGraph where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  labelTarget : FigureLabel → GraphAxis
  leftEndpointPositionMeters : ℝ
  rightEndpointPositionMeters : ℝ
  forceScaleNewtons : ℝ
  plottedForceComponentInNewtons : ℝ → ℝ
  plottedSegmentIsStraight : Bool

/-!
The dimensionful block--spring system, its trajectory observables, and the
supplied calibrated graph.  Physlib's scalar harmonic oscillator is retained
as the underlying ideal model and is linked to the dimensionful mass and
stiffness by the governing-law interface below.
-/
structure BlockSpringOscillatorSetup where
  restoringElement : RestoringElement
  surfaceCondition : SurfaceCondition
  motionRegime : MotionRegime
  initialMotionDirection : CoordinateDirection
  blockMass : MassQuantity
  springStiffness : SpringStiffnessQuantity
  equilibriumPosition : LengthQuantity
  amplitude : LengthQuantity
  initialTime : TimeQuantity
  position : TimeQuantity → LengthQuantity
  velocity : TimeQuantity → VelocityQuantity
  netForceAtPosition : LengthQuantity → ForceComponentQuantity
  kineticEnergy : TimeQuantity → DimEnergy
  springPotentialEnergy : TimeQuantity → DimEnergy
  oscillator : ClassicalMechanics.HarmonicOscillator
  graph : ForcePositionGraph

/-!
Problem-statement data.  In particular, no numerical initial speed or kinetic
energy is supplied: only its positive direction is known.
-/
structure MatchesProblemDescription
    (setup : BlockSpringOscillatorSetup) : Prop where
  blockIsAttachedToSpring : setup.restoringElement = .spring
  surfaceIsFrictionless : setup.surfaceCondition = .frictionless
  motionIsSimpleHarmonic : setup.motionRegime = .simpleHarmonic
  blockMassKilograms : massInKilograms setup.blockMass = 1 / 2
  equilibriumAtZero : lengthInMeters setup.equilibriumPosition = 0
  displayedInitialTimeSeconds : timeInSeconds setup.initialTime = 0
  initiallyAtEquilibrium :
    lengthInMeters (setup.position setup.initialTime) =
      lengthInMeters setup.equilibriumPosition
  initiallyMovingInPositiveX : setup.initialMotionDirection = .positiveX
  initialVelocityIsPositive :
    0 < velocityInMetersPerSecond (setup.velocity setup.initialTime)

/-!
Readouts taken from the primary image.  The endpoint positions are treated as
the turning positions of the depicted oscillation, so the positive endpoint
is the physical amplitude.  The plotted signed scalar curve is explicitly
linked to the dimensionful net-force observable throughout the shown range.
-/
structure MatchesPrimaryFigure
    (setup : BlockSpringOscillatorSetup) : Prop where
  horizontalAxisIsPosition :
    setup.graph.horizontalAxisQuantity = .positionInMeters
  verticalAxisIsSignedNetForce :
    setup.graph.verticalAxisQuantity = .signedNetForceInNewtons
  xLabelIsHorizontal : setup.graph.labelTarget .xMeters = .horizontal
  forceLabelIsVertical : setup.graph.labelTarget .forceNewtons = .vertical
  leftPositionLabelIsHorizontal :
    setup.graph.labelTarget .negativePointThree = .horizontal
  rightPositionLabelIsHorizontal :
    setup.graph.labelTarget .positivePointThree = .horizontal
  positiveScaleLabelIsVertical :
    setup.graph.labelTarget .positiveForceScale = .vertical
  negativeScaleLabelIsVertical :
    setup.graph.labelTarget .negativeForceScale = .vertical
  leftEndpointMeters : setup.graph.leftEndpointPositionMeters = -(3 / 10)
  rightEndpointMeters : setup.graph.rightEndpointPositionMeters = 3 / 10
  forceScaleIsSeventyFiveNewtons : setup.graph.forceScaleNewtons = 75
  leftEndpointForce :
    setup.graph.plottedForceComponentInNewtons
        setup.graph.leftEndpointPositionMeters =
      setup.graph.forceScaleNewtons
  graphPassesThroughOrigin :
    setup.graph.plottedForceComponentInNewtons 0 = 0
  rightEndpointForce :
    setup.graph.plottedForceComponentInNewtons
        setup.graph.rightEndpointPositionMeters =
      -setup.graph.forceScaleNewtons
  plottedSegmentIsStraight : setup.graph.plottedSegmentIsStraight = true
  rightEndpointIsAmplitude :
    setup.graph.rightEndpointPositionMeters = lengthInMeters setup.amplitude
  leftEndpointIsNegativeAmplitude :
    setup.graph.leftEndpointPositionMeters = -lengthInMeters setup.amplitude
  plottedCurveReadsPhysicalNetForce :
    ∀ position : LengthQuantity,
      setup.graph.leftEndpointPositionMeters ≤ lengthInMeters position →
      lengthInMeters position ≤ setup.graph.rightEndpointPositionMeters →
      setup.graph.plottedForceComponentInNewtons (lengthInMeters position) =
        forceComponentInNewtons (setup.netForceAtPosition position)

/-- Positivity conditions selecting the physical oscillator branch. -/
structure HasPhysicalParameters
    (setup : BlockSpringOscillatorSetup) : Prop where
  massPositive : 0 < massInKilograms setup.blockMass
  stiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness
  amplitudePositive : 0 < lengthInMeters setup.amplitude

/-!
Governing laws for an undamped one-dimensional simple harmonic oscillator.
They are the dimensionful-readout counterparts of Physlib's linear force,
kinetic-energy, potential-energy, and total-energy definitions.  The final
numerical maximum and answer choice do not occur in this interface.
-/
structure SatisfiesUndampedSimpleHarmonicOscillatorLaws
    (setup : BlockSpringOscillatorSetup) : Prop where
  oscillatorMassMatches :
    setup.oscillator.m = massInKilograms setup.blockMass
  oscillatorStiffnessMatches :
    setup.oscillator.k =
      springStiffnessInNewtonsPerMeter setup.springStiffness
  linearRestoringForceLaw :
    ∀ position : LengthQuantity,
      forceComponentInNewtons (setup.netForceAtPosition position) =
        -springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters position
  kineticEnergyLaw :
    ∀ time : TimeQuantity,
      energyInJoules (setup.kineticEnergy time) =
        (1 / 2 : ℝ) * massInKilograms setup.blockMass *
          velocityInMetersPerSecond (setup.velocity time) ^ 2
  springPotentialEnergyLaw :
    ∀ time : TimeQuantity,
      energyInJoules (setup.springPotentialEnergy time) =
        (1 / 2 : ℝ) *
          springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters (setup.position time) ^ 2
  mechanicalEnergyConservation :
    ∀ time : TimeQuantity,
      energyInJoules (setup.kineticEnergy time) +
          energyInJoules (setup.springPotentialEnergy time) =
        energyInJoules (setup.kineticEnergy setup.initialTime) +
          energyInJoules
            (setup.springPotentialEnergy setup.initialTime)
  amplitudeIsReachedAtPositiveTurningPoint :
    ∃ turningTime : TimeQuantity,
      lengthInMeters (setup.position turningTime) =
          lengthInMeters setup.amplitude ∧
        velocityInMetersPerSecond (setup.velocity turningTime) = 0

/-! ## Requested maximum and displayed answers -/

/-!
An energy is the attained maximum kinetic energy when it is the actual kinetic
energy at some time and its joule readout is a greatest element of the range
of kinetic-energy readouts along the motion.
-/
def IsMaximumKineticEnergy
    (setup : BlockSpringOscillatorSetup) (maximumEnergy : DimEnergy) : Prop :=
  (∃ time : TimeQuantity, maximumEnergy = setup.kineticEnergy time) ∧
    IsGreatest
      (Set.range (fun time : TimeQuantity =>
        energyInJoules (setup.kineticEnergy time)))
      (energyInJoules maximumEnergy)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Joule value printed beside each answer choice. -/
def AnswerChoice.joules : AnswerChoice → ℝ
  | .A => 102 / 10
  | .B => 108 / 10
  | .C => 113 / 10
  | .D => 124 / 10

/-- Dataset metadata recording choice C; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Conventional nearest-tenth rounding with half-ties rounded upward: a positive
exact value in `[displayed - 0.05, displayed + 0.05)` prints as `displayed`.
-/
def RoundsToNearestTenth
    (energy : DimEnergy) (displayedJoules : ℝ) : Prop :=
  displayedJoules - 1 / 20 ≤ energyInJoules energy ∧
    energyInJoules energy < displayedJoules + 1 / 20

/-- A displayed choice is no farther from the exact energy than any option. -/
def IsClosestDisplayedAnswer
    (energy : DimEnergy) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |energyInJoules energy - choice.joules| ≤
      |energyInJoules energy - other.joules|

/-!
The endpoint force and displacement determine the spring stiffness:
`k = F_s / A = 75 N / 0.30 m = 250 N/m`.
-/
lemma springStiffnessInNewtonsPerMeter_eq_twoHundredFifty
    (setup : BlockSpringOscillatorSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_laws : SatisfiesUndampedSimpleHarmonicOscillatorLaws setup) :
    springStiffnessInNewtonsPerMeter setup.springStiffness = 250 := by
  have hAmplitude :
      lengthInMeters setup.amplitude =
        setup.graph.rightEndpointPositionMeters :=
    _figure.rightEndpointIsAmplitude.symm
  have hLeftLeAmplitude :
      setup.graph.leftEndpointPositionMeters ≤
        lengthInMeters setup.amplitude := by
    rw [hAmplitude, _figure.leftEndpointMeters, _figure.rightEndpointMeters]
    norm_num
  have hAmplitudeLeRight :
      lengthInMeters setup.amplitude ≤
        setup.graph.rightEndpointPositionMeters := by
    rw [hAmplitude]
  have hGraphPhysical :=
    _figure.plottedCurveReadsPhysicalNetForce setup.amplitude
      hLeftLeAmplitude hAmplitudeLeRight
  have hForce :
      forceComponentInNewtons (setup.netForceAtPosition setup.amplitude) =
        -75 := by
    calc
      forceComponentInNewtons (setup.netForceAtPosition setup.amplitude) =
          setup.graph.plottedForceComponentInNewtons
            (lengthInMeters setup.amplitude) := hGraphPhysical.symm
      _ = setup.graph.plottedForceComponentInNewtons
            setup.graph.rightEndpointPositionMeters := by rw [hAmplitude]
      _ = -setup.graph.forceScaleNewtons := _figure.rightEndpointForce
      _ = -75 := by rw [_figure.forceScaleIsSeventyFiveNewtons]
  have hHooke := _laws.linearRestoringForceLaw setup.amplitude
  rw [hAmplitude, _figure.rightEndpointMeters] at hHooke
  nlinarith

/-!
Energy conservation transfers the spring energy at the amplitude turning
point to kinetic energy at equilibrium.  Nonnegative spring potential energy
also shows this equilibrium kinetic energy is a genuine attained maximum.
The force--displacement triangle has area
`(1/2) F_s A = (1/2)(75)(0.30) = 45/4 J`.
-/
lemma maximumKineticEnergy_exact
    (setup : BlockSpringOscillatorSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesUndampedSimpleHarmonicOscillatorLaws setup) :
    ∃ maximumEnergy : DimEnergy,
      IsMaximumKineticEnergy setup maximumEnergy ∧
        energyInJoules maximumEnergy =
          (1 / 2 : ℝ) *
            springStiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters setup.amplitude ^ 2 ∧
        energyInJoules maximumEnergy =
          (1 / 2 : ℝ) * setup.graph.forceScaleNewtons *
            setup.graph.rightEndpointPositionMeters ∧
        energyInJoules maximumEnergy = 45 / 4 := by
  have hInitialPosition :
      lengthInMeters (setup.position setup.initialTime) = 0 := by
    calc
      lengthInMeters (setup.position setup.initialTime) =
          lengthInMeters setup.equilibriumPosition :=
        _description.initiallyAtEquilibrium
      _ = 0 := _description.equilibriumAtZero
  have hInitialPotential :
      energyInJoules (setup.springPotentialEnergy setup.initialTime) = 0 := by
    rw [_laws.springPotentialEnergyLaw, hInitialPosition]
    ring
  obtain ⟨turningTime, hTurningPosition, hTurningVelocity⟩ :=
    _laws.amplitudeIsReachedAtPositiveTurningPoint
  have hTurningKinetic :
      energyInJoules (setup.kineticEnergy turningTime) = 0 := by
    rw [_laws.kineticEnergyLaw, hTurningVelocity]
    ring
  have hTurningPotential :
      energyInJoules (setup.springPotentialEnergy turningTime) =
        (1 / 2 : ℝ) *
          springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.amplitude ^ 2 := by
    rw [_laws.springPotentialEnergyLaw, hTurningPosition]
  have hInitialKinetic :
      energyInJoules (setup.kineticEnergy setup.initialTime) =
        (1 / 2 : ℝ) *
          springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.amplitude ^ 2 := by
    have hConservation :=
      _laws.mechanicalEnergyConservation turningTime
    rw [hTurningKinetic, hTurningPotential, hInitialPotential] at hConservation
    linarith
  have hPotentialNonnegative (time : TimeQuantity) :
      0 ≤ energyInJoules (setup.springPotentialEnergy time) := by
    rw [_laws.springPotentialEnergyLaw]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (le_of_lt _physical.stiffnessPositive))
      (sq_nonneg (lengthInMeters (setup.position time)))
  let maximumEnergy : DimEnergy := setup.kineticEnergy setup.initialTime
  refine ⟨maximumEnergy, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact ⟨setup.initialTime, rfl⟩
    · constructor
      · exact ⟨setup.initialTime, rfl⟩
      · rintro _ ⟨time, rfl⟩
        have hConservation := _laws.mechanicalEnergyConservation time
        rw [hInitialPotential] at hConservation
        dsimp [maximumEnergy]
        linarith [hPotentialNonnegative time]
  · exact hInitialKinetic
  · rw [hInitialKinetic, ← _figure.rightEndpointIsAmplitude,
      _figure.forceScaleIsSeventyFiveNewtons,
      _figure.rightEndpointMeters]
    have hStiffness :=
      springStiffnessInNewtonsPerMeter_eq_twoHundredFifty
        setup _figure _laws
    rw [hStiffness]
    norm_num
  · rw [hInitialKinetic, ← _figure.rightEndpointIsAmplitude,
      _figure.rightEndpointMeters]
    have hStiffness :=
      springStiffnessInNewtonsPerMeter_eq_twoHundredFifty
        setup _figure _laws
    rw [hStiffness]
    norm_num

/-!
The oscillator's maximum kinetic energy is exactly `45/4 J = 11.25 J`.
With the displayed one-decimal precision this rounds upward to `11.3 J`,
choice C, and C is a closest displayed option.

This formalizes `thm:physics:phyx_mini_0275:target`.
-/
theorem problem_phyx_mini_0275
    (setup : BlockSpringOscillatorSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesUndampedSimpleHarmonicOscillatorLaws setup) :
    ∃ maximumEnergy : DimEnergy,
      IsMaximumKineticEnergy setup maximumEnergy ∧
        energyInJoules maximumEnergy =
          (1 / 2 : ℝ) * setup.graph.forceScaleNewtons *
            setup.graph.rightEndpointPositionMeters ∧
        energyInJoules maximumEnergy = 45 / 4 ∧
        RoundsToNearestTenth maximumEnergy AnswerChoice.C.joules ∧
        IsClosestDisplayedAnswer maximumEnergy .C := by
  obtain ⟨maximumEnergy, hMaximum, _, hGraphEnergy, hExactEnergy⟩ :=
    maximumKineticEnergy_exact
      setup _description _figure _physical _laws
  refine ⟨maximumEnergy, hMaximum, hGraphEnergy, hExactEnergy, ?_, ?_⟩
  · norm_num [RoundsToNearestTenth, AnswerChoice.joules, hExactEnergy]
  · intro other
    cases other <;>
      norm_num [AnswerChoice.joules, hExactEnergy]

end PhyXMiniProblems.ProblemPhyXMini0275
