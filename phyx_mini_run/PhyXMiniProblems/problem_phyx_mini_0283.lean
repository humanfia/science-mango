import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0283

open Dimension

/-!
# Acceleration limit for a two-cord toddler jump seat

A child and jump seat hang from the horizontal part of a doorframe by one
elastic cord on each side.  Their common static descent is `d_s`.  From that
equilibrium position the seat is pulled downward an additional distance
`d_m` and released.  The requested design value of `d_s` makes the maximum
vertical acceleration equal to `0.20 g` when `d_m = 10 cm`.

The physical masses, lengths, acceleration magnitudes, and spring stiffnesses
below are Physlib dimension-carrying quantities.  Real numbers occur only as
coherent unit readouts and as dimensionless ratios printed in the exercise.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative spring stiffness, with dimension force per length, `M T⁻²`. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout UnitChoices.SI length

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  quantityReadout centimeterUnitChoices length

/-- Meters-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  quantityReadout UnitChoices.SI acceleration

/-- Newtons-per-meter readout of a spring stiffness. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  quantityReadout UnitChoices.SI stiffness

/-! ## Primary-figure vocabulary and geometry -/

/-- The two modeled sides of the jump-seat suspension. -/
inductive CordSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Individually identifiable components visible in the supplied bitmap. -/
inductive FigureComponent where
  | horizontalDoorframeSupport
  | leftCordAssembly
  | rightCordAssembly
  | jumpSeat
  | seatedChild
  | floor
  deriving DecidableEq, Repr

/-- Upper anchor positions on the horizontal support. -/
inductive FrameAttachment where
  | leftAnchor
  | rightAnchor
  deriving DecidableEq, Repr

/-- Lower attachment positions on the seat. -/
inductive SeatAttachment where
  | leftSide
  | rightSide
  deriving DecidableEq, Repr

/-- The direction in which the modeled seat is free to oscillate. -/
inductive MotionAxis where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Mechanical idealization assigned to each elastic cord. -/
inductive CordMechanicalModel where
  | idealLinearSpring
  | other
  deriving DecidableEq, Repr

/-!
Qualitative and incidence data transcribed from the primary image.  The image
contains no printed labels or numerical scale; its colors and proportions do
not supply any physical measurement.
-/
structure JumpSeatFigure where
  shows : FigureComponent → Prop
  upperAttachment : CordSide → FrameAttachment
  lowerAttachment : CordSide → SeatAttachment
  cordRunsVertically : CordSide → Prop
  childIsSeated : Prop
  childFeetAreVisible : Bool
  hasPrintedText : Bool
  depictedCordAssemblyCount : ℕ

/-! ## Independent physical setup -/

/-!
All response quantities are independent fields.  In particular,
`staticDescent` is not defined from the answer.  The scalar Physlib oscillator
models the combined child-seat motion about the loaded equilibrium; later
governing-law fields relate its positive mass and stiffness parameters to the
dimensionful apparatus.
-/
structure JumpSeatOscillatorSetup where
  childMass : MassQuantity
  seatMass : MassQuantity
  suspendedMass : MassQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  perSideCordStiffness : CordSide → SpringStiffnessQuantity
  effectiveParallelStiffness : SpringStiffnessQuantity
  cordExtensionAtStaticEquilibrium : CordSide → LengthQuantity
  staticDescent : LengthQuantity
  releasePullDown : LengthQuantity
  maximumAccelerationMagnitude : AccelerationMagnitudeQuantity
  safetyFractionOfGravity : ℝ
  oscillator : ClassicalMechanics.HarmonicOscillator
  modeledCordCount : CordSide → ℕ
  motionAxis : MotionAxis
  cordModel : CordMechanicalModel
  oscillatesAboutLoadedEquilibrium : Bool
  figure : JumpSeatFigure

/-!
Problem data and primary-image readouts.  The condition on maximum
acceleration says that the design is evaluated at the stated `0.20 g` safety
threshold; it supplies no value for `staticDescent`.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : JumpSeatOscillatorSetup) : Prop where
  pullDownCentimeters : lengthInCentimeters setup.releasePullDown = 10
  safetyFractionIsTwentyPercent : setup.safetyFractionOfGravity = 1 / 5
  accelerationAtSafetyThreshold :
    accelerationInMetersPerSecondSquared
        setup.maximumAccelerationMagnitude =
      setup.safetyFractionOfGravity *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  oneModeledCordOnEachSide : ∀ side, setup.modeledCordCount side = 1
  modeledMotionIsVertical : setup.motionAxis = .vertical
  cordsAreTreatedAsLinearSprings : setup.cordModel = .idealLinearSpring
  releasedMotionIsAboutLoadedEquilibrium :
    setup.oscillatesAboutLoadedEquilibrium = true
  allComponentsShown : ∀ component, setup.figure.shows component
  leftCordUpperAnchor :
    setup.figure.upperAttachment .left = .leftAnchor
  rightCordUpperAnchor :
    setup.figure.upperAttachment .right = .rightAnchor
  leftCordSeatAttachment :
    setup.figure.lowerAttachment .left = .leftSide
  rightCordSeatAttachment :
    setup.figure.lowerAttachment .right = .rightSide
  cordsDepictedVertically : ∀ side, setup.figure.cordRunsVertically side
  childDepictedInSeat : setup.figure.childIsSeated
  childFeetVisible : setup.figure.childFeetAreVisible = true
  twoCordAssembliesDepicted : setup.figure.depictedCordAssemblyCount = 2
  noPrintedFigureLabels : setup.figure.hasPrintedText = false

/-- Positivity and nondegeneracy conditions for the physical design. -/
structure HasPhysicalJumpSeatParameters
    (setup : JumpSeatOscillatorSetup) : Prop where
  suspendedMassPositive : 0 < massInKilograms setup.suspendedMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  cordStiffnessPositive :
    ∀ side,
      0 < springStiffnessInNewtonsPerMeter
        (setup.perSideCordStiffness side)
  effectiveStiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter
      setup.effectiveParallelStiffness
  staticDescentPositive : 0 < lengthInMeters setup.staticDescent
  pullDownPositive : 0 < lengthInMeters setup.releasePullDown
  maximumAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.maximumAccelerationMagnitude

/-! ## Governing spring, equilibrium, and oscillator laws -/

/-!
The two Hookean cords undergo the same vertical extension and act in parallel,
so their stiffnesses add.  Static force balance gives `K d_s = m g`.  Around
that loaded equilibrium, Physlib's harmonic oscillator has the same combined
mass and effective stiffness, and an amplitude `d_m` has maximum acceleration
`ω² d_m`.

These are general mechanical laws.  None states `d_s = 50 cm` or chooses an
answer label.
-/
structure SatisfiesTwoCordJumpSeatLaws
    (setup : JumpSeatOscillatorSetup) : Prop where
  suspendedMassIsChildPlusSeat :
    massInKilograms setup.suspendedMass =
      massInKilograms setup.childMass + massInKilograms setup.seatMass
  eachCordExtensionEqualsStaticDescent :
    ∀ side,
      lengthInMeters (setup.cordExtensionAtStaticEquilibrium side) =
        lengthInMeters setup.staticDescent
  parallelStiffnessAdds :
    springStiffnessInNewtonsPerMeter setup.effectiveParallelStiffness =
      springStiffnessInNewtonsPerMeter
          (setup.perSideCordStiffness .left) +
        springStiffnessInNewtonsPerMeter
          (setup.perSideCordStiffness .right)
  staticHookeEquilibrium :
    springStiffnessInNewtonsPerMeter setup.effectiveParallelStiffness *
        lengthInMeters setup.staticDescent =
      massInKilograms setup.suspendedMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  oscillatorMassMatchesSuspendedMass :
    setup.oscillator.m = massInKilograms setup.suspendedMass
  oscillatorStiffnessMatchesParallelCords :
    setup.oscillator.k =
      springStiffnessInNewtonsPerMeter setup.effectiveParallelStiffness
  releaseMaximumAcceleration :
    accelerationInMetersPerSecondSquared
        setup.maximumAccelerationMagnitude =
      setup.oscillator.ω ^ 2 * lengthInMeters setup.releasePullDown

/-! ## Derived relation and answer -/

/-!
Eliminating the common mass and effective stiffness between static balance
and the harmonic-oscillator acceleration law gives
`a_max d_s = g d_m`.
-/
lemma maximum_acceleration_static_descent_relation
    (setup : JumpSeatOscillatorSetup)
    (_physical : HasPhysicalJumpSeatParameters setup)
    (_laws : SatisfiesTwoCordJumpSeatLaws setup) :
    accelerationInMetersPerSecondSquared
          setup.maximumAccelerationMagnitude *
        lengthInMeters setup.staticDescent =
      accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters setup.releasePullDown := by
  rw [_laws.releaseMaximumAcceleration, setup.oscillator.ω_sq,
    _laws.oscillatorStiffnessMatchesParallelCords,
    _laws.oscillatorMassMatchesSuspendedMass]
  field_simp [_physical.suspendedMassPositive.ne']
  calc
    springStiffnessInNewtonsPerMeter setup.effectiveParallelStiffness *
          lengthInMeters setup.releasePullDown *
        lengthInMeters setup.staticDescent =
      (springStiffnessInNewtonsPerMeter setup.effectiveParallelStiffness *
          lengthInMeters setup.staticDescent) *
        lengthInMeters setup.releasePullDown := by ring
    _ = (massInKilograms setup.suspendedMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration) *
        lengthInMeters setup.releasePullDown := by
      rw [_laws.staticHookeEquilibrium]
    _ = massInKilograms setup.suspendedMass *
          lengthInMeters setup.releasePullDown *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration := by ring

/-- The stated `10 cm` amplitude and `0.20 g` limit require `d_s = 50 cm`. -/
lemma static_descent_is_fifty_centimeters
    (setup : JumpSeatOscillatorSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalJumpSeatParameters setup)
    (_laws : SatisfiesTwoCordJumpSeatLaws setup) :
    lengthInCentimeters setup.staticDescent = 50 := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (length.2 UnitChoices.SI centimeterUnitChoices)
    norm_num [lengthInCentimeters, lengthInMeters, quantityReadout,
      centimeterUnitChoices, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have h_pullDown :=
    length_centimeters_eq setup.releasePullDown
  rw [_problem.pullDownCentimeters] at h_pullDown
  have h_pullDown_meters :
      lengthInMeters setup.releasePullDown = 1 / 10 := by
    linarith
  have h_relation :=
    maximum_acceleration_static_descent_relation
      setup _physical _laws
  rw [_problem.accelerationAtSafetyThreshold,
    _problem.safetyFractionIsTwentyPercent,
    h_pullDown_meters] at h_relation
  have h_staticDescent_meters :
      lengthInMeters setup.staticDescent = 1 / 2 := by
    apply mul_left_cancel₀
      _physical.gravityPositive.ne'
    nlinarith
  rw [length_centimeters_eq, h_staticDescent_meters]
  norm_num

/-- Labels of the four answers printed in the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Static-descent readout printed beside each answer, in centimeters. -/
def AnswerChoice.staticDescentCentimeters : AnswerChoice → ℝ
  | .A => 40
  | .B => 45
  | .C => 55
  | .D => 50

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A modeled design agrees with one of the displayed centimeter choices. -/
def MatchesAnswerChoice
    (setup : JumpSeatOscillatorSetup) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters setup.staticDescent =
    choice.staticDescentCentimeters

/-!
The required static descent is `50 cm`, hence recorded choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0283:target`.
-/
theorem problem_phyx_mini_0283
    (setup : JumpSeatOscillatorSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalJumpSeatParameters setup)
    (_laws : SatisfiesTwoCordJumpSeatLaws setup) :
    lengthInCentimeters setup.staticDescent = 50 ∧
      MatchesAnswerChoice setup recordedAnswerChoice := by
  have h_staticDescent :=
    static_descent_is_fifty_centimeters
      setup _problem _physical _laws
  refine ⟨h_staticDescent, ?_⟩
  simpa [MatchesAnswerChoice, recordedAnswerChoice,
    AnswerChoice.staticDescentCentimeters] using h_staticDescent

end PhyXMiniProblems.ProblemPhyXMini0283
