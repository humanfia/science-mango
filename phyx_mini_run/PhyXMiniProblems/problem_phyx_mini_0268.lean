import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0268

open Dimension

/-!
# Small oscillations of a center-pivoted rod coupled to a spring

A uniform rod of mass `0.600 kg` rotates in a horizontal plane about a
vertical axis through its center.  An ideal spring of force constant
`1850 N/m` joins one endpoint of the rod to a wall.  At equilibrium the rod
is parallel to the wall.  The primary image labels the wall, the spring by
`k`, and the central rotation axis.

Physlib dimensionful quantities represent mass, length, time, force,
inertia, and torque.  Real numbers below occur only as signed angular
coordinates, coherent unit readouts, and dimensionless numerical data printed
with the exercise.
-/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed displacement along the spring axis. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A spring force constant has dimension force per length, or mass/time². -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed force component along the spring axis. -/
abbrev SignedForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Moment of inertia has dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A signed torque about the vertical rotation axis. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A nonnegative linear restoring-torque coefficient per dimensionless
radian. -/
abbrev RestoringCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Angular acceleration has inverse-time-squared dimension because radians
are dimensionless. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A nonnegative angular frequency, with inverse-time dimension. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed displacement in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (displacement : SignedLengthQuantity) : ℝ :=
  (displacement {UnitChoices.SI with length := unit}).val

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a spring constant in coherent selected mass and time units. -/
def springConstantReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Read a signed force in coherent mechanical units. -/
def signedForceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : SignedForceQuantity) : ℝ :=
  (force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Read a moment of inertia in coherent mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read a signed torque in coherent mechanical units. -/
def signedTorqueReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (torque : SignedTorqueQuantity) : ℝ :=
  (torque {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Read a restoring coefficient in coherent mechanical units. -/
def restoringCoefficientReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (coefficient : RestoringCoefficientQuantity) : ℝ :=
  ((coefficient {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular acceleration in inverse units of a selected time unit. -/
def angularAccelerationReadout
    (timeUnit : TimeUnit) (acceleration : AngularAccelerationQuantity) : ℝ :=
  (acceleration {UnitChoices.SI with time := timeUnit}).val

/-- Read angular frequency in inverse units of a selected time unit. -/
def angularFrequencyReadout
    (timeUnit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- SI kilogram readout of the rod mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- SI meter readout of a length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- SI second readout of a duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- SI spring-constant readout, numerically in newtons per meter. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  springConstantReadout MassUnit.kilograms TimeUnit.seconds springConstant

/-- Objects visible in the supplied overhead-view image. -/
inductive FigureObject where
  | wall
  | coiledSpring
  | uniformRod
  | rotationAxisMarker
  deriving DecidableEq, Repr

/-- Text labels printed in the supplied image. -/
inductive FigureTextLabel where
  | wallText
  | springConstantK
  | rotationAxisText
  deriving DecidableEq, Repr

/-- Distinguished points in the rod--spring diagram. -/
inductive FigurePoint where
  | wallAnchor
  | springRodAttachment
  | rodCenterAxis
  | freeRodEndpoint
  deriving DecidableEq, Repr

/-- The plane in which the rod is free to move. -/
inductive MotionPlane where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Orientation of the fixed rotation axis. -/
inductive AxisOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- The mass model for the rod. -/
inductive RodMassModel where
  | uniform
  | other
  deriving DecidableEq, Repr

/-- The geometric idealization used for the rod's central moment of inertia. -/
inductive RodGeometry where
  | longSlender
  | other
  deriving DecidableEq, Repr

/-- The force model for the spring. -/
inductive SpringForceModel where
  | idealHookean
  | other
  deriving DecidableEq, Repr

/-- Relative orientation of the rod and wall at equilibrium. -/
inductive RodWallAlignment where
  | parallel
  | other
  deriving DecidableEq, Repr

/-- Relative orientation of the spring and rod at equilibrium. -/
inductive SpringRodAlignment where
  | perpendicular
  | other
  deriving DecidableEq, Repr

/-- How the slightly displaced rod is started. -/
inductive ReleaseCondition where
  | fromRestAfterSmallRotation
  | other
  deriving DecidableEq, Repr

/-!
Incidence data and qualitative readouts transcribed from the primary image.
The bitmap shows a displaced rod but contains no length scale, so
`depictedDisplacementAngle` is a dimensionless schematic coordinate rather
than measured numerical data.
-/
structure SuppliedRodSpringFigure where
  shows : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  springEndpoints : FigurePoint × FigurePoint
  rodEndpoints : FigurePoint × FigurePoint
  rotationAxisPoint : FigurePoint
  springAttachmentIsRodEndpoint : Bool
  rotationAxisIsRodCenter : Bool
  viewIsOverhead : Bool
  wallIsFixed : Bool
  springLiesInHorizontalPlane : Bool
  rodShownDisplacedFromEquilibrium : Bool
  depictedDisplacementAngle : ℝ

/-!
Independent physical quantities and response fields of the experiment.  The
rod length is included even though the final closed form is length-independent.
Neither the period nor the restoring coefficient is defined by the requested
answer; governing laws below constrain them.
-/
structure CenterPivotedRodSpringSetup where
  rodMass : MassQuantity
  rodLength : LengthQuantity
  endpointLeverArm : LengthQuantity
  springConstant : SpringConstantQuantity
  momentOfInertiaAboutAxis : MomentOfInertiaQuantity
  linearizedRestoringCoefficient : RestoringCoefficientQuantity
  smallOscillationAngularFrequency : AngularFrequencyQuantity
  smallOscillationPeriod : TimeQuantity
  smallAngleCutoff : NNReal
  linearizedSpringExtension : ℝ → SignedLengthQuantity
  linearizedSpringForce : ℝ → SignedForceQuantity
  linearizedSpringTorque : ℝ → SignedTorqueQuantity
  linearizedTotalTorque : ℝ → SignedTorqueQuantity
  linearizedAngularAcceleration : ℝ → AngularAccelerationQuantity
  motionPlane : MotionPlane
  axisOrientation : AxisOrientation
  rodMassModel : RodMassModel
  rodGeometry : RodGeometry
  springForceModel : SpringForceModel
  equilibriumAlignment : RodWallAlignment
  equilibriumSpringRodAlignment : SpringRodAlignment
  releaseCondition : ReleaseCondition
  figure : SuppliedRodSpringFigure

/-- The chosen neighborhood in which first-order angular laws are used. -/
def IsInSmallAngleRegime
    (setup : CenterPivotedRodSpringSetup) (θ : ℝ) : Prop :=
  |θ| ≤ (setup.smallAngleCutoff : ℝ)

/-!
Numerical data, qualitative setup, and figure readouts supplied by the source.
The rod length and pictured deflection have no numerical readout in the image.
No field assigns the requested period or selects an answer choice.
-/
structure MatchesProblemAndFigureReadouts
    (setup : CenterPivotedRodSpringSetup) : Prop where
  rodMassKilograms : massInKilograms setup.rodMass = 0.600
  springConstantNewtonsPerMeter :
    springConstantInNewtonsPerMeter setup.springConstant = 1850
  rodMovesInHorizontalPlane : setup.motionPlane = .horizontal
  axisIsVertical : setup.axisOrientation = .vertical
  rodIsUniform : setup.rodMassModel = .uniform
  rodIsLongAndSlender : setup.rodGeometry = .longSlender
  springIsIdealHookean : setup.springForceModel = .idealHookean
  rodParallelToWallAtEquilibrium :
    setup.equilibriumAlignment = .parallel
  springPerpendicularToRodAtEquilibrium :
    setup.equilibriumSpringRodAlignment = .perpendicular
  releasedFromRestAfterSmallRotation :
    setup.releaseCondition = .fromRestAfterSmallRotation
  allObjectsShown : ∀ object, setup.figure.shows object = true
  allPrintedLabelsShown :
    ∀ label, setup.figure.showsTextLabel label = true
  springJoinsWallToRodEndpoint :
    setup.figure.springEndpoints =
      (.wallAnchor, .springRodAttachment)
  rodRunsBetweenItsEndpoints :
    setup.figure.rodEndpoints =
      (.springRodAttachment, .freeRodEndpoint)
  axisMarkedAtRodCenter :
    setup.figure.rotationAxisPoint = .rodCenterAxis
  springConnectionAtEndpoint :
    setup.figure.springAttachmentIsRodEndpoint = true
  centralAxisReadout : setup.figure.rotationAxisIsRodCenter = true
  overheadViewReadout : setup.figure.viewIsOverhead = true
  fixedWallReadout : setup.figure.wallIsFixed = true
  horizontalSpringConnectionReadout :
    setup.figure.springLiesInHorizontalPlane = true
  displacedRodShown :
    setup.figure.rodShownDisplacedFromEquilibrium = true

/-!
Strict positivity and nondegeneracy assumptions.  They make the rod and spring
physical and support the scalar oscillator bridge without prescribing its
period.
-/
structure HasPhysicalRodSpringParameters
    (setup : CenterPivotedRodSpringSetup) : Prop where
  rodMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.rodMass
  rodLengthPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.rodLength
  endpointLeverArmPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.endpointLeverArm
  springConstantPositive :
    ∀ massUnit timeUnit,
      0 < springConstantReadout massUnit timeUnit setup.springConstant
  momentOfInertiaPositive :
    ∀ massUnit lengthUnit,
      0 < momentOfInertiaReadout massUnit lengthUnit
        setup.momentOfInertiaAboutAxis
  restoringCoefficientPositive :
    ∀ massUnit lengthUnit timeUnit,
      0 < restoringCoefficientReadout massUnit lengthUnit timeUnit
        setup.linearizedRestoringCoefficient
  angularFrequencyPositive :
    ∀ timeUnit,
      0 < angularFrequencyReadout timeUnit
        setup.smallOscillationAngularFrequency
  periodPositive :
    ∀ timeUnit, 0 < timeReadout timeUnit setup.smallOscillationPeriod
  smallAngleCutoffPositive : 0 < (setup.smallAngleCutoff : ℝ)
  smallAngleCutoffBelowRightAngle :
    (setup.smallAngleCutoff : ℝ) < Real.pi / 2

/-!
For a uniform thin rod of length `L` rotating about a perpendicular axis
through its center, `I = m L² / 12`.  This local law predicate is needed
because the available Physlib rigid-body rotational equation is informal and
does not provide the uniform-rod formula.
-/
structure SatisfiesUniformRodInertiaLaw
    (setup : CenterPivotedRodSpringSetup) : Prop where
  uniformRodInertia :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.momentOfInertiaAboutAxis =
        massReadout massUnit setup.rodMass *
          (lengthReadout lengthUnit setup.rodLength) ^ 2 / 12

/-!
Because the pivot is at the rod center and the spring is connected to one end,
the spring's lever arm is `L/2`.  This is figure/setup geometry, not a period
formula.
-/
structure SatisfiesCenteredEndpointGeometry
    (setup : CenterPivotedRodSpringSetup) : Prop where
  endpointLeverArmIsHalfLength :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit setup.endpointLeverArm =
        lengthReadout lengthUnit setup.rodLength / 2

/-!
First-order mechanics for a signed angular displacement `θ`, whose positive
direction is chosen to increase the spring length:

* the attached endpoint moves by `r θ` along the spring axis;
* Hooke's law gives force `-k x`;
* the spring torque is the force times the centered lever arm;
* the spring is the only source of torque in the horizontal plane;
* `τ = -κ θ` characterizes the effective restoring coefficient;
* rotational Newton's law is `I θ'' = τ`.

These laws contain no period formula or numerical answer.
-/
structure SatisfiesLinearizedRodSpringLaws
    (setup : CenterPivotedRodSpringSetup) : Prop where
  endpointTangentialDisplacement :
    ∀ (lengthUnit : LengthUnit) (θ : ℝ),
      IsInSmallAngleRegime setup θ →
        signedLengthReadout lengthUnit
            (setup.linearizedSpringExtension θ) =
          lengthReadout lengthUnit setup.endpointLeverArm * θ
  hookeLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit) (θ : ℝ),
      IsInSmallAngleRegime setup θ →
        signedForceReadout massUnit lengthUnit timeUnit
            (setup.linearizedSpringForce θ) =
          -springConstantReadout massUnit timeUnit setup.springConstant *
            signedLengthReadout lengthUnit
              (setup.linearizedSpringExtension θ)
  springTorqueLeverArm :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit) (θ : ℝ),
      IsInSmallAngleRegime setup θ →
        signedTorqueReadout massUnit lengthUnit timeUnit
            (setup.linearizedSpringTorque θ) =
          lengthReadout lengthUnit setup.endpointLeverArm *
            signedForceReadout massUnit lengthUnit timeUnit
              (setup.linearizedSpringForce θ)
  totalTorqueIsSpringTorque :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit) (θ : ℝ),
      IsInSmallAngleRegime setup θ →
        signedTorqueReadout massUnit lengthUnit timeUnit
            (setup.linearizedTotalTorque θ) =
          signedTorqueReadout massUnit lengthUnit timeUnit
            (setup.linearizedSpringTorque θ)
  restoringCoefficientCharacterization :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit) (θ : ℝ),
      IsInSmallAngleRegime setup θ →
        signedTorqueReadout massUnit lengthUnit timeUnit
            (setup.linearizedTotalTorque θ) =
          -restoringCoefficientReadout massUnit lengthUnit timeUnit
              setup.linearizedRestoringCoefficient * θ
  rotationalNewtonSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit) (θ : ℝ),
      IsInSmallAngleRegime setup θ →
        momentOfInertiaReadout massUnit lengthUnit
              setup.momentOfInertiaAboutAxis *
            angularAccelerationReadout timeUnit
              (setup.linearizedAngularAcceleration θ) =
          signedTorqueReadout massUnit lengthUnit timeUnit
            (setup.linearizedTotalTorque θ)

/-!
The scalar equation `I θ'' + κ θ = 0` has the same mathematical form as
Physlib's positive harmonic oscillator.  Its `m` slot is filled by the
moment-of-inertia readout and its `k` slot by the restoring-torque coefficient
readout; their ratio has the required inverse-time-squared dimension.
-/
def scalarRotationalOscillator
    (setup : CenterPivotedRodSpringSetup)
    (hPhysical : HasPhysicalRodSpringParameters setup)
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit) :
    ClassicalMechanics.HarmonicOscillator where
  m := momentOfInertiaReadout massUnit lengthUnit
    setup.momentOfInertiaAboutAxis
  k := restoringCoefficientReadout massUnit lengthUnit timeUnit
    setup.linearizedRestoringCoefficient
  m_pos := hPhysical.momentOfInertiaPositive massUnit lengthUnit
  k_pos := hPhysical.restoringCoefficientPositive massUnit lengthUnit timeUnit

/-!
The modeled angular frequency and period agree with Physlib's grounded
`ω = sqrt (k/m)` and `period = 2π/ω` for the scalar rotational oscillator.
This is a generic simple-harmonic-motion law; it does not expand `I` or `κ`
using this problem's rod and spring parameters.
-/
structure SatisfiesIdealSmallOscillationLaw
    (setup : CenterPivotedRodSpringSetup)
    (hPhysical : HasPhysicalRodSpringParameters setup) : Prop where
  angularFrequencyFromOscillator :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      angularFrequencyReadout timeUnit
          setup.smallOscillationAngularFrequency =
        (scalarRotationalOscillator setup hPhysical
          massUnit lengthUnit timeUnit).ω
  periodFromAngularFrequency :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      timeReadout timeUnit setup.smallOscillationPeriod =
        ClassicalMechanics.HarmonicOscillator.period
          (scalarRotationalOscillator setup hPhysical
            massUnit lengthUnit timeUnit)

/-!
The linearized spring geometry and Hooke law imply `κ = k r²`.  This is an
intermediate consequence rather than a premise field.
-/
lemma restoringCoefficient_readout
    (setup : CenterPivotedRodSpringSetup)
    (hPhysical : HasPhysicalRodSpringParameters setup)
    (hLaws : SatisfiesLinearizedRodSpringLaws setup)
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (timeUnit : TimeUnit) :
    restoringCoefficientReadout massUnit lengthUnit timeUnit
        setup.linearizedRestoringCoefficient =
      springConstantReadout massUnit timeUnit setup.springConstant *
        (lengthReadout lengthUnit setup.endpointLeverArm) ^ 2 := by
  let θ : ℝ := setup.smallAngleCutoff
  have hθpos : 0 < θ := hPhysical.smallAngleCutoffPositive
  have hθsmall : IsInSmallAngleRegime setup θ := by
    rw [IsInSmallAngleRegime, abs_of_pos hθpos]
  have hExtension :=
    hLaws.endpointTangentialDisplacement lengthUnit θ hθsmall
  have hForce :=
    hLaws.hookeLaw massUnit lengthUnit timeUnit θ hθsmall
  have hSpringTorque :=
    hLaws.springTorqueLeverArm massUnit lengthUnit timeUnit θ hθsmall
  have hTotalTorque :=
    hLaws.totalTorqueIsSpringTorque massUnit lengthUnit timeUnit θ hθsmall
  have hRestoring :=
    hLaws.restoringCoefficientCharacterization
      massUnit lengthUnit timeUnit θ hθsmall
  apply mul_right_cancel₀ hθpos.ne'
  calc
    restoringCoefficientReadout massUnit lengthUnit timeUnit
          setup.linearizedRestoringCoefficient * θ =
        -signedTorqueReadout massUnit lengthUnit timeUnit
          (setup.linearizedTotalTorque θ) := by linarith
    _ = -signedTorqueReadout massUnit lengthUnit timeUnit
          (setup.linearizedSpringTorque θ) := by rw [hTotalTorque]
    _ = -(lengthReadout lengthUnit setup.endpointLeverArm *
          signedForceReadout massUnit lengthUnit timeUnit
            (setup.linearizedSpringForce θ)) := by rw [hSpringTorque]
    _ = -(lengthReadout lengthUnit setup.endpointLeverArm *
          (-springConstantReadout massUnit timeUnit setup.springConstant *
            signedLengthReadout lengthUnit
              (setup.linearizedSpringExtension θ))) := by rw [hForce]
    _ = -(lengthReadout lengthUnit setup.endpointLeverArm *
          (-springConstantReadout massUnit timeUnit setup.springConstant *
            (lengthReadout lengthUnit setup.endpointLeverArm * θ))) := by
          rw [hExtension]
    _ = (springConstantReadout massUnit timeUnit setup.springConstant *
          (lengthReadout lengthUnit setup.endpointLeverArm) ^ 2) * θ := by
          ring

/-- The answer labels displayed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Period values printed beside the answer choices, in seconds. -/
def displayedPeriodInSeconds : AnswerChoice → ℝ
  | .A => 0.0562
  | .B => 0.0587
  | .C => 0.0653
  | .D => 0.0674

/-- The answer label recorded in the source dataset; this is metadata, not a
premise of either theorem below. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A computed duration rounds to the displayed value at four decimal places. -/
def RoundsToFourDecimalPlaces (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 20000

/-- A displayed choice agrees, to the printed precision, with the physical
period's SI-second readout. -/
def MatchesAnswerChoice
    (setup : CenterPivotedRodSpringSetup) (choice : AnswerChoice) : Prop :=
  RoundsToFourDecimalPlaces
    (timeInSeconds setup.smallOscillationPeriod)
    (displayedPeriodInSeconds choice)

/-!
Uniform-rod inertia, centered endpoint geometry, the linearized spring torque,
and the generic oscillator law imply

`T = 2π sqrt (m / (3k))`.

The rod length cancels between `I = mL²/12` and `κ = k(L/2)²`.  No hypothesis
contains this closed form.
-/
lemma smallOscillationPeriod_formula
    (setup : CenterPivotedRodSpringSetup)
    (hPhysical : HasPhysicalRodSpringParameters setup)
    (hInertia : SatisfiesUniformRodInertiaLaw setup)
    (hGeometry : SatisfiesCenteredEndpointGeometry setup)
    (hLinearized : SatisfiesLinearizedRodSpringLaws setup)
    (hOscillation :
      SatisfiesIdealSmallOscillationLaw setup hPhysical) :
    ∀ (massUnit : MassUnit) (timeUnit : TimeUnit),
      timeReadout timeUnit setup.smallOscillationPeriod =
        2 * Real.pi * Real.sqrt
          (massReadout massUnit setup.rodMass /
            (3 * springConstantReadout massUnit timeUnit
              setup.springConstant)) := by
  intro massUnit timeUnit
  let lengthUnit : LengthUnit := .meters
  have hmpos := hPhysical.rodMassPositive massUnit
  have hLpos := hPhysical.rodLengthPositive lengthUnit
  have hIpos := hPhysical.momentOfInertiaPositive massUnit lengthUnit
  have hκpos :=
    hPhysical.restoringCoefficientPositive massUnit lengthUnit timeUnit
  have hkpos := hPhysical.springConstantPositive massUnit timeUnit
  have hInertiaReadout :=
    hInertia.uniformRodInertia massUnit lengthUnit
  have hLeverArm := hGeometry.endpointLeverArmIsHalfLength lengthUnit
  have hRestoringReadout :=
    restoringCoefficient_readout setup hPhysical hLinearized
      massUnit lengthUnit timeUnit
  have hRatio :
      restoringCoefficientReadout massUnit lengthUnit timeUnit
          setup.linearizedRestoringCoefficient /
          momentOfInertiaReadout massUnit lengthUnit
            setup.momentOfInertiaAboutAxis =
        3 * springConstantReadout massUnit timeUnit setup.springConstant /
          massReadout massUnit setup.rodMass := by
    rw [hRestoringReadout, hLeverArm, hInertiaReadout]
    field_simp [hmpos.ne', hLpos.ne']
    all_goals ring
  rw [hOscillation.periodFromAngularFrequency massUnit lengthUnit timeUnit]
  change
    2 * Real.pi /
        Real.sqrt
          (restoringCoefficientReadout massUnit lengthUnit timeUnit
              setup.linearizedRestoringCoefficient /
            momentOfInertiaReadout massUnit lengthUnit
              setup.momentOfInertiaAboutAxis) =
      2 * Real.pi *
        Real.sqrt
          (massReadout massUnit setup.rodMass /
            (3 * springConstantReadout massUnit timeUnit
              setup.springConstant))
  rw [hRatio, div_eq_mul_inv]
  congr 1
  calc
    (Real.sqrt
        (3 * springConstantReadout massUnit timeUnit setup.springConstant /
          massReadout massUnit setup.rodMass))⁻¹ =
        Real.sqrt
          (3 * springConstantReadout massUnit timeUnit setup.springConstant /
            massReadout massUnit setup.rodMass)⁻¹ := by
          rw [Real.sqrt_inv]
    _ = Real.sqrt
          (massReadout massUnit setup.rodMass /
            (3 * springConstantReadout massUnit timeUnit
              setup.springConstant)) := by
          congr 1
          field_simp [hmpos.ne', hkpos.ne']

/-!
With `m = 0.600 kg` and `k = 1850 N/m`, the formula above gives approximately
`0.0653 s`, the value printed as choice `C`.

This is the formal target corresponding to
`thm:physics:phyx_mini_0268:target`.
-/
theorem problem_phyx_mini_0268
    (setup : CenterPivotedRodSpringSetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalRodSpringParameters setup)
    (hInertia : SatisfiesUniformRodInertiaLaw setup)
    (hGeometry : SatisfiesCenteredEndpointGeometry setup)
    (hLinearized : SatisfiesLinearizedRodSpringLaws setup)
    (hOscillation :
      SatisfiesIdealSmallOscillationLaw setup hPhysical) :
    (∀ (massUnit : MassUnit) (timeUnit : TimeUnit),
      timeReadout timeUnit setup.smallOscillationPeriod =
        2 * Real.pi * Real.sqrt
          (massReadout massUnit setup.rodMass /
            (3 * springConstantReadout massUnit timeUnit
              setup.springConstant))) ∧
      MatchesAnswerChoice setup .C := by
  constructor
  · exact smallOscillationPeriod_formula setup hPhysical hInertia hGeometry
      hLinearized hOscillation
  · have hmass := hReadouts.rodMassKilograms
    change
      massReadout MassUnit.kilograms setup.rodMass = 0.600 at hmass
    have hspring := hReadouts.springConstantNewtonsPerMeter
    change
      springConstantReadout MassUnit.kilograms TimeUnit.seconds
        setup.springConstant = 1850 at hspring
    rw [MatchesAnswerChoice, RoundsToFourDecimalPlaces, timeInSeconds,
      smallOscillationPeriod_formula setup hPhysical hInertia hGeometry
        hLinearized hOscillation MassUnit.kilograms TimeUnit.seconds,
      hmass, hspring]
    norm_num [displayedPeriodInSeconds]
    have hpiLower : (3.14 : ℝ) < Real.pi := by
      have hsin_lt {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
          Real.sin x < x := by
        have habs : |x| = x := abs_of_nonneg hx.le
        have hbound := (abs_le.mp
          (Real.sin_bound (x := x) (by rw [habs]; exact hx1))).2
        rw [habs] at hbound
        have hpoly : 0 ≤ x ^ 3 * (1 - x) :=
          mul_nonneg (pow_nonneg hx.le 3) (sub_nonneg.mpr hx1)
        have hpow : 0 < x ^ 3 := pow_pos hx 3
        nlinarith
      have hs1 : Real.sqrt (2 + (0 : ℝ)) ≤ (338 : ℝ) / 239 := by
        rw [Real.sqrt_le_iff]
        norm_num
      have hs2 : Real.sqrt (2 + (338 : ℝ) / 239) ≤
          (704 : ℝ) / 381 := by
        rw [Real.sqrt_le_iff]
        norm_num
      have hs3 : Real.sqrt (2 + (704 : ℝ) / 381) ≤
          (1940 : ℝ) / 989 := by
        rw [Real.sqrt_le_iff]
        norm_num
      have hs4 : Real.sqrt (2 + (1940 : ℝ) / 989) ≤
          (1447 : ℝ) / 727 := by
        rw [Real.sqrt_le_iff]
        norm_num
      have hseries : Real.sqrtTwoAddSeries 0 4 ≤ (1447 : ℝ) / 727 := by
        calc
          Real.sqrtTwoAddSeries 0 4 =
              Real.sqrtTwoAddSeries (Real.sqrt (2 + 0)) 3 :=
            Real.sqrtTwoAddSeries_succ 0 3
          _ ≤ Real.sqrtTwoAddSeries ((338 : ℝ) / 239) 3 :=
            Real.sqrtTwoAddSeries_monotone_left hs1 3
          _ = Real.sqrtTwoAddSeries
              (Real.sqrt (2 + (338 : ℝ) / 239)) 2 :=
            Real.sqrtTwoAddSeries_succ ((338 : ℝ) / 239) 2
          _ ≤ Real.sqrtTwoAddSeries ((704 : ℝ) / 381) 2 :=
            Real.sqrtTwoAddSeries_monotone_left hs2 2
          _ = Real.sqrtTwoAddSeries
              (Real.sqrt (2 + (704 : ℝ) / 381)) 1 :=
            Real.sqrtTwoAddSeries_succ ((704 : ℝ) / 381) 1
          _ ≤ Real.sqrtTwoAddSeries ((1940 : ℝ) / 989) 1 :=
            Real.sqrtTwoAddSeries_monotone_left hs3 1
          _ = Real.sqrtTwoAddSeries
              (Real.sqrt (2 + (1940 : ℝ) / 989)) 0 :=
            Real.sqrtTwoAddSeries_succ ((1940 : ℝ) / 989) 0
          _ ≤ Real.sqrtTwoAddSeries ((1447 : ℝ) / 727) 0 :=
            Real.sqrtTwoAddSeries_monotone_left hs4 0
          _ = (1447 : ℝ) / 727 := by simp
      have hrad : (3.14 : ℝ) / 32 <
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num at hseries ⊢
        linarith
      have hsinLower : (3.14 : ℝ) / 64 <
          Real.sin (Real.pi / 64) := by
        rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
          Real.sin_pi_over_two_pow_succ]
        nlinarith
      have hpiDivPos : 0 < Real.pi / 64 := by positivity
      have hpiDivLeOne : Real.pi / 64 ≤ 1 := by
        linarith [Real.pi_le_four]
      have hsinUpper := hsin_lt hpiDivPos hpiDivLeOne
      linarith
    have hpiUpper : Real.pi < (3.1416 : ℝ) := by
      have hsin_gt_sub_cube {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
          x - x ^ 3 / 4 < Real.sin x := by
        have habs : |x| = x := abs_of_nonneg hx.le
        have hbound := (abs_le.mp
          (Real.sin_bound (x := x) (by rw [habs]; exact hx1))).1
        rw [habs] at hbound
        have hpoly : 0 ≤ x ^ 3 * (1 - x) :=
          mul_nonneg (pow_nonneg hx.le 3) (sub_nonneg.mpr hx1)
        have hpow : 0 < x ^ 3 := pow_pos hx 3
        nlinarith
      have hstepDown {x y z : ℝ} {n : ℕ}
          (hz : z ≤ Real.sqrtTwoAddSeries x n)
          (hxy : x ≤ Real.sqrt (2 + y)) :
          z ≤ Real.sqrtTwoAddSeries y (n + 1) := by
        calc
          z ≤ Real.sqrtTwoAddSeries x n := hz
          _ ≤ Real.sqrtTwoAddSeries (Real.sqrt (2 + y)) n :=
            Real.sqrtTwoAddSeries_monotone_left hxy n
          _ = Real.sqrtTwoAddSeries y (n + 1) :=
            (Real.sqrtTwoAddSeries_succ y n).symm
      let z : ℝ :=
        2 - (((3.1416 : ℝ) - 1 / (4 : ℝ) ^ 9) /
          (2 : ℝ) ^ 10) ^ 2
      have hr1 : (4756 : ℝ) / 3363 ≤ Real.sqrt (2 + 0) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr2 : (14965 : ℝ) / 8099 ≤
          Real.sqrt (2 + (4756 : ℝ) / 3363) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr3 : (21183 : ℝ) / 10799 ≤
          Real.sqrt (2 + (14965 : ℝ) / 8099) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr4 : (49188 : ℝ) / 24713 ≤
          Real.sqrt (2 + (21183 : ℝ) / 10799) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr5 : (2 : ℝ) - 53 / 22000 ≤
          Real.sqrt (2 + (49188 : ℝ) / 24713) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr6 : (2 : ℝ) - 71 / 117869 ≤
          Real.sqrt (2 + ((2 : ℝ) - 53 / 22000)) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr7 : (2 : ℝ) - 47 / 312092 ≤
          Real.sqrt (2 + ((2 : ℝ) - 71 / 117869)) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr8 : (2 : ℝ) - 17 / 451533 ≤
          Real.sqrt (2 + ((2 : ℝ) - 47 / 312092)) := by
        rw [Real.le_sqrt] <;> norm_num
      have hr9 : (2 : ℝ) - 4 / 424971 ≤
          Real.sqrt (2 + ((2 : ℝ) - 17 / 451533)) := by
        rw [Real.le_sqrt] <;> norm_num
      have hz0 :
          z ≤ Real.sqrtTwoAddSeries ((2 : ℝ) - 4 / 424971) 0 := by
        dsimp [z]
        norm_num [Real.sqrtTwoAddSeries]
      have hz1 := hstepDown hz0 hr9
      have hz2 := hstepDown hz1 hr8
      have hz3 := hstepDown hz2 hr7
      have hz4 := hstepDown hz3 hr6
      have hz5 := hstepDown hz4 hr5
      have hz6 := hstepDown hz5 hr4
      have hz7 := hstepDown hz6 hr3
      have hz8 := hstepDown hz7 hr2
      have hseries : z ≤ Real.sqrtTwoAddSeries 0 9 :=
        hstepDown hz8 hr1
      change
        2 - (((3.1416 : ℝ) - 1 / (4 : ℝ) ^ 9) /
            (2 : ℝ) ^ 10) ^ 2 ≤
          Real.sqrtTwoAddSeries 0 9 at hseries
      have hrad : Real.sqrt (2 - Real.sqrtTwoAddSeries 0 9) ≤
          ((3.1416 : ℝ) - 1 / (4 : ℝ) ^ 9) / (2 : ℝ) ^ 10 := by
        rw [Real.sqrt_le_iff]
        constructor
        · norm_num
        · linarith
      have hsinUpper :
          (2 : ℝ) ^ 11 * Real.sin (Real.pi / (2 : ℝ) ^ 11) ≤
            (3.1416 : ℝ) - 1 / (4 : ℝ) ^ 9 := by
        rw [show (11 : ℕ) = 9 + 2 by norm_num,
          Real.sin_pi_over_two_pow_succ]
        norm_num at hrad ⊢
        nlinarith
      have hxpos : 0 < Real.pi / (2 : ℝ) ^ 11 := by positivity
      have hxone : Real.pi / (2 : ℝ) ^ 11 ≤ 1 := by
        linarith [Real.pi_le_four]
      have hsinLower := hsin_gt_sub_cube hxpos hxone
      have hpiCube : Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 :=
        pow_le_pow_left₀ Real.pi_nonneg Real.pi_le_four 3
      have hremainder :
          (2 : ℝ) ^ 11 * ((Real.pi / (2 : ℝ) ^ 11) ^ 3 / 4) ≤
            1 / (4 : ℝ) ^ 9 := by
        norm_num at hpiCube ⊢
        nlinarith
      have hscaled := mul_lt_mul_of_pos_left hsinLower
        (show (0 : ℝ) < 2 ^ 11 by positivity)
      nlinarith
    have hsqrtLower : (0.010397 : ℝ) <
        Real.sqrt (0.600 / (3 * 1850)) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hsqrtUpper : Real.sqrt (0.600 / (3 * 1850)) <
        (0.010398 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hproductLower :
        (3.14 : ℝ) * 0.010397 <
          Real.pi * Real.sqrt (0.600 / (3 * 1850)) :=
      mul_lt_mul_of_nonneg hpiLower hsqrtLower (by norm_num) (by norm_num)
    have hproductUpper :
        Real.pi * Real.sqrt (0.600 / (3 * 1850)) <
          (3.1416 : ℝ) * 0.010398 :=
      mul_lt_mul_of_nonneg hpiUpper hsqrtUpper Real.pi_nonneg
        (Real.sqrt_nonneg _)
    rw [abs_lt]
    constructor <;> norm_num at * <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0268
