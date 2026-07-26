import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0269

open Dimension

/-!
# Rotational inertia of a plate coupled to a spring

A metal plate rotates about an axle through its center of mass.  An ideal
spring joins a wall to a point on the rim, a distance `r` from the axle.  A
small rotation therefore extends the spring tangentially and produces a
restoring torque.  The supplied graph gives the period of the resulting
angular simple harmonic motion.

Dimensionful mechanical quantities use Physlib's `Dimensionful` and
`WithDim` types.  Real numbers are used only for coherent SI readouts, signed
dimensionless angles (radians), graph labels in degrees, and displayed answer
values.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed extension along the spring axis. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A spring force constant has dimension force per length, or mass/time². -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed force component along the tangent at the rim attachment. -/
abbrev SignedForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Rotational inertia has dimension mass times length squared. -/
abbrev RotationalInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A signed torque about the axle through the plate's center of mass. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A nonnegative restoring-torque coefficient per dimensionless radian. -/
abbrev RestoringCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Angular velocity has inverse-time dimension because radians are dimensionless. -/
abbrev AngularVelocityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Angular acceleration has inverse-time-squared dimension. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A nonnegative angular frequency. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Meter readout of a signed spring extension. -/
def signedLengthInMeters (extension : SignedLengthQuantity) : ℝ :=
  signedSIReadout extension

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  nonnegativeSIReadout duration

/-- SI readout of a spring constant, numerically in newtons per meter. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  nonnegativeSIReadout springConstant

/-- Newton readout of a signed tangential force. -/
def signedForceInNewtons (force : SignedForceQuantity) : ℝ :=
  signedSIReadout force

/-- Kilogram-meter-squared readout of rotational inertia. -/
def rotationalInertiaInKilogramMetersSquared
    (inertia : RotationalInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Newton-meter readout of a signed torque. -/
def signedTorqueInNewtonMeters (torque : SignedTorqueQuantity) : ℝ :=
  signedSIReadout torque

/-- Newton-meter readout of a restoring-torque coefficient. -/
def restoringCoefficientInNewtonMeters
    (coefficient : RestoringCoefficientQuantity) : ℝ :=
  nonnegativeSIReadout coefficient

/-- Radian-per-second readout of a signed angular velocity. -/
def angularVelocityInRadiansPerSecond
    (velocity : AngularVelocityQuantity) : ℝ :=
  signedSIReadout velocity

/-- Radian-per-second-squared readout of angular acceleration. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationQuantity) : ℝ :=
  signedSIReadout acceleration

/-- Radian-per-second readout of a nonnegative angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Convert a dimensionless radian coordinate to the degree readout used by the graph. -/
def angleInDegrees (angleInRadians : ℝ) : ℝ :=
  angleInRadians * 180 / Real.pi

/-! ## Apparatus and primary-figure labels -/

/-- Material category of the rotating plate. -/
inductive PlateMaterial where
  | metal
  | other
  deriving DecidableEq, Repr

/-- Position of the plate's axle. -/
inductive AxlePlacement where
  | throughCenterOfMass
  | other
  deriving DecidableEq, Repr

/-- Body to which the fixed end of the spring is connected. -/
inductive SpringAnchor where
  | wall
  | other
  deriving DecidableEq, Repr

/-- Position of the moving end of the spring on the plate. -/
inductive SpringAttachment where
  | rimPoint
  | other
  deriving DecidableEq, Repr

/-- Constitutive model used for the spring. -/
inductive SpringForceModel where
  | idealHookean
  | other
  deriving DecidableEq, Repr

/-- Motion regime described by the source. -/
inductive AngularMotionRegime where
  | smallAngleSimpleHarmonic
  | other
  deriving DecidableEq, Repr

/-- Units printed on the time axis of the supplied graph. -/
inductive GraphTimeUnit where
  | milliseconds
  | other
  deriving DecidableEq, Repr

/-- Units printed on the angular-position axis of the supplied graph. -/
inductive GraphAngleUnit where
  | degrees
  | other
  deriving DecidableEq, Repr

/-- Individually visible components and labels in the two-panel source image. -/
inductive FigureComponent where
  | fixedWall
  | coiledSpring
  | metalPlate
  | centralAxleMarker
  | radiusLabelR
  | angularPositionGraph
  | timeScaleLabelTs
  deriving DecidableEq, Repr

/-!
Primary-image data.  The right panel begins at a positive angular maximum and
returns to the next positive maximum at the grid line labelled `t_s`.  Thus
the named separation is a directly read figure quantity, not a value defined
from the requested inertia.
-/
structure SuppliedFigureReadout where
  shows : FigureComponent → Bool
  springHorizontalAtRest : Bool
  radiusToAttachmentPerpendicularToSpringAtRest : Bool
  attachmentDistanceFromCenter : LengthQuantity
  horizontalAxisUnit : GraphTimeUnit
  verticalAxisUnit : GraphAngleUnit
  timeScaleTs : TimeQuantity
  consecutivePositivePeakSeparation : TimeQuantity
  positivePeakAngleDegrees : ℝ
  negativePeakAngleDegrees : ℝ
  angularTraceRadians : TimeQuantity → ℝ

/-!
The independent physical state and response fields.  In particular,
`rotationalInertia`, `restoringCoefficient`, `angularFrequency`, and
`motionPeriod` are independent quantities constrained only by the laws below;
none is defined to equal the requested answer.
-/
structure PlateSpringSetup where
  plateMaterial : PlateMaterial
  axlePlacement : AxlePlacement
  fixedSpringAnchor : SpringAnchor
  movingSpringAttachment : SpringAttachment
  springForceModel : SpringForceModel
  motionRegime : AngularMotionRegime
  springConstant : SpringConstantQuantity
  rimAttachmentRadius : LengthQuantity
  rotationalInertia : RotationalInertiaQuantity
  restoringCoefficient : RestoringCoefficientQuantity
  angularFrequency : AngularFrequencyQuantity
  motionPeriod : TimeQuantity
  smallAngleCutoff : NNReal
  restConfigurationTime : TimeQuantity
  releaseTime : TimeQuantity
  angularPositionRadians : TimeQuantity → ℝ
  angularVelocity : TimeQuantity → AngularVelocityQuantity
  angularAcceleration : TimeQuantity → AngularAccelerationQuantity
  springExtension : TimeQuantity → SignedLengthQuantity
  tangentialSpringForce : TimeQuantity → SignedForceQuantity
  springTorqueAboutAxle : TimeQuantity → SignedTorqueQuantity
  totalTorqueAboutAxle : TimeQuantity → SignedTorqueQuantity
  figure : SuppliedFigureReadout

/-- The interval on which the first-order tangential geometry is assumed. -/
def IsInSmallAngleRegime (setup : PlateSpringSetup) (time : TimeQuantity) : Prop :=
  |setup.angularPositionRadians time| ≤ (setup.smallAngleCutoff : ℝ)

/-! ## Scenario, figure/data readouts, and governing laws -/

/-- Qualitative assumptions stated for the apparatus and motion. -/
def MatchesVerbalScenario (setup : PlateSpringSetup) : Prop :=
  setup.plateMaterial = .metal ∧
    setup.axlePlacement = .throughCenterOfMass ∧
    setup.fixedSpringAnchor = .wall ∧
    setup.movingSpringAttachment = .rimPoint ∧
    setup.springForceModel = .idealHookean ∧
    setup.motionRegime = .smallAngleSimpleHarmonic

/-!
Numerical data and readouts supplied by the statement and primary figure:

* `k = 2000 N/m`;
* `r = 2.5 cm = 1/40 m`;
* release from `7°` and from rest;
* `t_s = 20 ms = 1/50 s`;
* the graph's next positive maximum occurs one `t_s` after the first.

The last item is a period measurement from the graph, not an inertia formula.
-/
structure MatchesProblemAndFigureReadouts (setup : PlateSpringSetup) : Prop where
  springConstantSI :
    springConstantInNewtonsPerMeter setup.springConstant = 2000
  attachmentRadiusMeters :
    lengthInMeters setup.rimAttachmentRadius = 1 / 40
  springInitiallyAtRestLength :
    signedLengthInMeters
      (setup.springExtension setup.restConfigurationTime) = 0
  releaseAngleDegrees :
    angleInDegrees (setup.angularPositionRadians setup.releaseTime) = 7
  releaseAngleNonzero : setup.angularPositionRadians setup.releaseTime ≠ 0
  releaseWithinSmallAngleRegime : IsInSmallAngleRegime setup setup.releaseTime
  releasedFromRest :
    angularVelocityInRadiansPerSecond
      (setup.angularVelocity setup.releaseTime) = 0
  allFigureComponentsShown : ∀ component, setup.figure.shows component = true
  springShownHorizontalAtRest : setup.figure.springHorizontalAtRest = true
  perpendicularRadiusReadout :
    setup.figure.radiusToAttachmentPerpendicularToSpringAtRest = true
  depictedRadiusMatchesSetup :
    lengthInMeters setup.figure.attachmentDistanceFromCenter =
      lengthInMeters setup.rimAttachmentRadius
  graphTimeAxisInMilliseconds :
    setup.figure.horizontalAxisUnit = .milliseconds
  graphAngleAxisInDegrees : setup.figure.verticalAxisUnit = .degrees
  timeScaleSeconds : timeInSeconds setup.figure.timeScaleTs = 1 / 50
  consecutivePeaksSeparatedByTs :
    timeInSeconds setup.figure.consecutivePositivePeakSeparation =
      timeInSeconds setup.figure.timeScaleTs
  positiveGraphPeakDegrees : setup.figure.positivePeakAngleDegrees = 7
  negativeGraphPeakDegrees : setup.figure.negativePeakAngleDegrees = -7
  releaseIsPositiveGraphPeak :
    angleInDegrees (setup.angularPositionRadians setup.releaseTime) =
      setup.figure.positivePeakAngleDegrees
  graphTraceMatchesExperiment :
    ∀ time,
      setup.figure.angularTraceRadians time =
        setup.angularPositionRadians time

/-! Strict positivity and nondegeneracy assumptions for the physical model. -/
structure HasPhysicalPlateSpringParameters (setup : PlateSpringSetup) : Prop where
  attachmentRadiusPositive :
    0 < lengthInMeters setup.rimAttachmentRadius
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant
  rotationalInertiaPositive :
    0 < rotationalInertiaInKilogramMetersSquared setup.rotationalInertia
  restoringCoefficientPositive :
    0 < restoringCoefficientInNewtonMeters setup.restoringCoefficient
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  motionPeriodPositive : 0 < timeInSeconds setup.motionPeriod
  smallAngleCutoffPositive : 0 < (setup.smallAngleCutoff : ℝ)
  smallAngleCutoffBelowRightAngle :
    (setup.smallAngleCutoff : ℝ) < Real.pi / 2

/-!
First-order mechanics for the small angular motion.  The positive angular
direction is chosen to increase the spring length:

* tangential extension is `x = r θ`;
* Hooke's law is `F = -k x`;
* the perpendicular rim lever arm gives `τ = r F`;
* the spring supplies the total axle torque;
* `τ = -κ θ` defines the effective restoring coefficient;
* rotational Newton's law is `I α = τ`.

These are governing laws.  No field solves for `I`, fixes it numerically, or
selects an answer choice.
-/
structure SatisfiesLinearizedPlateSpringLaws (setup : PlateSpringSetup) : Prop where
  tangentialExtensionLaw :
    ∀ time,
      IsInSmallAngleRegime setup time →
        signedLengthInMeters (setup.springExtension time) =
          lengthInMeters setup.rimAttachmentRadius *
            setup.angularPositionRadians time
  hookeLaw :
    ∀ time,
      IsInSmallAngleRegime setup time →
        signedForceInNewtons (setup.tangentialSpringForce time) =
          -springConstantInNewtonsPerMeter setup.springConstant *
            signedLengthInMeters (setup.springExtension time)
  springTorqueLeverArmLaw :
    ∀ time,
      IsInSmallAngleRegime setup time →
        signedTorqueInNewtonMeters (setup.springTorqueAboutAxle time) =
          lengthInMeters setup.rimAttachmentRadius *
            signedForceInNewtons (setup.tangentialSpringForce time)
  totalTorqueIsSpringTorque :
    ∀ time,
      IsInSmallAngleRegime setup time →
        signedTorqueInNewtonMeters (setup.totalTorqueAboutAxle time) =
          signedTorqueInNewtonMeters (setup.springTorqueAboutAxle time)
  restoringCoefficientCharacterization :
    ∀ time,
      IsInSmallAngleRegime setup time →
        signedTorqueInNewtonMeters (setup.totalTorqueAboutAxle time) =
          -restoringCoefficientInNewtonMeters setup.restoringCoefficient *
            setup.angularPositionRadians time
  rotationalNewtonSecondLaw :
    ∀ time,
      IsInSmallAngleRegime setup time →
        rotationalInertiaInKilogramMetersSquared setup.rotationalInertia *
            angularAccelerationInRadiansPerSecondSquared
              (setup.angularAcceleration time) =
          signedTorqueInNewtonMeters (setup.totalTorqueAboutAxle time)

/-!
The scalar equation `I θ'' + κ θ = 0` has the form represented by Physlib's
positive `ClassicalMechanics.HarmonicOscillator`.  The oscillator's `m` slot
is therefore filled by the SI readout of rotational inertia, and its `k` slot
by the SI readout of the restoring-torque coefficient.
-/
def scalarRotationalOscillator
    (setup : PlateSpringSetup)
    (hPhysical : HasPhysicalPlateSpringParameters setup) :
    ClassicalMechanics.HarmonicOscillator where
  m := rotationalInertiaInKilogramMetersSquared setup.rotationalInertia
  k := restoringCoefficientInNewtonMeters setup.restoringCoefficient
  m_pos := hPhysical.rotationalInertiaPositive
  k_pos := hPhysical.restoringCoefficientPositive

/-!
The measured frequency and period agree with Physlib's generic harmonic
oscillator, and one period is the separation of consecutive positive peaks in
the graph.  This predicate contains no expansion of the unknown inertia in
terms of this problem's numerical data.
-/
structure SatisfiesIdealAngularSHMLaw
    (setup : PlateSpringSetup)
    (hPhysical : HasPhysicalPlateSpringParameters setup) : Prop where
  angularFrequencyFromOscillator :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      (scalarRotationalOscillator setup hPhysical).ω
  periodFromOscillator :
    timeInSeconds setup.motionPeriod =
      ClassicalMechanics.HarmonicOscillator.period
        (scalarRotationalOscillator setup hPhysical)
  periodIsConsecutivePositivePeakSeparation :
    timeInSeconds setup.motionPeriod =
      timeInSeconds setup.figure.consecutivePositivePeakSeparation

/-! ## Derived inertia and displayed answer -/

/-!
The figure geometry, small-angle extension, Hooke force, and lever-arm torque
imply the intermediate relation `κ = k r²`.  It remains a conclusion rather
than a law field because it combines several independently stated laws.
-/
lemma restoringCoefficient_formula
    (setup : PlateSpringSetup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_laws : SatisfiesLinearizedPlateSpringLaws setup) :
    restoringCoefficientInNewtonMeters setup.restoringCoefficient =
      springConstantInNewtonsPerMeter setup.springConstant *
        (lengthInMeters setup.rimAttachmentRadius) ^ 2 := by
  have hExtension :=
    _laws.tangentialExtensionLaw setup.releaseTime
      _readouts.releaseWithinSmallAngleRegime
  have hForce :=
    _laws.hookeLaw setup.releaseTime
      _readouts.releaseWithinSmallAngleRegime
  have hSpringTorque :=
    _laws.springTorqueLeverArmLaw setup.releaseTime
      _readouts.releaseWithinSmallAngleRegime
  have hTotalTorque :=
    _laws.totalTorqueIsSpringTorque setup.releaseTime
      _readouts.releaseWithinSmallAngleRegime
  have hRestoring :=
    _laws.restoringCoefficientCharacterization setup.releaseTime
      _readouts.releaseWithinSmallAngleRegime
  have hRelation :
      -restoringCoefficientInNewtonMeters setup.restoringCoefficient *
            setup.angularPositionRadians setup.releaseTime =
        lengthInMeters setup.rimAttachmentRadius *
          (-springConstantInNewtonsPerMeter setup.springConstant *
            (lengthInMeters setup.rimAttachmentRadius *
              setup.angularPositionRadians setup.releaseTime)) := by
    calc
      _ = signedTorqueInNewtonMeters
            (setup.totalTorqueAboutAxle setup.releaseTime) := hRestoring.symm
      _ = signedTorqueInNewtonMeters
            (setup.springTorqueAboutAxle setup.releaseTime) := hTotalTorque
      _ = lengthInMeters setup.rimAttachmentRadius *
            signedForceInNewtons
              (setup.tangentialSpringForce setup.releaseTime) := hSpringTorque
      _ = lengthInMeters setup.rimAttachmentRadius *
            (-springConstantInNewtonsPerMeter setup.springConstant *
              signedLengthInMeters
                (setup.springExtension setup.releaseTime)) := by rw [hForce]
      _ = _ := by rw [hExtension]
  have hCancelled :
      (restoringCoefficientInNewtonMeters setup.restoringCoefficient -
          springConstantInNewtonsPerMeter setup.springConstant *
            (lengthInMeters setup.rimAttachmentRadius) ^ 2) *
        setup.angularPositionRadians setup.releaseTime = 0 := by
    nlinarith
  exact sub_eq_zero.mp <|
    (mul_eq_zero.mp hCancelled).resolve_right _readouts.releaseAngleNonzero

/-!
For `κ = k r²` and `T = 2π sqrt(I/κ)`, the rotational inertia is

`I = k r² T² / (4π²)`.

This is the exact physical relation inferred from the spring and graph; no
hypothesis above contains it.
-/
lemma rotationalInertia_exact
    (setup : PlateSpringSetup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_physical : HasPhysicalPlateSpringParameters setup)
    (_linearized : SatisfiesLinearizedPlateSpringLaws setup)
    (_shm : SatisfiesIdealAngularSHMLaw setup _physical) :
    rotationalInertiaInKilogramMetersSquared setup.rotationalInertia =
      springConstantInNewtonsPerMeter setup.springConstant *
          (lengthInMeters setup.rimAttachmentRadius) ^ 2 *
          (timeInSeconds setup.motionPeriod) ^ 2 /
        (4 * Real.pi ^ 2) := by
  let oscillator := scalarRotationalOscillator setup _physical
  have hPeriod :
      timeInSeconds setup.motionPeriod =
        2 * Real.pi / oscillator.ω := by
    rw [_shm.periodFromOscillator]
    rfl
  have hFrequencySq :
      oscillator.ω ^ 2 =
        restoringCoefficientInNewtonMeters setup.restoringCoefficient /
          rotationalInertiaInKilogramMetersSquared setup.rotationalInertia := by
    simpa [oscillator, scalarRotationalOscillator] using oscillator.ω_sq
  have hFrequencyNe : oscillator.ω ≠ 0 := oscillator.ω_ne_zero
  have hInertiaNe :
      rotationalInertiaInKilogramMetersSquared setup.rotationalInertia ≠ 0 :=
    _physical.rotationalInertiaPositive.ne'
  have hRestoring :=
    restoringCoefficient_formula setup _readouts _linearized
  have hFrequencySq' :
      oscillator.ω ^ 2 =
        (springConstantInNewtonsPerMeter setup.springConstant *
            (lengthInMeters setup.rimAttachmentRadius) ^ 2) /
          rotationalInertiaInKilogramMetersSquared setup.rotationalInertia := by
    calc
      _ = restoringCoefficientInNewtonMeters setup.restoringCoefficient /
            rotationalInertiaInKilogramMetersSquared setup.rotationalInertia :=
        hFrequencySq
      _ = _ := by rw [hRestoring]
  have hFrequencySq'' :
      oscillator.ω ^ 2 *
          rotationalInertiaInKilogramMetersSquared setup.rotationalInertia =
        springConstantInNewtonsPerMeter setup.springConstant *
          (lengthInMeters setup.rimAttachmentRadius) ^ 2 := by
    exact (eq_div_iff hInertiaNe).mp hFrequencySq'
  have hInertiaFromFrequency :
      rotationalInertiaInKilogramMetersSquared setup.rotationalInertia =
        (springConstantInNewtonsPerMeter setup.springConstant *
            (lengthInMeters setup.rimAttachmentRadius) ^ 2) /
          oscillator.ω ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hFrequencyNe)).mpr
    simpa [mul_comm] using hFrequencySq''
  calc
    _ = (springConstantInNewtonsPerMeter setup.springConstant *
            (lengthInMeters setup.rimAttachmentRadius) ^ 2) /
          oscillator.ω ^ 2 := hInertiaFromFrequency
    _ = springConstantInNewtonsPerMeter setup.springConstant *
          (lengthInMeters setup.rimAttachmentRadius) ^ 2 *
          (2 * Real.pi / oscillator.ω) ^ 2 /
        (4 * Real.pi ^ 2) := by
      field_simp [hFrequencyNe, Real.pi_ne_zero]
      ring
    _ = _ := by rw [← hPeriod]

/-- Labels of the four rotational-inertia choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed rotational inertia for each choice, in `kg · m²`. -/
def displayedInertiaInKilogramMetersSquared : AnswerChoice → ℝ
  | .A => 8 / 1000000
  | .B => 10 / 1000000
  | .C => 13 / 1000000
  | .D => 16 / 1000000

/-- The dataset's recorded answer label; metadata, not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A listed choice is uniquely closest to the exact inferred SI value.  This
models the rounding implicit in a multiple-choice answer instead of falsely
asserting that the irrational exact value is equal to a displayed decimal.
-/
def IsUniqueClosestAnswer
    (setup : PlateSpringSetup) (choice : AnswerChoice) : Prop :=
  ∀ other,
    other ≠ choice →
      |rotationalInertiaInKilogramMetersSquared setup.rotationalInertia -
          displayedInertiaInKilogramMetersSquared choice| <
        |rotationalInertiaInKilogramMetersSquared setup.rotationalInertia -
          displayedInertiaInKilogramMetersSquared other|

/-!
The apparatus laws and graph readout imply the exact inertia formula, and with
`k = 2000 N/m`, `r = 2.5 cm`, and `T = 20 ms`, choice `C` is the unique
closest displayed value (`1.3 × 10⁻⁵ kg · m²`).

This is the formal target corresponding to
`thm:physics:phyx_mini_0269:target`.
-/
theorem problem_phyx_mini_0269
    (setup : PlateSpringSetup)
    (_scenario : MatchesVerbalScenario setup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_physical : HasPhysicalPlateSpringParameters setup)
    (_linearized : SatisfiesLinearizedPlateSpringLaws setup)
    (_shm : SatisfiesIdealAngularSHMLaw setup _physical) :
    (rotationalInertiaInKilogramMetersSquared setup.rotationalInertia =
      springConstantInNewtonsPerMeter setup.springConstant *
          (lengthInMeters setup.rimAttachmentRadius) ^ 2 *
          (timeInSeconds setup.motionPeriod) ^ 2 /
        (4 * Real.pi ^ 2)) ∧
      IsUniqueClosestAnswer setup .C := by
  have hExact :=
    rotationalInertia_exact setup _readouts _physical _linearized _shm
  constructor
  · exact hExact
  · let inertia :=
      rotationalInertiaInKilogramMetersSquared setup.rotationalInertia
    have hPeriod : timeInSeconds setup.motionPeriod = 1 / 50 := by
      calc
        _ = timeInSeconds setup.figure.consecutivePositivePeakSeparation :=
          _shm.periodIsConsecutivePositivePeakSeparation
        _ = timeInSeconds setup.figure.timeScaleTs :=
          _readouts.consecutivePeaksSeparatedByTs
        _ = _ := _readouts.timeScaleSeconds
    have hValue : inertia = 1 / (8000 * Real.pi ^ 2) := by
      dsimp [inertia]
      rw [hExact, _readouts.springConstantSI,
        _readouts.attachmentRadiusMeters, hPeriod]
      ring
    have hDenominatorPositive : 0 < (8000 : ℝ) * Real.pi ^ 2 := by
      positivity
    have hPiSquareLower : ((314 : ℝ) / 100) ^ 2 < Real.pi ^ 2 := by
      have hPiLower := Real.pi_gt_d2
      norm_num at hPiLower
      have hProduct :
          0 < (Real.pi - (314 : ℝ) / 100) *
            (Real.pi + (314 : ℝ) / 100) := by
        apply mul_pos
        · apply sub_pos.mpr
          norm_num at hPiLower ⊢
          exact hPiLower
        · positivity
      nlinarith
    have hPiSquareUpper : Real.pi ^ 2 < ((315 : ℝ) / 100) ^ 2 := by
      have hPiUpper := Real.pi_lt_d2
      norm_num at hPiUpper
      have hProduct :
          0 < ((315 : ℝ) / 100 - Real.pi) *
            ((315 : ℝ) / 100 + Real.pi) := by
        apply mul_pos
        · apply sub_pos.mpr
          norm_num at hPiUpper ⊢
          exact hPiUpper
        · positivity
      nlinarith
    have hLower : (23 : ℝ) / 2000000 < inertia := by
      rw [hValue, lt_div_iff₀ hDenominatorPositive]
      nlinarith [hPiSquareUpper]
    have hUpper : inertia < (13 : ℝ) / 1000000 := by
      rw [hValue, div_lt_iff₀ hDenominatorPositive]
      nlinarith [hPiSquareLower]
    unfold IsUniqueClosestAnswer
    intro other hOther
    cases other with
    | A =>
        change |inertia - 13 / 1000000| < |inertia - 8 / 1000000|
        have hAboveA : (8 : ℝ) / 1000000 < inertia := by
          linarith
        rw [abs_of_neg (sub_neg.mpr hUpper),
          abs_of_pos (sub_pos.mpr hAboveA)]
        linarith
    | B =>
        change |inertia - 13 / 1000000| < |inertia - 10 / 1000000|
        have hAboveB : (10 : ℝ) / 1000000 < inertia := by
          linarith
        rw [abs_of_neg (sub_neg.mpr hUpper),
          abs_of_pos (sub_pos.mpr hAboveB)]
        linarith
    | C =>
        exact (hOther rfl).elim
    | D =>
        change |inertia - 13 / 1000000| < |inertia - 16 / 1000000|
        have hBelowD : inertia < (16 : ℝ) / 1000000 := by
          linarith
        rw [abs_of_neg (sub_neg.mpr hUpper),
          abs_of_neg (sub_neg.mpr hBelowD)]
        norm_num

end PhyXMiniProblems.ProblemPhyXMini0269
