import Mathlib
import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Solution
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0979

open Dimension

/-!
# Electromagnetically damped motion of a spring-mounted slidewire

A conducting vertical bar closes a horizontal U-shaped rail and can slide along
the rail's horizontal axis.  A spring connects the bar to the wall.  Motion in
a uniform magnetic field directed into the page induces a current, whose
magnetic force opposes the motion.  Thus the mechanical system is a damped
harmonic oscillator.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers occur only at coherent-SI readout boundaries and in the
coordinate model used by Physlib's `DampedHarmonicOscillator` API.

Assumption/target split:

* governing laws: resistance addition, uniform-field calibration, motional
  emf, Ohm's law, the magnetic-force law, viscous magnetic drag, the damped
  oscillator equation and selected trajectory, and the generic underdamped
  exponential amplitude-envelope law;
* previous-part results: none;
* figure/data readouts: the U-shaped rail, moving bar, spring and wall; the
  labels `M`, `R`, `k`, `W`, `x`, and `B`; field crosses into the page; the
  stated SI measurements and release from rest;
* current target conclusion: at `5.00 s`, the amplitude rounds to `5.13 cm`
  (answer B).

The value `5.13 cm` occurs only in the final conclusion.  In particular, it is
not a setup field, data calibration, or governing-law premise.
-/

/-! ## Dimensions, physical quantities, and coherent-SI readouts -/

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has dimension `M L² T⁻¹ C⁻²` (ohm). -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A spring constant has dimension `M T⁻²` (newton per metre). -/
def springConstantDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electromotive force has dimension `M L² T⁻² C⁻¹` (volt). -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current has dimension `C T⁻¹` (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Force has dimension `M L T⁻²` (newton). -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A viscous damping coefficient has dimension `M T⁻¹` (kg/s). -/
def dampingCoefficientDimension : Dimension :=
  M𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassMagnitude : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent elapsed or clock time. -/
abbrev TimeMagnitude : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedMagnitude : Type := DimSpeed

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent spring constant. -/
abbrev SpringConstantMagnitude : Type :=
  Dimensionful (WithDim springConstantDimension NNReal)

/-- A nonnegative, unit-independent electromotive-force magnitude. -/
abbrev ElectromotiveForceMagnitude : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent mechanical damping coefficient. -/
abbrev DampingCoefficientMagnitude : Type :=
  Dimensionful (WithDim dampingCoefficientDimension NNReal)

/-- Read a mass in kilograms. -/
def massInKilograms (mass : MassMagnitude) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a time in seconds. -/
def timeInSeconds (time : TimeMagnitude) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Read a spring constant in newtons per metre. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantMagnitude) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-- Read an electromotive-force magnitude in volts. -/
def electromotiveForceInVolts
    (emf : ElectromotiveForceMagnitude) : ℝ :=
  ((emf UnitChoices.SI).val : ℝ)

/-- Read an electric-current magnitude in amperes. -/
def electricCurrentInAmperes
    (current : ElectricCurrentMagnitude) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read a damping coefficient in kilograms per second. -/
def dampingCoefficientInKilogramsPerSecond
    (coefficient : DampingCoefficientMagnitude) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-! ## Primary-raster vocabulary and apparatus -/

/-- Objects visibly present in image `979.png`. -/
inductive FigureObject where
  | fixedWall
  | spring
  | movingBar
  | uShapedRail
  | magneticFieldCrosses
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels visible in image `979.png`. -/
inductive FigureLabel where
  | massM
  | resistanceR
  | springConstantK
  | railWidthW
  | displacementX
  | magneticFieldB
  deriving DecidableEq, Fintype, Repr

/-- Named directions needed for the top-view geometry. -/
inductive SpatialDirection where
  | positiveX
  | negativeX
  | upwardOnPage
  | downwardOnPage
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Orientation of an object or marked span in the figure. -/
inductive AxisOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-!
Literal qualitative content of the primary raster.  It records labels and
geometry only and contains no amplitude readout.
-/
structure ElectromagneticSpringFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  barOrientation : AxisOrientation
  springAxis : AxisOrientation
  displacementAxis : AxisOrientation
  widthSpanOrientation : AxisOrientation
  fieldMarkerDirection : SpatialDirection
  displacementArrowDirection : SpatialDirection
  barClosesUShapedRail : Bool
  springConnectsWallToBar : Bool
  widthMarksRailSeparation : Bool

/-!
Independent physical quantities and observables for the apparatus.  The
amplitude envelope is an observable indexed by clock time; it is not defined
from the requested answer.
-/
structure ElectromagneticSpringSetup where
  figure : ElectromagneticSpringFigure
  magneticField : Electromagnetism.MagneticField 3
  uniformFieldRegion : Set (Time × Space 3)
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  movingBarMass : MassMagnitude
  movingBarResistance : ResistanceMagnitude
  railResistance : ResistanceMagnitude
  totalCircuitResistance : ResistanceMagnitude
  railWidth : LengthMagnitude
  springConstant : SpringConstantMagnitude
  initialStretch : LengthMagnitude
  initialSpeed : SpeedMagnitude
  releaseTime : TimeMagnitude
  observationTime : TimeMagnitude
  inducedEmfAtSpeed : SpeedMagnitude → ElectromotiveForceMagnitude
  inducedCurrentAtSpeed : SpeedMagnitude → ElectricCurrentMagnitude
  magneticDragForceAtSpeed : SpeedMagnitude → ForceMagnitude
  magneticDampingCoefficient : DampingCoefficientMagnitude
  magneticDragDirectionForPositiveVelocity : SpatialDirection
  initialStretchDirection : SpatialDirection
  railPlaneIsHorizontal : Bool
  barSlidesWithoutFriction : Bool
  railResistanceIsNegligible : Bool
  fieldDirection : SpatialDirection
  oscillator : ClassicalMechanics.DampedHarmonicOscillator
  initialConditions :
    ClassicalMechanics.DampedHarmonicOscillator.InitialConditions
  motionTrajectory : Time → EuclideanSpace ℝ (Fin 1)
  amplitudeEnvelope : TimeMagnitude → LengthMagnitude

/-! ## Figure evidence, scenario, data, and governing laws -/

/-- Every qualitative label and relation directly read from image `979.png`. -/
structure MatchesPrimaryElectromagneticSpringFigure
    (setup : ElectromagneticSpringSetup) : Prop where
  fixedWallShown : setup.figure.showsObject .fixedWall = true
  springShown : setup.figure.showsObject .spring = true
  movingBarShown : setup.figure.showsObject .movingBar = true
  uShapedRailShown : setup.figure.showsObject .uShapedRail = true
  fieldCrossesShown : setup.figure.showsObject .magneticFieldCrosses = true
  massLabelShown : setup.figure.showsLabel .massM = true
  resistanceLabelShown : setup.figure.showsLabel .resistanceR = true
  springConstantLabelShown : setup.figure.showsLabel .springConstantK = true
  widthLabelShown : setup.figure.showsLabel .railWidthW = true
  displacementLabelShown : setup.figure.showsLabel .displacementX = true
  magneticFieldLabelShown : setup.figure.showsLabel .magneticFieldB = true
  barIsVerticalOnPage : setup.figure.barOrientation = .vertical
  springIsHorizontalOnPage : setup.figure.springAxis = .horizontal
  displacementAxisIsHorizontal : setup.figure.displacementAxis = .horizontal
  railWidthIsVerticalOnPage : setup.figure.widthSpanOrientation = .vertical
  crossesMeanIntoPage : setup.figure.fieldMarkerDirection = .intoPage
  positiveDisplacementPointsRight :
    setup.figure.displacementArrowDirection = .positiveX
  barClosesRail : setup.figure.barClosesUShapedRail = true
  springJoinsWallAndBar : setup.figure.springConnectsWallToBar = true
  widthIsRailSeparation : setup.figure.widthMarksRailSeparation = true

/-- Qualitative prose assumptions about the idealized apparatus. -/
structure MatchesElectromagneticSpringScenario
    (setup : ElectromagneticSpringSetup) : Prop where
  horizontalRail : setup.railPlaneIsHorizontal = true
  frictionlessSliding : setup.barSlidesWithoutFriction = true
  negligibleRailResistance : setup.railResistanceIsNegligible = true
  fieldPointsIntoPlane : setup.fieldDirection = .intoPage
  stretchIsAlongPositiveX : setup.initialStretchDirection = .positiveX
  magneticDragOpposesPositiveMotion :
    setup.magneticDragDirectionForPositiveVelocity = .negativeX

/-!
The numerical values stated in the prose, expressed as exact coherent-SI
readouts.  `40.0 cm` and `10.0 cm` are converted to metres.
-/
structure ElectromagneticSpringProblemData
    (setup : ElectromagneticSpringSetup) : Prop where
  barMass : massInKilograms setup.movingBarMass = 6 / 5
  barResistance : resistanceInOhms setup.movingBarResistance = 1 / 2
  negligibleRailResistance : resistanceInOhms setup.railResistance = 0
  railWidth : lengthInMeters setup.railWidth = 2 / 5
  springConstant :
    springConstantInNewtonsPerMeter setup.springConstant = 90
  magneticFieldMagnitude :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 1
  initialStretch : lengthInMeters setup.initialStretch = 1 / 10
  releasedFromRest : speedInMetersPerSecond setup.initialSpeed = 0
  releaseTime : timeInSeconds setup.releaseTime = 0
  observationTime : timeInSeconds setup.observationTime = 5

/-!
Generic physical laws used to derive the damping and amplitude.  None mentions
the answer choice `5.13 cm` or fixes the amplitude at the observation time.
-/
structure ElectromagneticSpringLaws
    (setup : ElectromagneticSpringSetup) : Prop where
  totalResistanceLaw :
    resistanceInOhms setup.totalCircuitResistance =
      resistanceInOhms setup.movingBarResistance +
        resistanceInOhms setup.railResistance
  fieldIsConstant :
    ∀ t₁ p₁ t₂ p₂,
      (t₁, p₁) ∈ setup.uniformFieldRegion →
      (t₂, p₂) ∈ setup.uniformFieldRegion →
      setup.magneticField t₁ p₁ = setup.magneticField t₂ p₂
  uniformFieldMagnitude :
    ∀ t p,
      (t, p) ∈ setup.uniformFieldRegion →
      ‖setup.magneticField t p‖ =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  motionalEmfLaw :
    ∀ speed,
      electromotiveForceInVolts (setup.inducedEmfAtSpeed speed) =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthInMeters setup.railWidth * speedInMetersPerSecond speed
  ohmsLaw :
    ∀ speed,
      electromotiveForceInVolts (setup.inducedEmfAtSpeed speed) =
        electricCurrentInAmperes (setup.inducedCurrentAtSpeed speed) *
          resistanceInOhms setup.totalCircuitResistance
  magneticForceLaw :
    ∀ speed,
      forceInNewtons (setup.magneticDragForceAtSpeed speed) =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          electricCurrentInAmperes (setup.inducedCurrentAtSpeed speed) *
            lengthInMeters setup.railWidth
  viscousDampingLaw :
    ∀ speed,
      forceInNewtons (setup.magneticDragForceAtSpeed speed) =
        dampingCoefficientInKilogramsPerSecond
            setup.magneticDampingCoefficient *
          speedInMetersPerSecond speed
  oscillatorMassCalibration :
    setup.oscillator.m = massInKilograms setup.movingBarMass
  oscillatorSpringCalibration :
    setup.oscillator.k =
      springConstantInNewtonsPerMeter setup.springConstant
  oscillatorDampingCalibration :
    setup.oscillator.γ =
      dampingCoefficientInKilogramsPerSecond
        setup.magneticDampingCoefficient
  motionSatisfiesEquation :
    setup.oscillator.EquationOfMotion setup.motionTrajectory
  selectedTrajectory :
    setup.motionTrajectory =
      setup.oscillator.trajectory setup.initialConditions
  initialPositionMagnitude :
    ‖setup.initialConditions.x₀‖ = lengthInMeters setup.initialStretch
  initialVelocityIsZero : setup.initialConditions.v₀ = 0
  underdampedAmplitudeEnvelope :
    setup.oscillator.IsUnderdamped →
      ∀ t,
        timeInSeconds setup.releaseTime ≤ timeInSeconds t →
        lengthInMeters (setup.amplitudeEnvelope t) =
          lengthInMeters setup.initialStretch *
            Real.exp
              (-setup.oscillator.decayRate *
                (timeInSeconds t - timeInSeconds setup.releaseTime))

/-! ## Derived relations and requested answer -/

/-- The induction laws make the magnetic drag coefficient `B² W² / R`. -/
theorem magneticDampingCoefficient_eq
    (setup : ElectromagneticSpringSetup)
    (data : ElectromagneticSpringProblemData setup)
    (laws : ElectromagneticSpringLaws setup) :
    dampingCoefficientInKilogramsPerSecond
        setup.magneticDampingCoefficient =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude ^ 2 *
        lengthInMeters setup.railWidth ^ 2 /
          resistanceInOhms setup.totalCircuitResistance := by
  have hResistance :
      resistanceInOhms setup.totalCircuitResistance = 1 / 2 := by
    rw [laws.totalResistanceLaw, data.barResistance,
      data.negligibleRailResistance]
    norm_num
  have hEmf := laws.motionalEmfLaw DimSpeed.oneMeterPerSecond
  have hOhm := laws.ohmsLaw DimSpeed.oneMeterPerSecond
  have hForce := laws.magneticForceLaw DimSpeed.oneMeterPerSecond
  have hDamping := laws.viscousDampingLaw DimSpeed.oneMeterPerSecond
  norm_num [speedInMetersPerSecond] at hEmf hOhm hForce hDamping
  rw [data.magneticFieldMagnitude, data.railWidth] at hEmf hForce
  rw [hResistance] at hOhm
  rw [data.magneticFieldMagnitude, data.railWidth, hResistance]
  norm_num at hEmf hOhm hForce hDamping ⊢
  linarith

/-- For the stated apparatus, the magnetic damping coefficient is `0.32 kg/s`. -/
theorem magneticDampingCoefficient_eq_eight_twenty_fifths
    (setup : ElectromagneticSpringSetup)
    (data : ElectromagneticSpringProblemData setup)
    (laws : ElectromagneticSpringLaws setup) :
    dampingCoefficientInKilogramsPerSecond
        setup.magneticDampingCoefficient = 8 / 25 := by
  rw [magneticDampingCoefficient_eq setup data laws,
    data.magneticFieldMagnitude, data.railWidth,
    laws.totalResistanceLaw, data.barResistance,
    data.negligibleRailResistance]
  norm_num

/-- The calibrated oscillator lies in the oscillatory, underdamped regime. -/
theorem oscillator_isUnderdamped
    (setup : ElectromagneticSpringSetup)
    (data : ElectromagneticSpringProblemData setup)
    (laws : ElectromagneticSpringLaws setup) :
    setup.oscillator.IsUnderdamped := by
  rw [ClassicalMechanics.DampedHarmonicOscillator.IsUnderdamped,
    ClassicalMechanics.DampedHarmonicOscillator.discriminant,
    laws.oscillatorDampingCalibration,
    magneticDampingCoefficient_eq_eight_twenty_fifths setup data laws,
    laws.oscillatorMassCalibration, data.barMass,
    laws.oscillatorSpringCalibration, data.springConstant]
  norm_num

/-- The amplitude decay rate `γ/(2M)` is `2/15 s⁻¹`. -/
theorem decayRate_eq_two_fifteenths
    (setup : ElectromagneticSpringSetup)
    (data : ElectromagneticSpringProblemData setup)
    (laws : ElectromagneticSpringLaws setup) :
    setup.oscillator.decayRate = 2 / 15 := by
  rw [ClassicalMechanics.DampedHarmonicOscillator.decayRate,
    laws.oscillatorDampingCalibration,
    magneticDampingCoefficient_eq_eight_twenty_fifths setup data laws,
    laws.oscillatorMassCalibration, data.barMass]
  norm_num

/-- At `5 s`, the model gives the exact amplitude `0.1 exp (-2/3)` metres. -/
theorem amplitude_at_observation_time_eq
    (setup : ElectromagneticSpringSetup)
    (data : ElectromagneticSpringProblemData setup)
    (laws : ElectromagneticSpringLaws setup) :
    lengthInMeters (setup.amplitudeEnvelope setup.observationTime) =
      (1 / 10) * Real.exp (-(2 / 3)) := by
  have hTime :
      timeInSeconds setup.releaseTime ≤
        timeInSeconds setup.observationTime := by
    rw [data.releaseTime, data.observationTime]
    norm_num
  have hEnvelope :=
    laws.underdampedAmplitudeEnvelope
      (oscillator_isUnderdamped setup data laws)
      setup.observationTime hTime
  rw [data.initialStretch,
    decayRate_eq_two_fifteenths setup data laws,
    data.observationTime, data.releaseTime] at hEnvelope
  norm_num at hEnvelope ⊢
  exact hEnvelope

/-!
`RoundsToHundredthCentimeter length n` means that the length, expressed in
centimetres, lies within half of `0.01 cm` of `n / 100` centimetres.
-/
def RoundsToHundredthCentimeter
    (length : LengthMagnitude) (hundredthsOfCentimeter : ℕ) : Prop :=
  |100 * lengthInMeters length - (hundredthsOfCentimeter : ℝ) / 100| <
    1 / 200

/-- The amplitude at `5.00 s` rounds to `5.13 cm`, answer choice B. -/
theorem amplitude_at_five_seconds
    (setup : ElectromagneticSpringSetup)
    (figure : MatchesPrimaryElectromagneticSpringFigure setup)
    (scenario : MatchesElectromagneticSpringScenario setup)
    (data : ElectromagneticSpringProblemData setup)
    (laws : ElectromagneticSpringLaws setup) :
    RoundsToHundredthCentimeter
      (setup.amplitudeEnvelope setup.observationTime) 513 := by
  rw [RoundsToHundredthCentimeter,
    amplitude_at_observation_time_eq setup data laws]
  have hExpLower :
      (2000 / 1027 : ℝ) < Real.exp (2 / 3) := by
    have h := Real.sum_le_exp_of_nonneg
      (x := (2 / 3 : ℝ)) (by norm_num) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hExpUpper :
      Real.exp (2 / 3 : ℝ) < (80 / 41 : ℝ) := by
    have h := Real.exp_bound' (x := (2 / 3 : ℝ))
      (by norm_num) (by norm_num) (n := 8) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hExpNegLower :
      (41 / 80 : ℝ) < Real.exp (-(2 / 3)) := by
    rw [Real.exp_neg]
    have hInverse :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 80 / 41)
        (Real.exp_pos (2 / 3 : ℝ))).2 hExpUpper
    norm_num at hInverse
    exact hInverse
  have hExpNegUpper :
      Real.exp (-(2 / 3)) < (1027 / 2000 : ℝ) := by
    rw [Real.exp_neg]
    have hInverse :=
      (inv_lt_inv₀ (Real.exp_pos (2 / 3 : ℝ))
        (by norm_num : (0 : ℝ) < 2000 / 1027)).2 hExpLower
    norm_num at hInverse
    exact hInverse
  rw [abs_lt]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0979
