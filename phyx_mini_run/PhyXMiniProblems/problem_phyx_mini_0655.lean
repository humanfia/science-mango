import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0655

open Dimension

/-!
# Matter-wave broadening of a falling dust-particle beam

Dust particles of diameter `1.0 μm` and mass `1.0 × 10⁻¹⁵ kg` are released
from rest immediately above a circular `1.0 μm` aperture in a vacuum chamber.
After falling a distance `d`, the particles form a detection circle. The
question asks for the distance at which the modeled matter-wave broadening
increases its diameter by ten percent, from `1.0 μm` to `1.1 μm`.

Lengths, mass, duration, speed, acceleration, momentum magnitude, and action
are unit-independent Physlib quantities. Real numbers occur only as
calibrated readouts, dimensionless ratios, and displayed answer values.

The physical laws are premises separate from the requested distance. The
idealized route used by the recorded answer combines constant-gravity free
fall, `p = m v`, the de Broglie relation `λ p = h`, and a local paraxial
approximation to aperture broadening.

The paraxial approximation is not globalized into an exact linear law.  An
abstract dimensionless response `B` gives the exact modeled broadening at the
operating wavelength-to-aperture ratio `ε = λ / a`.  Its first-order behavior
is recorded by `B(0) = 0` and `B'(0) = 1`, while an explicit remainder bound
controls the use of the linear approximation at the experiment's `ε`.
-/

/-! ## Physical quantities and calibrated readouts -/

/-- The physical dimension of acceleration, length per time squared. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of momentum, mass times length per time. -/
def momentumDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹

/-- The physical dimension of action, or joule-seconds. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical momentum magnitude. -/
abbrev MomentumMagnitudeQuantity : Type :=
  Dimensionful (WithDim momentumDimension NNReal)

/-- A nonnegative physical action, used here for Planck's constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read acceleration in coherent length-per-time-squared units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read momentum in coherent mass-length-per-time units. -/
def momentumReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (momentum : MomentumMagnitudeQuantity) : ℝ :=
  ((momentum {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read action in coherent mass-length-squared-per-time units. -/
def actionReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (action : ActionQuantity) : ℝ :=
  ((action {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Micrometre readout of a physical length. -/
def lengthInMicrometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.micrometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Kilogram-metre-per-second readout of a momentum magnitude. -/
def momentumInKilogramMetersPerSecond
    (momentum : MomentumMagnitudeQuantity) : ℝ :=
  momentumReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds momentum

/-- Joule-second readout of an action quantity. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  actionReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds action

/-!
Physlib supplies the reduced Planck constant `Constants.ℏ` in joule-seconds.
The de Broglie relation below uses the full Planck constant `h = 2πℏ`.
-/
def fullPlanckConstantInJouleSeconds : ℝ :=
  2 * Real.pi * Constants.ℏ.val

/-! ## Scenario roles and primary-figure vocabulary -/

/-- Contents of the chamber surrounding the falling particles. -/
inductive ChamberMedium where
  | vacuum
  | other
  deriving DecidableEq, Repr

/-- Geometry of the opening through which each particle passes. -/
inductive ApertureGeometry where
  | circularHole
  | other
  deriving DecidableEq, Repr

/-- Idealized model used to turn matter-wave spreading into a circle width. -/
inductive BroadeningModel where
  | localParaxialMatterWaveResponse
  | other
  deriving DecidableEq, Repr

/-- Physical objects visibly represented in the supplied diagram. -/
inductive FigureObject where
  | dustParticle
  | horizontalBarrier
  | circularHole
  | shadedPropagationCone
  | detectorSurface
  | detectionCircle
  deriving DecidableEq, Fintype, Repr

/-- Text and symbolic annotations visibly represented in the diagram. -/
inductive FigureLabel where
  | particleDiameterOneMicrometer
  | holeDiameterOneMicrometer
  | detectorDistanceD
  | detectionCircle
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative evidence retained from the primary image. The image shows three
vertically aligned particles, one barely fitting hole, a shaded spreading
cone, and a detector below the barrier. It gives no numerical value for `d`
and does not label a numerical final detection-circle diameter.
-/
structure DustDiffractionFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  visibleParticleCount : ℕ
  particlesAlignedVerticallyAboveHole : Bool
  holeBarelyAccommodatesParticle : Bool
  shadedConeRunsFromHoleToDetector : Bool
  detectorLiesBelowBarrier : Bool
  distanceArrowRunsFromBarrierToDetector : Bool
  circleWidthArrowShownAtDetector : Bool
  containsNumericalDetectorDistance : Bool
  containsNumericalFinalCircleDiameter : Bool

/-!
Independent quantities for the experiment. In particular,
`detectorDistance` is not defined from an answer choice or from the numerical
result requested by the problem.
-/
structure FallingDustDiffractionSetup where
  chamberMedium : ChamberMedium
  apertureGeometry : ApertureGeometry
  broadeningModel : BroadeningModel
  particleMass : MassQuantity
  particleDiameter : LengthQuantity
  apertureDiameter : LengthQuantity
  detectorDistance : LengthQuantity
  classicalDetectionCircleDiameter : LengthQuantity
  quantumDetectionCircleDiameter : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  fallDurationFromAperture : TimeQuantity
  verticalSpeedAtAperture : DimSpeed
  verticalSpeedAtDetector : DimSpeed
  verticalMomentumAtDetector : MomentumMagnitudeQuantity
  deBroglieWavelengthAtDetector : LengthQuantity
  planckConstant : ActionQuantity
  /-- Exact dimensionless broadening response as a function of `λ / a`. -/
  normalizedApertureBroadeningResponse : ℝ → ℝ
  particlesReleasedFromRest : Bool
  everyParticlePassesThroughHole : Bool
  figure : DustDiffractionFigure

/-! ## Scenario, source data, figure evidence, and governing laws -/

/-!
Qualitative scenario information from the prose. Because no release height
above the hole is supplied, the textbook calculation is represented
explicitly by the idealization that the particle's vertical speed is zero at
the aperture plane.
-/
structure MatchesFallingDustScenario
    (setup : FallingDustDiffractionSetup) : Prop where
  chamberIsVacuum : setup.chamberMedium = .vacuum
  openingIsCircular : setup.apertureGeometry = .circularHole
  usesParaxialMatterWaveModel :
    setup.broadeningModel = .localParaxialMatterWaveResponse
  releasedFromRest : setup.particlesReleasedFromRest = true
  restIdealizationAtAperture :
    speedInMetersPerSecond setup.verticalSpeedAtAperture = 0
  everyParticlePassesAperture : setup.everyParticlePassesThroughHole = true
  apertureBarelyFitsParticle :
    lengthInMeters setup.apertureDiameter =
      lengthInMeters setup.particleDiameter

/-!
Numerical quantities stated in the problem, together with their equivalent
SI calibrations. The final `1.1 μm` circle is the observation condition; the
unknown detector distance is absent.
-/
structure MatchesProblemReadouts
    (setup : FallingDustDiffractionSetup) : Prop where
  particleMassKilograms :
    massInKilograms setup.particleMass = 1 / (10 : ℝ) ^ 15
  particleDiameterMicrometers :
    lengthInMicrometers setup.particleDiameter = 1
  particleDiameterMeters :
    lengthInMeters setup.particleDiameter = 1 / (10 : ℝ) ^ 6
  apertureDiameterMicrometers :
    lengthInMicrometers setup.apertureDiameter = 1
  apertureDiameterMeters :
    lengthInMeters setup.apertureDiameter = 1 / (10 : ℝ) ^ 6
  classicalCircleDiameterMicrometers :
    lengthInMicrometers setup.classicalDetectionCircleDiameter = 1
  classicalCircleDiameterMeters :
    lengthInMeters setup.classicalDetectionCircleDiameter = 1 / (10 : ℝ) ^ 6
  quantumCircleDiameterMicrometers :
    lengthInMicrometers setup.quantumDetectionCircleDiameter = 11 / 10
  quantumCircleDiameterMeters :
    lengthInMeters setup.quantumDetectionCircleDiameter = 11 / (10 : ℝ) ^ 7
  tenPercentDiameterIncrease :
    lengthInMeters setup.quantumDetectionCircleDiameter =
      (11 / 10 : ℝ) * lengthInMeters setup.classicalDetectionCircleDiameter

/-!
Standard terrestrial gravity and Planck-constant calibrations used by the
numerical model. Neither field fixes the detector distance.
-/
structure MatchesPhysicalConstantCalibrations
    (setup : FallingDustDiffractionSetup) : Prop where
  terrestrialGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5
  planckConstantCalibration :
    actionInJouleSeconds setup.planckConstant =
      fullPlanckConstantInJouleSeconds

/-- Qualitative and symbolic information read from the supplied raster. -/
structure MatchesSuppliedFigure
    (figure : DustDiffractionFigure) : Prop where
  everyNamedObjectShown : ∀ object, figure.showsObject object = true
  everyNamedLabelShown : ∀ label, figure.showsLabel label = true
  threeParticlesShown : figure.visibleParticleCount = 3
  particlesAreVerticallyAligned :
    figure.particlesAlignedVerticallyAboveHole = true
  holeBarelyFitsParticles : figure.holeBarelyAccommodatesParticle = true
  propagationConeShown : figure.shadedConeRunsFromHoleToDetector = true
  detectorBelowAperture : figure.detectorLiesBelowBarrier = true
  distanceArrowShown : figure.distanceArrowRunsFromBarrierToDetector = true
  detectionWidthArrowShown : figure.circleWidthArrowShownAtDetector = true
  distanceHasNoNumericalReadout :
    figure.containsNumericalDetectorDistance = false
  finalCircleHasNoNumericalImageReadout :
    figure.containsNumericalFinalCircleDiameter = false

/-!
Positivity and ordering conditions selecting the physically meaningful
branch. They do not assign a numerical detector distance.
-/
structure HasPhysicalDustDiffractionParameters
    (setup : FallingDustDiffractionSetup) : Prop where
  particleMassPositive : 0 < massInKilograms setup.particleMass
  particleDiameterPositive : 0 < lengthInMeters setup.particleDiameter
  apertureDiameterPositive : 0 < lengthInMeters setup.apertureDiameter
  detectorDistancePositive : 0 < lengthInMeters setup.detectorDistance
  classicalCircleDiameterPositive :
    0 < lengthInMeters setup.classicalDetectionCircleDiameter
  finalCircleWider :
    lengthInMeters setup.classicalDetectionCircleDiameter <
      lengthInMeters setup.quantumDetectionCircleDiameter
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  fallDurationPositive : 0 < timeInSeconds setup.fallDurationFromAperture
  detectorSpeedPositive :
    0 < speedInMetersPerSecond setup.verticalSpeedAtDetector
  detectorMomentumPositive :
    0 < momentumInKilogramMetersPerSecond setup.verticalMomentumAtDetector
  wavelengthPositive :
    0 < lengthInMeters setup.deBroglieWavelengthAtDetector
  planckConstantPositive : 0 < actionInJouleSeconds setup.planckConstant

/-!
Governing relations for the idealized calculation:

* constant-gravity fall from rest gives `d = g t² / 2` and `v = g t`;
* the detector momentum magnitude is `p = m v`;
* the de Broglie wavelength obeys `λ p = h`;
* an exact normalized response `B(λ/a)` gives the modeled diameter increase;
* `B` has first-order paraxial behavior at zero, with a controlled finite-point
  remainder at the experiment's wavelength-to-aperture ratio.

Thus `B(ε) = ε` is used only to first order near `ε = 0`, not asserted as a
global exact equality.  These general laws contain no numerical value for `d`
and no answer choice.
-/
structure SatisfiesMatterWaveFreeFallLaws
    (setup : FallingDustDiffractionSetup) : Prop where
  freeFallDistanceFromRest :
    lengthInMeters setup.detectorDistance =
      (1 / 2 : ℝ) *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        (timeInSeconds setup.fallDurationFromAperture) ^ 2
  detectorSpeedFromFreeFall :
    speedInMetersPerSecond setup.verticalSpeedAtDetector =
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        timeInSeconds setup.fallDurationFromAperture
  classicalMomentumLaw :
    momentumInKilogramMetersPerSecond setup.verticalMomentumAtDetector =
      massInKilograms setup.particleMass *
        speedInMetersPerSecond setup.verticalSpeedAtDetector
  deBroglieRelation :
    lengthInMeters setup.deBroglieWavelengthAtDetector *
        momentumInKilogramMetersPerSecond setup.verticalMomentumAtDetector =
      actionInJouleSeconds setup.planckConstant
  zeroRatioProducesNoBroadening :
    setup.normalizedApertureBroadeningResponse 0 = 0
  paraxialFirstOrderAtZero :
    HasDerivAt setup.normalizedApertureBroadeningResponse 1 0
  exactBroadeningAtOperatingRatio :
    lengthInMeters setup.quantumDetectionCircleDiameter -
        lengthInMeters setup.classicalDetectionCircleDiameter =
      lengthInMeters setup.detectorDistance *
        setup.normalizedApertureBroadeningResponse
          (lengthInMeters setup.deBroglieWavelengthAtDetector /
            lengthInMeters setup.apertureDiameter)
  wavelengthApertureRatioInParaxialRegime :
    |lengthInMeters setup.deBroglieWavelengthAtDetector /
        lengthInMeters setup.apertureDiameter| ≤ (1 / 1000 : ℝ)
  explicitParaxialRemainderBound :
    |setup.normalizedApertureBroadeningResponse
          (lengthInMeters setup.deBroglieWavelengthAtDetector /
            lengthInMeters setup.apertureDiameter) -
        lengthInMeters setup.deBroglieWavelengthAtDetector /
          lengthInMeters setup.apertureDiameter| ≤
      (lengthInMeters setup.deBroglieWavelengthAtDetector /
        lengthInMeters setup.apertureDiameter) ^ 2

/-! ## Derived distance and answer interpretation -/

/-- The four candidate detector distances printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre value printed beside each answer label. -/
def displayedDistanceInMeters : AnswerChoice → ℝ
  | .A => 400000000000
  | .B => 420000000000
  | .C => 440000000000
  | .D => 460000000000

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed distance is at least as close as every other choice. -/
def IsClosestDisplayedDistance
    (setup : FallingDustDiffractionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |lengthInMeters setup.detectorDistance - displayedDistanceInMeters choice| ≤
      |lengthInMeters setup.detectorDistance - displayedDistanceInMeters other|

/-- The selected choice is the unique closest displayed detector distance. -/
def IsUniqueClosestDisplayedDistance
    (setup : FallingDustDiffractionSetup) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedDistance setup choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedDistance setup other → other = choice

/-!
The explicit response remainder controls the error made when the exact modeled
broadening is replaced by its first-order paraxial term.  This is a derived
conclusion, not a premise field or a definitional expansion.
-/
lemma actualBroadeningWithinParaxialRemainder
    (setup : FallingDustDiffractionSetup)
    (hPhysical : HasPhysicalDustDiffractionParameters setup)
    (hLaws : SatisfiesMatterWaveFreeFallLaws setup) :
    |(lengthInMeters setup.quantumDetectionCircleDiameter -
          lengthInMeters setup.classicalDetectionCircleDiameter) -
        lengthInMeters setup.detectorDistance *
          (lengthInMeters setup.deBroglieWavelengthAtDetector /
            lengthInMeters setup.apertureDiameter)| ≤
      lengthInMeters setup.detectorDistance *
        (lengthInMeters setup.deBroglieWavelengthAtDetector /
          lengthInMeters setup.apertureDiameter) ^ 2 := by
  rw [hLaws.exactBroadeningAtOperatingRatio]
  rw [← mul_sub, abs_mul, abs_of_pos hPhysical.detectorDistancePositive]
  exact mul_le_mul_of_nonneg_left hLaws.explicitParaxialRemainderBound
    hPhysical.detectorDistancePositive.le

/-!
Blueprint: `thm:physics:phyx_mini_0655:target`.

For a diameter increase of `0.1 μm`, a `1.0 μm` aperture, a particle mass of
`10⁻¹⁵ kg`, terrestrial `g`, and `h = 2πℏ`, the first-order central prediction
is approximately `4.46 × 10¹¹ m`.  The explicit remainder contract is strong
enough to place the exact modeled distance strictly between `4.3 × 10¹¹ m`
and `4.5 × 10¹¹ m`.  Hence choice C, `4.4 × 10¹¹ m`, is uniquely closest.

Neither this interval nor the assertion that C is closest occurs in the
scenario, readout, figure, calibration, or law premises.
-/
theorem problem_phyx_mini_0655
    (setup : FallingDustDiffractionSetup)
    (hScenario : MatchesFallingDustScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hConstants : MatchesPhysicalConstantCalibrations setup)
    (hFigure : MatchesSuppliedFigure setup.figure)
    (hPhysical : HasPhysicalDustDiffractionParameters setup)
    (hLaws : SatisfiesMatterWaveFreeFallLaws setup) :
    (430000000000 : ℝ) < lengthInMeters setup.detectorDistance ∧
      lengthInMeters setup.detectorDistance < (450000000000 : ℝ) ∧
      IsUniqueClosestDisplayedDistance setup .C := by
  let d := lengthInMeters setup.detectorDistance
  let t := timeInSeconds setup.fallDurationFromAperture
  let g :=
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  let v := speedInMetersPerSecond setup.verticalSpeedAtDetector
  let m := massInKilograms setup.particleMass
  let p :=
    momentumInKilogramMetersPerSecond setup.verticalMomentumAtDetector
  let l := lengthInMeters setup.deBroglieWavelengthAtDetector
  let a := lengthInMeters setup.apertureDiameter
  let H := actionInJouleSeconds setup.planckConstant
  let r := l / a
  let q := d * r
  have hd : d = (1 / 2 : ℝ) * g * t ^ 2 := by
    simpa [d, g, t] using hLaws.freeFallDistanceFromRest
  have hv : v = g * t := by
    simpa [v, g, t] using hLaws.detectorSpeedFromFreeFall
  have hp : p = m * v := by
    simpa [p, m, v] using hLaws.classicalMomentumLaw
  have hl : l * p = H := by
    simpa [l, p, H] using hLaws.deBroglieRelation
  have hm : m = 1 / (10 : ℝ) ^ 15 := by
    simpa [m] using hReadouts.particleMassKilograms
  have ha : a = 1 / (10 : ℝ) ^ 6 := by
    simpa [a] using hReadouts.apertureDiameterMeters
  have hg : g = 49 / 5 := by
    simpa [g] using hConstants.terrestrialGravity
  have hd_pos : 0 < d := by
    simpa [d] using hPhysical.detectorDistancePositive
  have ht_pos : 0 < t := by
    simpa [t] using hPhysical.fallDurationPositive
  have hl_pos : 0 < l := by
    simpa [l] using hPhysical.wavelengthPositive
  have ha_pos : 0 < a := by
    simpa [a] using hPhysical.apertureDiameterPositive
  have hr_pos : 0 < r := div_pos hl_pos ha_pos
  have hq_pos : 0 < q := mul_pos hd_pos hr_pos
  have hr_upper : r ≤ (1 / 1000 : ℝ) := by
    have hratio := hLaws.wavelengthApertureRatioInParaxialRegime
    change |r| ≤ (1 / 1000 : ℝ) at hratio
    rw [abs_of_pos hr_pos] at hratio
    exact hratio
  have hq_relation : 2 * m * a * q = H * t := by
    calc
      2 * m * a * q = 2 * m * d * l := by
        dsimp [q, r]
        field_simp
      _ = t * (l * p) := by
        rw [hd, hp, hv]
        ring
      _ = H * t := by rw [hl]; ring
  have hrem :=
    actualBroadeningWithinParaxialRemainder setup hPhysical hLaws
  rw [hReadouts.quantumCircleDiameterMeters,
    hReadouts.classicalCircleDiameterMeters] at hrem
  change
    |(11 / (10 : ℝ) ^ 7 - 1 / (10 : ℝ) ^ 6) - q| ≤ d * r ^ 2 at hrem
  have hsmall : d * r ^ 2 ≤ q / 1000 := by
    calc
      d * r ^ 2 = q * r := by simp [q]; ring
      _ ≤ q * (1 / 1000 : ℝ) :=
        mul_le_mul_of_nonneg_left hr_upper hq_pos.le
      _ = q / 1000 := by ring
  have herror : |(1 / (10 : ℝ) ^ 7) - q| ≤ q / 1000 := by
    norm_num at hrem ⊢
    exact hrem.trans hsmall
  have herror' := abs_le.mp herror
  have hPiLower : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hPiUpper : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hH_lower : (6626 / (10 : ℝ) ^ 37) < H := by
    change
      (6626 / (10 : ℝ) ^ 37) <
        actionInJouleSeconds setup.planckConstant
    rw [hConstants.planckConstantCalibration]
    unfold fullPlanckConstantInJouleSeconds Constants.ℏ
    norm_num at hPiLower hPiUpper ⊢
    nlinarith only [hPiLower]
  have hH_upper : H < (6627 / (10 : ℝ) ^ 37) := by
    change
      actionInJouleSeconds setup.planckConstant <
        (6627 / (10 : ℝ) ^ 37)
    rw [hConstants.planckConstantCalibration]
    unfold fullPlanckConstantInJouleSeconds Constants.ℏ
    norm_num at hPiLower hPiUpper ⊢
    nlinarith only [hPiUpper]
  have hHt_lower : (6626 / (10 : ℝ) ^ 37) * t < H * t :=
    mul_lt_mul_of_pos_right hH_lower ht_pos
  have hHt_upper : H * t < (6627 / (10 : ℝ) ^ 37) * t :=
    mul_lt_mul_of_pos_right hH_upper ht_pos
  rw [hm, ha] at hq_relation
  norm_num at hq_relation herror' hHt_lower hHt_upper
  have ht_lower : (300000 : ℝ) < t := by
    nlinarith only [hq_relation, herror'.2, hHt_upper]
  have ht_upper : t < (303000 : ℝ) := by
    nlinarith only [hq_relation, herror'.1, hHt_lower]
  have ht_sq_lower : (300000 : ℝ) ^ 2 < t ^ 2 := by
    nlinarith only [ht_lower]
  have ht_sq_upper : t ^ 2 < (303000 : ℝ) ^ 2 := by
    nlinarith only [ht_pos, ht_upper]
  rw [hg] at hd
  have hd_lower : (430000000000 : ℝ) < d := by
    nlinarith only [hd, ht_sq_lower]
  have hd_upper : d < (450000000000 : ℝ) := by
    nlinarith only [hd, ht_sq_upper]
  change
    (430000000000 : ℝ) < d ∧ d < (450000000000 : ℝ) ∧ _
  refine ⟨hd_lower, hd_upper, ?_⟩
  change
    (∀ other : AnswerChoice,
      |d - displayedDistanceInMeters .C| ≤
        |d - displayedDistanceInMeters other|) ∧
      ∀ other : AnswerChoice,
        (∀ candidate : AnswerChoice,
          |d - displayedDistanceInMeters other| ≤
            |d - displayedDistanceInMeters candidate|) →
        other = .C
  have hCdist :
      |d - (440000000000 : ℝ)| < (10000000000 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith only [hd_lower, hd_upper]
  have hAdist :
      (10000000000 : ℝ) < |d - (400000000000 : ℝ)| := by
    rw [abs_of_pos (by linarith only [hd_lower])]
    linarith only [hd_lower]
  have hBdist :
      (10000000000 : ℝ) < |d - (420000000000 : ℝ)| := by
    rw [abs_of_pos (by linarith only [hd_lower])]
    linarith only [hd_lower]
  have hDdist :
      (10000000000 : ℝ) < |d - (460000000000 : ℝ)| := by
    rw [abs_of_neg (by linarith only [hd_upper])]
    linarith only [hd_upper]
  constructor
  · intro other
    cases other with
    | A =>
        change
          |d - (440000000000 : ℝ)| ≤ |d - (400000000000 : ℝ)|
        exact (lt_trans hCdist hAdist).le
    | B =>
        change
          |d - (440000000000 : ℝ)| ≤ |d - (420000000000 : ℝ)|
        exact (lt_trans hCdist hBdist).le
    | C => exact le_rfl
    | D =>
        change
          |d - (440000000000 : ℝ)| ≤ |d - (460000000000 : ℝ)|
        exact (lt_trans hCdist hDdist).le
  · intro other hother
    cases other with
    | A =>
        exfalso
        have h := hother AnswerChoice.C
        change
          |d - (400000000000 : ℝ)| ≤ |d - (440000000000 : ℝ)| at h
        linarith only [h, hCdist, hAdist]
    | B =>
        exfalso
        have h := hother AnswerChoice.C
        change
          |d - (420000000000 : ℝ)| ≤ |d - (440000000000 : ℝ)| at h
        linarith only [h, hCdist, hBdist]
    | C => rfl
    | D =>
        exfalso
        have h := hother AnswerChoice.C
        change
          |d - (460000000000 : ℝ)| ≤ |d - (440000000000 : ℝ)| at h
        linarith only [h, hCdist, hDdist]

end PhyXMiniProblems.ProblemPhyXMini0655
