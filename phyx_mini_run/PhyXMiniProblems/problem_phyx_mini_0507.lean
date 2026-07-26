import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0507

open Dimension

/-!
# Matter-wave broadening of a falling dust-particle beam

Dust particles of diameter `1.0 μm` and mass `1.0 × 10⁻¹⁵ kg` are released
from rest immediately above a circular `1.0 μm` aperture in a vacuum chamber.
After falling a distance `d`, the particles form a detection circle. The
question asks for the distance at which matter-wave broadening increases the
diameter by ten percent, from `1.0 μm` to `1.1 μm`. The displayed answer is
interpreted as the leading-order paraxial prediction, while the physical
detector distance retains an explicit controlled approximation remainder.

Lengths, mass, duration, speed, acceleration, momentum magnitude, and action
are unit-independent Physlib quantities. Real numbers occur only as
calibrated readouts, dimensionless ratios, and displayed answer values.

The physical laws are premises separate from the requested distance. The route
used by the recorded answer combines constant-gravity free fall, `p = m v`,
the de Broglie relation `λ p = h`, and the first-order paraxial aperture
estimate `d λ / a`. The latter is not asserted as a globally exact identity:
its signed remainder and a relative error bound are part of the model.
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

/-- A signed, unit-independent length, used for an approximation remainder. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

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

/-- Read a signed physical length in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

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

/-- Metre readout of a signed physical length. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters length

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
  | controlledParaxialMatterWaveAtDetectorSpeed
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
  paraxialBroadeningRemainder : SignedLengthQuantity
  paraxialRelativeErrorTolerance : ℝ
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
    setup.broadeningModel = .controlledParaxialMatterWaveAtDetectorSpeed
  paraxialRelativeErrorToleranceNonnegative :
    0 ≤ setup.paraxialRelativeErrorTolerance
  paraxialRelativeErrorToleranceBelowOne :
    setup.paraxialRelativeErrorTolerance < 1
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
* paraxial matter-wave spreading has leading term `d λ / a`;
* a signed remainder closes the exact width balance; and
* the remainder is bounded relative to the leading term.

Thus the first-order approximation is quantitatively controlled rather than
globalized as an exact physical identity. These general laws contain no
numerical value for `d` and no answer choice.
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
  paraxialApertureBroadeningWithRemainder :
    lengthInMeters setup.quantumDetectionCircleDiameter -
        lengthInMeters setup.classicalDetectionCircleDiameter =
      lengthInMeters setup.detectorDistance *
        lengthInMeters setup.deBroglieWavelengthAtDetector /
          lengthInMeters setup.apertureDiameter +
        signedLengthInMeters setup.paraxialBroadeningRemainder
  paraxialRemainderRelativeBound :
    |signedLengthInMeters setup.paraxialBroadeningRemainder| ≤
      setup.paraxialRelativeErrorTolerance *
        |lengthInMeters setup.detectorDistance *
            lengthInMeters setup.deBroglieWavelengthAtDetector /
          lengthInMeters setup.apertureDiameter|

/-! ## Derived distance and answer interpretation -/

/-!
The zero-remainder, leading-order distance estimate obtained by eliminating
fall time, speed, momentum, and wavelength. This is an estimator built from
the measured diameter increase and physical parameters, not a definition of
the actual detector distance or of an answer choice.
-/
def leadingOrderDetectorDistanceEstimateInMeters
    (setup : FallingDustDiffractionSetup) : ℝ :=
  2 *
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
    (((lengthInMeters setup.quantumDetectionCircleDiameter -
          lengthInMeters setup.classicalDetectionCircleDiameter) *
        lengthInMeters setup.apertureDiameter *
        massInKilograms setup.particleMass) /
      actionInJouleSeconds setup.planckConstant) ^ 2

/-- The four candidate detector distances printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre value printed beside each answer label. -/
def displayedDistanceInMeters : AnswerChoice → ℝ
  | .A => 1400000000000
  | .B => 320000000000
  | .C => 440000000000
  | .D => 480000000000

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed distance is at least as close as every other choice. -/
def IsClosestDisplayedDistance
    (distanceEstimateInMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |distanceEstimateInMeters - displayedDistanceInMeters choice| ≤
      |distanceEstimateInMeters - displayedDistanceInMeters other|

/-- The selected choice is the unique closest displayed detector distance. -/
def IsUniqueClosestDisplayedDistance
    (distanceEstimateInMeters : ℝ) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedDistance distanceEstimateInMeters choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedDistance distanceEstimateInMeters other →
        other = choice

/-!
Eliminating fall time, speed, momentum, and wavelength from the exact laws and
the remainder-aware paraxial balance gives

`d = 2 g ((((D_q - D_c) - r) a m) / h)²`.

This is a derived conclusion, not a premise field or a definitional expansion.
-/
lemma detectorDistanceFromMatterWaveBroadening
    (setup : FallingDustDiffractionSetup)
    (hPhysical : HasPhysicalDustDiffractionParameters setup)
    (hLaws : SatisfiesMatterWaveFreeFallLaws setup) :
    lengthInMeters setup.detectorDistance =
      2 *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        ((((lengthInMeters setup.quantumDetectionCircleDiameter -
              lengthInMeters setup.classicalDetectionCircleDiameter) -
            signedLengthInMeters setup.paraxialBroadeningRemainder) *
            lengthInMeters setup.apertureDiameter *
            massInKilograms setup.particleMass) /
          actionInJouleSeconds setup.planckConstant) ^ 2 := by
  have ha : lengthInMeters setup.apertureDiameter ≠ 0 :=
    ne_of_gt hPhysical.apertureDiameterPositive
  have hLambda : lengthInMeters setup.deBroglieWavelengthAtDetector ≠ 0 :=
    ne_of_gt hPhysical.wavelengthPositive
  have hm : massInKilograms setup.particleMass ≠ 0 :=
    ne_of_gt hPhysical.particleMassPositive
  have hg :
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration ≠ 0 :=
    ne_of_gt hPhysical.gravityPositive
  have ht : timeInSeconds setup.fallDurationFromAperture ≠ 0 :=
    ne_of_gt hPhysical.fallDurationPositive
  have hwidth :
      (lengthInMeters setup.quantumDetectionCircleDiameter -
        lengthInMeters setup.classicalDetectionCircleDiameter -
        signedLengthInMeters setup.paraxialBroadeningRemainder) *
          lengthInMeters setup.apertureDiameter =
        lengthInMeters setup.detectorDistance *
          lengthInMeters setup.deBroglieWavelengthAtDetector := by
    have hb := hLaws.paraxialApertureBroadeningWithRemainder
    field_simp [ha] at hb ⊢
    linarith
  have hratio :
      ((lengthInMeters setup.quantumDetectionCircleDiameter -
            lengthInMeters setup.classicalDetectionCircleDiameter -
            signedLengthInMeters setup.paraxialBroadeningRemainder) *
          lengthInMeters setup.apertureDiameter *
          massInKilograms setup.particleMass) /
        actionInJouleSeconds setup.planckConstant =
      timeInSeconds setup.fallDurationFromAperture / 2 := by
    rw [hwidth, ← hLaws.deBroglieRelation, hLaws.classicalMomentumLaw,
      hLaws.detectorSpeedFromFreeFall, hLaws.freeFallDistanceFromRest]
    field_simp [hLambda, hm, hg, ht]
  rw [hratio, hLaws.freeFallDistanceFromRest]
  ring

/-!
The explicit remainder contract controls the difference between the
zero-remainder leading-order estimate and the physical detector distance.
The factor `2η + η²` is the relative error obtained when a leading width is
perturbed by a remainder of relative magnitude at most `η` and the inferred
distance depends quadratically on that width.
-/
lemma leadingOrderDetectorDistanceEstimate_errorBound
    (setup : FallingDustDiffractionSetup)
    (hScenario : MatchesFallingDustScenario setup)
    (hPhysical : HasPhysicalDustDiffractionParameters setup)
    (hLaws : SatisfiesMatterWaveFreeFallLaws setup) :
    |leadingOrderDetectorDistanceEstimateInMeters setup -
        lengthInMeters setup.detectorDistance| ≤
      (2 * setup.paraxialRelativeErrorTolerance +
          setup.paraxialRelativeErrorTolerance ^ 2) *
        lengthInMeters setup.detectorDistance := by
  let W : ℝ :=
    lengthInMeters setup.quantumDetectionCircleDiameter -
      lengthInMeters setup.classicalDetectionCircleDiameter -
      signedLengthInMeters setup.paraxialBroadeningRemainder
  let K : ℝ :=
    lengthInMeters setup.apertureDiameter * massInKilograms setup.particleMass /
      actionInJouleSeconds setup.planckConstant
  let x : ℝ := W * K
  let y : ℝ := signedLengthInMeters setup.paraxialBroadeningRemainder * K
  let eta : ℝ := setup.paraxialRelativeErrorTolerance
  have hWeq : W = lengthInMeters setup.detectorDistance *
      lengthInMeters setup.deBroglieWavelengthAtDetector /
      lengthInMeters setup.apertureDiameter := by
    dsimp [W]
    linarith [hLaws.paraxialApertureBroadeningWithRemainder]
  have hW : 0 < W := by
    rw [hWeq]
    exact div_pos
      (mul_pos hPhysical.detectorDistancePositive hPhysical.wavelengthPositive)
      hPhysical.apertureDiameterPositive
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos
      (mul_pos hPhysical.apertureDiameterPositive hPhysical.particleMassPositive)
      hPhysical.planckConstantPositive
  have hx : 0 ≤ x := (mul_pos hW hK).le
  have heta : 0 ≤ eta :=
    hScenario.paraxialRelativeErrorToleranceNonnegative
  have hrem :
      |signedLengthInMeters setup.paraxialBroadeningRemainder| ≤ eta * |W| := by
    simpa only [eta, hWeq] using hLaws.paraxialRemainderRelativeBound
  have hy : |y| ≤ eta * x := by
    calc
      |y| =
          |signedLengthInMeters setup.paraxialBroadeningRemainder| * K := by
        rw [show y =
          signedLengthInMeters setup.paraxialBroadeningRemainder * K by rfl,
          abs_mul, abs_of_pos hK]
      _ ≤ (eta * |W|) * K := mul_le_mul_of_nonneg_right hrem hK.le
      _ = eta * x := by rw [abs_of_pos hW]; ring
  have hpoly :
      |(x + y) ^ 2 - x ^ 2| ≤ (2 * eta + eta ^ 2) * x ^ 2 := by
    calc
      |(x + y) ^ 2 - x ^ 2| = |2 * x * y + y ^ 2| := by
        congr 1
        ring
      _ ≤ |2 * x * y| + |y ^ 2| := abs_add_le _ _
      _ = 2 * x * |y| + |y| ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_pow]
        norm_num
      _ ≤ 2 * x * (eta * x) + (eta * x) ^ 2 := by gcongr
      _ = (2 * eta + eta ^ 2) * x ^ 2 := by ring
  have hEstimate : leadingOrderDetectorDistanceEstimateInMeters setup =
      2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        (x + y) ^ 2 := by
    unfold leadingOrderDetectorDistanceEstimateInMeters
    dsimp [x, y, W, K]
    congr 2
    ring
  have hd : lengthInMeters setup.detectorDistance =
      2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        x ^ 2 := by
    convert detectorDistanceFromMatterWaveBroadening setup hPhysical hLaws using 1
    · dsimp [x, W, K]
      ring
  have hScale : 0 ≤ 2 *
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration :=
    mul_nonneg (by norm_num) hPhysical.gravityPositive.le
  rw [hEstimate, hd]
  calc
    |2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
            (x + y) ^ 2 -
        2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          x ^ 2| =
        2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          |(x + y) ^ 2 - x ^ 2| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hScale]
    _ ≤ 2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        ((2 * eta + eta ^ 2) * x ^ 2) :=
      mul_le_mul_of_nonneg_left hpoly hScale
    _ = (2 * eta + eta ^ 2) *
        (2 * accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          x ^ 2) := by ring

/-!
Blueprint: `thm:physics:phyx_mini_0507:target`.

For a diameter increase of `0.1 μm`, a `1.0 μm` aperture, a particle mass of
`10⁻¹⁵ kg`, terrestrial `g`, and `h = 2πℏ`, the zero-remainder leading-order
distance estimate is the exact expression below (approximately
`4.46 × 10¹¹ m`). Hence choice C, `4.4 × 10¹¹ m`, is uniquely closest to that
estimate. The actual distance instead satisfies the displayed error bound.

Neither the numerical estimate, the error bound for the inferred distance,
nor the assertion that C is closest occurs in the scenario, readout, figure,
calibration, or law premises.
-/
theorem problem_phyx_mini_0507
    (setup : FallingDustDiffractionSetup)
    (hScenario : MatchesFallingDustScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hConstants : MatchesPhysicalConstantCalibrations setup)
    (hFigure : MatchesSuppliedFigure setup.figure)
    (hPhysical : HasPhysicalDustDiffractionParameters setup)
    (hLaws : SatisfiesMatterWaveFreeFallLaws setup) :
    |leadingOrderDetectorDistanceEstimateInMeters setup -
        lengthInMeters setup.detectorDistance| ≤
        (2 * setup.paraxialRelativeErrorTolerance +
            setup.paraxialRelativeErrorTolerance ^ 2) *
          lengthInMeters setup.detectorDistance ∧
      leadingOrderDetectorDistanceEstimateInMeters setup =
        2 * (49 / 5 : ℝ) *
          (((1 / (10 : ℝ) ^ 7) * (1 / (10 : ℝ) ^ 6) *
              (1 / (10 : ℝ) ^ 15)) /
            fullPlanckConstantInJouleSeconds) ^ 2 ∧
      IsUniqueClosestDisplayedDistance
        (leadingOrderDetectorDistanceEstimateInMeters setup) .C := by
  have hEstimate : leadingOrderDetectorDistanceEstimateInMeters setup =
      2 * (49 / 5 : ℝ) *
        (((1 / (10 : ℝ) ^ 7) * (1 / (10 : ℝ) ^ 6) *
            (1 / (10 : ℝ) ^ 15)) /
          fullPlanckConstantInJouleSeconds) ^ 2 := by
    unfold leadingOrderDetectorDistanceEstimateInMeters
    rw [hConstants.terrestrialGravity, hConstants.planckConstantCalibration,
      hReadouts.quantumCircleDiameterMeters,
      hReadouts.classicalCircleDiameterMeters,
      hReadouts.apertureDiameterMeters, hReadouts.particleMassKilograms]
    norm_num
  have hPiSqUpper : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 :=
    (sq_lt_sq₀ Real.pi_pos.le (by norm_num)).2 Real.pi_lt_d2
  have hLower :
      380000000000 < leadingOrderDetectorDistanceEstimateInMeters setup := by
    rw [hEstimate]
    unfold fullPlanckConstantInJouleSeconds
    norm_num [Constants.ℏ]
    field_simp [Real.pi_ne_zero]
    norm_num at hPiSqUpper
    nlinarith [hPiSqUpper]
  have hUpper :
      leadingOrderDetectorDistanceEstimateInMeters setup < 460000000000 := by
    rw [hEstimate]
    unfold fullPlanckConstantInJouleSeconds
    norm_num [Constants.ℏ]
    field_simp [Real.pi_ne_zero]
    nlinarith [Real.pi_gt_d2]
  refine ⟨leadingOrderDetectorDistanceEstimate_errorBound
      setup hScenario hPhysical hLaws, hEstimate, ?_⟩
  unfold IsUniqueClosestDisplayedDistance IsClosestDisplayedDistance
  have hStrictA :
      |leadingOrderDetectorDistanceEstimateInMeters setup - 440000000000| <
        |leadingOrderDetectorDistanceEstimateInMeters setup -
          1400000000000| := by
    rw [abs_of_nonpos (by linarith :
      leadingOrderDetectorDistanceEstimateInMeters setup - 1400000000000 ≤ 0)]
    rw [abs_lt]
    constructor <;> linarith
  have hStrictB :
      |leadingOrderDetectorDistanceEstimateInMeters setup - 440000000000| <
        |leadingOrderDetectorDistanceEstimateInMeters setup -
          320000000000| := by
    rw [abs_of_nonneg (by linarith :
      0 ≤ leadingOrderDetectorDistanceEstimateInMeters setup - 320000000000)]
    rw [abs_lt]
    constructor <;> linarith
  have hStrictD :
      |leadingOrderDetectorDistanceEstimateInMeters setup - 440000000000| <
        |leadingOrderDetectorDistanceEstimateInMeters setup -
          480000000000| := by
    rw [abs_of_nonpos (by linarith :
      leadingOrderDetectorDistanceEstimateInMeters setup - 480000000000 ≤ 0)]
    rw [abs_lt]
    constructor <;> linarith
  constructor
  · intro other
    cases other with
    | A => exact hStrictA.le
    | B => exact hStrictB.le
    | C => exact le_rfl
    | D => exact hStrictD.le
  · intro other hother
    cases other with
    | A =>
        have hc := hother .C
        exact (not_lt_of_ge hc hStrictA).elim
    | B =>
        have hc := hother .C
        exact (not_lt_of_ge hc hStrictB).elim
    | C => rfl
    | D =>
        have hc := hother .C
        exact (not_lt_of_ge hc hStrictD).elim

end PhyXMiniProblems.ProblemPhyXMini0507
