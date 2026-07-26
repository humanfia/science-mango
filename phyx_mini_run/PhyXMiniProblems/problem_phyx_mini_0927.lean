import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0927

open Dimension

/-!
# Acceleration of a proton in an electric field induced by a decreasing magnetic field

The primary raster shows a circular region of uniform magnetic field directed
into the page.  The four points `a`, `b`, `c`, and `d` are one centimetre
apart on a horizontal diameter.  In the raster, the radius arrow starts at
`b` and `d` is on the right-hand boundary, so the circle is centered at `b`
and `c` is one centimetre from the center.  This primary-image reading also
agrees with the recorded answer.  The auxiliary caption's claim that `a` is
the center is therefore treated as a caption error.

Physical magnitudes use Physlib's unit-independent
`Dimensionful (WithDim _ _)` representation.  Physlib's electric- and
magnetic-field types retain the spacetime-dependent vector-field roles of the
fields.  Real scalars occur only at named-unit readout boundaries, in printed
figure data, and in displayed answer values.

Assumption/target split:

* governing laws: uniform decrease of the magnetic field, Faraday's law for
  the circular loop through `c`, Lenz's direction rule, the initial Lorentz
  force, and Newton's second law;
* previous-part results: none;
* figure/data readouts: the four point labels, one-centimetre gaps, the
  two-centimetre radius centered at `b`, an into-page field, decrease rate
  `0.10 T/s`, initial rest, and standard proton mass and charge;
* current target conclusions: the induced-field and acceleration formulas,
  and the unique two-significant-figure match to recorded choice B.

None of the current target formulas or answer-matching predicates occurs in a
premise structure.
-/

/-! ## Dimensions, dimensionful quantities, and SI readouts -/

/-- Speed has physical dimension `L T⁻¹`. -/
def speedDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- Acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric-field strength has physical dimension `M L T⁻² C⁻¹`. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A magnetic-flux-density change rate has dimension `M T⁻² C⁻¹`. -/
def magneticFluxDensityRateDimension : Dimension :=
  magneticFluxDensityDimension * T𝓭⁻¹

/-- Magnetic flux per time, equivalently induced emf, has voltage dimension. -/
def magneticFluxRateDimension : Dimension :=
  magneticFluxDensityDimension * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent coordinate along the displayed diameter. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative rate at which a magnetic-flux-density magnitude decreases. -/
abbrev MagneticFluxDensityRateQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityRateDimension NNReal)

/-- A nonnegative magnetic-flux decrease rate through the loop at `c`. -/
abbrev MagneticFluxDecreaseRateQuantity : Type :=
  Dimensionful (WithDim magneticFluxRateDimension NNReal)

/-- A nonnegative induced electromotive-force magnitude. -/
abbrev InducedEmfMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxRateDimension NNReal)

/-- Read a physical length in a selected named unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed length in a selected named unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a signed coordinate in centimetres. -/
def signedLengthInCentimeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.centimeters length

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read an electric-charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read a speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read electric-field strength in volts per metre. -/
def electricFieldStrengthInVoltsPerMeter
    (field : ElectricFieldStrengthQuantity) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-- Read magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityQuantity) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-- Read a magnetic-flux-density change rate in teslas per second. -/
def magneticFluxDensityRateInTeslasPerSecond
    (rate : MagneticFluxDensityRateQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-- Read a magnetic-flux decrease rate in webers per second. -/
def magneticFluxDecreaseRateInWebersPerSecond
    (rate : MagneticFluxDecreaseRateQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-- Read an induced-emf magnitude in volts. -/
def inducedEmfMagnitudeInVolts (emf : InducedEmfMagnitudeQuantity) : ℝ :=
  ((emf UnitChoices.SI).val : ℝ)

/-- Physlib's elementary-charge unit expressed as a number of coulombs. -/
def physlibElementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-- CODATA-style proton mass used for the numerical answer, in kilograms. -/
def protonMassInKilograms : ℝ :=
  167262192595 / (10 : ℝ) ^ 38

/-! ## Physical and primary-raster vocabulary -/

/-- The four labelled points on the horizontal diameter. -/
inductive FigurePoint where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- The three adjacent one-centimetre gaps visible in the raster. -/
inductive AdjacentGap where
  | ab
  | bc
  | cd
  deriving DecidableEq, Fintype, Repr

/-- Particle species distinguished by the problem statement. -/
inductive ParticleSpecies where
  | proton
  | other
  deriving DecidableEq, Repr

/-- Qualitative directions needed to read the crosses and induced circulation. -/
inductive SpatialDirection where
  | intoPage
  | outOfPage
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Sense of circulation about the circle's center as seen in the raster. -/
inductive CirculationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- The standard idealization used by the problem. -/
inductive MagneticFieldModel where
  | spatiallyUniformInsideCircularRegion
  | other
  deriving DecidableEq, Repr

/-!
Literal presentation data from image `927.png`.  The numerical labels are
stored as physical quantities and calibrated below; they are not substitutes
for the underlying lengths.
-/
structure DecreasingMagneticFieldFigure where
  pointShown : FigurePoint → Bool
  printedPointText : FigurePoint → String
  adjacentGapLabel : AdjacentGap → LengthQuantity
  circleRadiusLabel : LengthQuantity
  circleCenterPoint : FigurePoint
  radiusArrowOrigin : FigurePoint
  dashedCircularBoundaryShown : Bool
  crossSymbolsShownInsideCircle : Bool

/-!
Independent physical quantities and observables.  In particular, acceleration,
field strength, flux rate, emf, and force magnitudes are not defined from a
displayed answer or from the requested closed form.
-/
structure ProtonInDecreasingMagneticFieldSetup where
  particleSpecies : ParticleSpecies
  particleMass : MassQuantity
  particleChargeMagnitude : ChargeMagnitudeQuantity
  initialSpeedAtC : SpeedQuantity
  accelerationMagnitudeAtC : AccelerationQuantity
  circleRadius : LengthQuantity
  adjacentPointSpacing : LengthQuantity
  horizontalCoordinateFromCircleCenter : FigurePoint → SignedLengthQuantity
  radialDistanceFromCircleCenter : FigurePoint → LengthQuantity
  magneticFluxDensityMagnitude : ℝ → MagneticFluxDensityQuantity
  magneticFluxDensityDecreaseRate : MagneticFluxDensityRateQuantity
  magneticFluxDecreaseRateThroughCLoop : MagneticFluxDecreaseRateQuantity
  inducedEmfMagnitudeAroundCLoop : InducedEmfMagnitudeQuantity
  inducedElectricFieldStrengthAtC : ElectricFieldStrengthQuantity
  initialElectricForceMagnitude : ForceMagnitudeQuantity
  initialMagneticForceMagnitude : ForceMagnitudeQuantity
  initialNetForceMagnitude : ForceMagnitudeQuantity
  magneticField : Electromagnetism.MagneticField 3
  inducedElectricField : Electromagnetism.ElectricField 3
  fieldDisk : Set (Time × Space 3)
  observationTime : Time
  observationTimeInSeconds : ℝ
  pointPosition : FigurePoint → Space 3
  magneticFieldDirection : SpatialDirection
  inducedCirculationSense : CirculationSense
  inducedElectricFieldDirectionAtC : SpatialDirection
  initialNetForceDirectionAtC : SpatialDirection
  accelerationDirectionAtC : SpatialDirection
  fieldModel : MagneticFieldModel
  figure : DecreasingMagneticFieldFigure

/-! ## Source data, primary-image evidence, and governing laws -/

/-- Qualitative and numerical data explicitly stated in the problem prose. -/
structure MatchesWrittenProblemData
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  particleIsProton : setup.particleSpecies = .proton
  protonInitiallyAtRestAtC :
    speedInMetersPerSecond setup.initialSpeedAtC = 0
  magneticFieldDecreaseRateTeslasPerSecond :
    magneticFluxDensityRateInTeslasPerSecond
        setup.magneticFluxDensityDecreaseRate = 1 / 10

/-!
Primary-raster evidence.  The image places `b` at the circle center: the
radius arrow begins there, `c` is one centimetre to its right, and `d` is two
centimetres to its right on the boundary.
-/
structure MatchesSuppliedDecreasingFieldFigure
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  everyPointShown : ∀ point, setup.figure.pointShown point = true
  labelA : setup.figure.printedPointText .a = "a"
  labelB : setup.figure.printedPointText .b = "b"
  labelC : setup.figure.printedPointText .c = "c"
  labelD : setup.figure.printedPointText .d = "d"
  everyGapLabelIsPhysicalSpacing : ∀ gap,
    setup.figure.adjacentGapLabel gap = setup.adjacentPointSpacing
  printedGapSpacingCentimeters :
    lengthInCentimeters setup.adjacentPointSpacing = 1
  printedRadiusDenotesPhysicalRadius :
    setup.figure.circleRadiusLabel = setup.circleRadius
  printedCircleRadiusCentimeters :
    lengthInCentimeters setup.circleRadius = 2
  circleIsCenteredAtB : setup.figure.circleCenterPoint = .b
  radiusArrowStartsAtB : setup.figure.radiusArrowOrigin = .b
  dashedCircleShown : setup.figure.dashedCircularBoundaryShown = true
  intoPageCrossesShown : setup.figure.crossSymbolsShownInsideCircle = true
  pointACoordinateCentimeters :
    signedLengthInCentimeters
        (setup.horizontalCoordinateFromCircleCenter .a) = -1
  pointBCoordinateCentimeters :
    signedLengthInCentimeters
        (setup.horizontalCoordinateFromCircleCenter .b) = 0
  pointCCoordinateCentimeters :
    signedLengthInCentimeters
        (setup.horizontalCoordinateFromCircleCenter .c) = 1
  pointDCoordinateCentimeters :
    signedLengthInCentimeters
        (setup.horizontalCoordinateFromCircleCenter .d) = 2
  pointCRadiusCentimeters :
    lengthInCentimeters (setup.radialDistanceFromCircleCenter .c) = 1
  pointDOnCircleBoundary :
    setup.radialDistanceFromCircleCenter .d = setup.circleRadius
  pointCIsInsideCircle :
    lengthInMeters (setup.radialDistanceFromCircleCenter .c) <
      lengthInMeters setup.circleRadius
  everyMarkedPointInOrOnFieldDisk : ∀ point,
    (setup.observationTime, setup.pointPosition point) ∈ setup.fieldDisk

/-!
Standard proton reference data.  Physlib supplies the elementary-charge unit;
no packaged proton-mass constant was found, so the mass calibration is stated
explicitly.  Neither calibration mentions acceleration.
-/
structure UsesStandardProtonReferenceData
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  protonMassKilograms :
    massInKilograms setup.particleMass = protonMassInKilograms
  protonChargeMagnitudeCoulombs :
    chargeMagnitudeInCoulombs setup.particleChargeMagnitude =
      physlibElementaryChargeInCoulombs

/-- Positivity and non-vacuity conditions for the physical setup. -/
structure HasPhysicalParameters
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  protonMassPositive : 0 < massInKilograms setup.particleMass
  protonChargePositive :
    0 < chargeMagnitudeInCoulombs setup.particleChargeMagnitude
  circleRadiusPositive : 0 < lengthInMeters setup.circleRadius
  pointCRadiusPositive :
    0 < lengthInMeters (setup.radialDistanceFromCircleCenter .c)
  decreaseRatePositive :
    0 < magneticFluxDensityRateInTeslasPerSecond
      setup.magneticFluxDensityDecreaseRate
  fieldDiskNonempty : setup.fieldDisk.Nonempty

/-!
The crosses denote an into-page field.  Within the dashed disk its magnitude
is spatially uniform, while its scalar magnitude has derivative equal to the
negative of the stated positive decrease rate.  The induced Physlib field is
also calibrated to the independently stored scalar strength at `c`.
-/
structure SatisfiesUniformDecreasingMagneticFieldModel
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  usesUniformCircularFieldModel :
    setup.fieldModel = .spatiallyUniformInsideCircularRegion
  fieldPointsIntoPage : setup.magneticFieldDirection = .intoPage
  magneticMagnitudeUniformInDisk :
    ∀ position,
      (setup.observationTime, position) ∈ setup.fieldDisk →
        ‖setup.magneticField setup.observationTime position‖ =
          magneticFluxDensityInTeslas
            (setup.magneticFluxDensityMagnitude setup.observationTimeInSeconds)
  magneticMagnitudeDecreasesAtStatedRate :
    HasDerivAt
      (fun time =>
        magneticFluxDensityInTeslas
          (setup.magneticFluxDensityMagnitude time))
      (-magneticFluxDensityRateInTeslasPerSecond
        setup.magneticFluxDensityDecreaseRate)
      setup.observationTimeInSeconds
  inducedFieldMagnitudeAtC :
    ‖setup.inducedElectricField setup.observationTime
        (setup.pointPosition .c)‖ =
      electricFieldStrengthInVoltsPerMeter
        setup.inducedElectricFieldStrengthAtC

/-!
Magnitude form of Faraday's law for the circular loop through `c`: uniform
flux gives `π r_c² |dB/dt|`, Faraday equates its decrease rate with induced
emf magnitude, and circular symmetry gives circulation `2 π r_c E_c`.
-/
structure SatisfiesFaradayLawAtC
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  fluxDecreaseRateThroughCLoop :
    magneticFluxDecreaseRateInWebersPerSecond
        setup.magneticFluxDecreaseRateThroughCLoop =
      Real.pi *
        lengthInMeters (setup.radialDistanceFromCircleCenter .c) ^ 2 *
        magneticFluxDensityRateInTeslasPerSecond
          setup.magneticFluxDensityDecreaseRate
  faradayEmfMagnitudeLaw :
    inducedEmfMagnitudeInVolts setup.inducedEmfMagnitudeAroundCLoop =
      magneticFluxDecreaseRateInWebersPerSecond
        setup.magneticFluxDecreaseRateThroughCLoop
  circularElectricFieldCirculation :
    inducedEmfMagnitudeInVolts setup.inducedEmfMagnitudeAroundCLoop =
      2 * Real.pi *
        lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
        electricFieldStrengthInVoltsPerMeter
          setup.inducedElectricFieldStrengthAtC

/-!
Lenz's law fixes clockwise circulation for a decreasing into-page field.  At
`c`, to the right of the center, its tangent points down; a positive proton's
electric force and acceleration have the same direction.
-/
structure SatisfiesLenzAndForceDirectionLaws
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  lenzLawGivesClockwiseCirculation :
    setup.inducedCirculationSense = .clockwise
  clockwiseTangentAtCPointsDown :
    setup.inducedCirculationSense = .clockwise →
      setup.inducedElectricFieldDirectionAtC = .downward
  positiveProtonForceFollowsElectricField :
    setup.initialNetForceDirectionAtC =
      setup.inducedElectricFieldDirectionAtC
  newtonDirectionLaw :
    setup.accelerationDirectionAtC = setup.initialNetForceDirectionAtC

/-!
Initial magnitude form of the Lorentz force and Newton's second law.  The
magnetic term is retained even though initial rest will make it vanish.
-/
structure SatisfiesInitialLorentzForceAndNewtonSecondLaw
    (setup : ProtonInDecreasingMagneticFieldSetup) : Prop where
  electricForceMagnitudeLaw :
    forceMagnitudeInNewtons setup.initialElectricForceMagnitude =
      chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
        electricFieldStrengthInVoltsPerMeter
          setup.inducedElectricFieldStrengthAtC
  magneticForceMagnitudeLaw :
    forceMagnitudeInNewtons setup.initialMagneticForceMagnitude =
      chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
        speedInMetersPerSecond setup.initialSpeedAtC *
        magneticFluxDensityInTeslas
          (setup.magneticFluxDensityMagnitude setup.observationTimeInSeconds)
  netForceMagnitudeLaw :
    forceMagnitudeInNewtons setup.initialNetForceMagnitude =
      forceMagnitudeInNewtons setup.initialElectricForceMagnitude +
        forceMagnitudeInNewtons setup.initialMagneticForceMagnitude
  newtonSecondLaw :
    massInKilograms setup.particleMass *
        accelerationInMetersPerSecondSquared
          setup.accelerationMagnitudeAtC =
      forceMagnitudeInNewtons setup.initialNetForceMagnitude

/-! ## Displayed answers and current target conclusions -/

/-- The four answer labels printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Acceleration magnitude printed beside each choice, in `m/s²`. -/
def AnswerChoice.displayedAccelerationInMetersPerSecondSquared :
    AnswerChoice → ℝ
  | .A => 29 * 10 ^ 3
  | .B => 48 * 10 ^ 3
  | .C => 96 * 10 ^ 3
  | .D => 24 * 10 ^ 3

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
All displayed accelerations have two significant figures.  A half-width of
`500 m/s²` is the rounding interval for the last displayed digit.
-/
def MatchesDisplayedAcceleration
    (setup : ProtonInDecreasingMagneticFieldSetup)
    (choice : AnswerChoice) : Prop :=
  |accelerationInMetersPerSecondSquared setup.accelerationMagnitudeAtC -
      choice.displayedAccelerationInMetersPerSecondSquared| < 500

/-- A choice is the unique displayed rounding match for the physical result. -/
def IsUniqueMatchingDisplayedAcceleration
    (setup : ProtonInDecreasingMagneticFieldSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedAcceleration setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedAcceleration setup other → other = choice

/-!
Faraday's law and circular symmetry give `E_c = r_c |dB/dt| / 2`.
This is a derived result, not a setup field or premise.
-/
lemma inducedElectricFieldAtC_eq_radius_mul_rate_div_two
    (setup : ProtonInDecreasingMagneticFieldSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hFaraday : SatisfiesFaradayLawAtC setup) :
    electricFieldStrengthInVoltsPerMeter
        setup.inducedElectricFieldStrengthAtC =
      lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
          magneticFluxDensityRateInTeslasPerSecond
            setup.magneticFluxDensityDecreaseRate /
        2 := by
  have hRadiusNe :
      lengthInMeters (setup.radialDistanceFromCircleCenter .c) ≠ 0 :=
    ne_of_gt hPhysical.pointCRadiusPositive
  have hPiRadiusNe :
      Real.pi * lengthInMeters (setup.radialDistanceFromCircleCenter .c) ≠ 0 :=
    mul_ne_zero (ne_of_gt Real.pi_pos) hRadiusNe
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  apply (mul_left_cancel₀ hPiRadiusNe)
  calc
    (Real.pi * lengthInMeters (setup.radialDistanceFromCircleCenter .c)) *
          (electricFieldStrengthInVoltsPerMeter
            setup.inducedElectricFieldStrengthAtC * 2) =
        inducedEmfMagnitudeInVolts setup.inducedEmfMagnitudeAroundCLoop := by
          rw [hFaraday.circularElectricFieldCirculation]
          ring
    _ = magneticFluxDecreaseRateInWebersPerSecond
          setup.magneticFluxDecreaseRateThroughCLoop :=
      hFaraday.faradayEmfMagnitudeLaw
    _ = (Real.pi * lengthInMeters
            (setup.radialDistanceFromCircleCenter .c)) *
          (lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
            magneticFluxDensityRateInTeslasPerSecond
              setup.magneticFluxDensityDecreaseRate) := by
          rw [hFaraday.fluxDecreaseRateThroughCLoop]
          ring

/-!
Initial rest makes the magnetic Lorentz term vanish.  Combining the electric
force with Newton's law gives the acceleration formula.
-/
lemma protonAccelerationAtC_eq_charge_mul_radius_mul_rate_div_mass
    (setup : ProtonInDecreasingMagneticFieldSetup)
    (hData : MatchesWrittenProblemData setup)
    (hPhysical : HasPhysicalParameters setup)
    (hFaraday : SatisfiesFaradayLawAtC setup)
    (hDynamics : SatisfiesInitialLorentzForceAndNewtonSecondLaw setup) :
    accelerationInMetersPerSecondSquared setup.accelerationMagnitudeAtC =
      chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
          magneticFluxDensityRateInTeslasPerSecond
            setup.magneticFluxDensityDecreaseRate /
        (2 * massInKilograms setup.particleMass) := by
  have hElectricField :=
    inducedElectricFieldAtC_eq_radius_mul_rate_div_two
      setup hPhysical hFaraday
  have hMagneticForce :
      forceMagnitudeInNewtons setup.initialMagneticForceMagnitude = 0 := by
    rw [hDynamics.magneticForceMagnitudeLaw,
      hData.protonInitiallyAtRestAtC]
    ring
  have hNetForce :
      forceMagnitudeInNewtons setup.initialNetForceMagnitude =
        chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          (lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
            magneticFluxDensityRateInTeslasPerSecond
              setup.magneticFluxDensityDecreaseRate / 2) := by
    rw [hDynamics.netForceMagnitudeLaw, hMagneticForce, add_zero,
      hDynamics.electricForceMagnitudeLaw, hElectricField]
  have hMassNe : massInKilograms setup.particleMass ≠ 0 :=
    ne_of_gt hPhysical.protonMassPositive
  have hNewton := hDynamics.newtonSecondLaw
  rw [hNetForce] at hNewton
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hMassNe)).2
  calc
    accelerationInMetersPerSecondSquared setup.accelerationMagnitudeAtC *
          (2 * massInKilograms setup.particleMass) =
        2 * (massInKilograms setup.particleMass *
          accelerationInMetersPerSecondSquared
            setup.accelerationMagnitudeAtC) := by ring
    _ = 2 * (chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          (lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
            magneticFluxDensityRateInTeslasPerSecond
              setup.magneticFluxDensityDecreaseRate / 2)) := by
        rw [hNewton]
    _ = chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
          magneticFluxDensityRateInTeslasPerSecond
            setup.magneticFluxDensityDecreaseRate := by ring

/-!
Standard proton data, the one-centimetre radius of `c`, and `0.10 T/s` put the
acceleration in the two-significant-figure interval centered on choice B.
-/
lemma protonAccelerationAtC_uniquely_matches_answerB
    (setup : ProtonInDecreasingMagneticFieldSetup)
    (hData : MatchesWrittenProblemData setup)
    (hFigure : MatchesSuppliedDecreasingFieldFigure setup)
    (hReference : UsesStandardProtonReferenceData setup)
    (hPhysical : HasPhysicalParameters setup)
    (hFaraday : SatisfiesFaradayLawAtC setup)
    (hDynamics : SatisfiesInitialLorentzForceAndNewtonSecondLaw setup) :
    IsUniqueMatchingDisplayedAcceleration setup .B := by
  have hCentimetersToMeters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have hscale := congrArg (fun x => (x.val : ℝ)) (length.2
      UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices))
    norm_num [lengthInMeters, lengthInCentimeters, lengthReadout,
      UnitChoices.SI, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.meters, LengthUnit.div_eq_val]
      at hscale ⊢
    exact hscale
  have hRadiusMeters :
      lengthInMeters (setup.radialDistanceFromCircleCenter .c) = 1 / 100 := by
    have hRadiusCentimeters := hFigure.pointCRadiusCentimeters
    rw [hCentimetersToMeters] at hRadiusCentimeters
    linarith only [hRadiusCentimeters]
  have hAcceleration :=
    protonAccelerationAtC_eq_charge_mul_radius_mul_rate_div_mass
      setup hData hPhysical hFaraday hDynamics
  have hCharge :
      chargeMagnitudeInCoulombs setup.particleChargeMagnitude =
        1.602176634e-19 := by
    rw [hReference.protonChargeMagnitudeCoulombs]
    norm_num [physlibElementaryChargeInCoulombs,
      ChargeUnit.elementaryCharge, ChargeUnit.scale, ChargeUnit.coulombs,
      ChargeUnit.div_eq_val, NNReal.toReal]
  have hMass :
      massInKilograms setup.particleMass =
        167262192595 / (10 : ℝ) ^ 38 := by
    simpa [protonMassInKilograms] using hReference.protonMassKilograms
  have hAccelerationEquation :
      (2 * massInKilograms setup.particleMass) *
          accelerationInMetersPerSecondSquared
            setup.accelerationMagnitudeAtC =
        chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
          magneticFluxDensityRateInTeslasPerSecond
            setup.magneticFluxDensityDecreaseRate := by
    rw [hAcceleration]
    field_simp [ne_of_gt hPhysical.protonMassPositive]
  rw [hCharge, hMass, hRadiusMeters,
    hData.magneticFieldDecreaseRateTeslasPerSecond] at hAccelerationEquation
  have hAccelerationBounds :
      47500 <
          accelerationInMetersPerSecondSquared
            setup.accelerationMagnitudeAtC ∧
        accelerationInMetersPerSecondSquared
            setup.accelerationMagnitudeAtC < 48500 := by
    constructor <;> norm_num at hAccelerationEquation ⊢ <;>
      linarith only [hAccelerationEquation]
  unfold IsUniqueMatchingDisplayedAcceleration
  constructor
  · rw [MatchesDisplayedAcceleration, abs_lt]
    norm_num [AnswerChoice.displayedAccelerationInMetersPerSecondSquared]
    constructor <;> linarith [hAccelerationBounds.1, hAccelerationBounds.2]
  · intro other hOther
    cases other
    · norm_num [MatchesDisplayedAcceleration,
        AnswerChoice.displayedAccelerationInMetersPerSecondSquared,
        abs_lt] at hOther
      linarith [hAccelerationBounds.1]
    · rfl
    · norm_num [MatchesDisplayedAcceleration,
        AnswerChoice.displayedAccelerationInMetersPerSecondSquared,
        abs_lt] at hOther
      linarith [hAccelerationBounds.2]
    · norm_num [MatchesDisplayedAcceleration,
        AnswerChoice.displayedAccelerationInMetersPerSecondSquared,
        abs_lt] at hOther
      linarith [hAccelerationBounds.1]

/-!
The induced field at `c` is `r_c |dB/dt| / 2`; the initially stationary
proton therefore has acceleration `q r_c |dB/dt| / (2m)`.  With standard
proton data, this rounds uniquely to `4.8 × 10⁴ m/s²`, recorded choice B.

This declaration formalizes `thm:physics:phyx_mini_0927:target`.  Neither
formula nor the answer match occurs in any premise.
-/
theorem problem_phyx_mini_0927
    (setup : ProtonInDecreasingMagneticFieldSetup)
    (hData : MatchesWrittenProblemData setup)
    (hFigure : MatchesSuppliedDecreasingFieldFigure setup)
    (hReference : UsesStandardProtonReferenceData setup)
    (hPhysical : HasPhysicalParameters setup)
    (hField : SatisfiesUniformDecreasingMagneticFieldModel setup)
    (hFaraday : SatisfiesFaradayLawAtC setup)
    (hDirections : SatisfiesLenzAndForceDirectionLaws setup)
    (hDynamics : SatisfiesInitialLorentzForceAndNewtonSecondLaw setup) :
    electricFieldStrengthInVoltsPerMeter
          setup.inducedElectricFieldStrengthAtC =
        lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
            magneticFluxDensityRateInTeslasPerSecond
              setup.magneticFluxDensityDecreaseRate /
          2 ∧
      accelerationInMetersPerSecondSquared setup.accelerationMagnitudeAtC =
        chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
            lengthInMeters (setup.radialDistanceFromCircleCenter .c) *
            magneticFluxDensityRateInTeslasPerSecond
              setup.magneticFluxDensityDecreaseRate /
          (2 * massInKilograms setup.particleMass) ∧
      IsUniqueMatchingDisplayedAcceleration setup recordedDatasetAnswer := by
  refine ⟨inducedElectricFieldAtC_eq_radius_mul_rate_div_two
      setup hPhysical hFaraday, ?_⟩
  refine ⟨protonAccelerationAtC_eq_charge_mul_radius_mul_rate_div_mass
      setup hData hPhysical hFaraday hDynamics, ?_⟩
  simpa [recordedDatasetAnswer] using
    protonAccelerationAtC_uniquely_matches_answerB
      setup hData hFigure hReference hPhysical hFaraday hDynamics

end PhyXMiniProblems.ProblemPhyXMini0927
