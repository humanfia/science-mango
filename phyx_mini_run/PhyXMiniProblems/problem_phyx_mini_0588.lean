import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0588

open Dimension

/-!
# Photon absorption rate of a small detector

An isotropic monochromatic source illuminates a detector of finite absorbing
area. The supplied figure gives emitted energy as a straight-line function of
time, so its slope is the source power. Geometric dilution, detector
absorptivity, the photon relation `Eγ λ = h c`, and energy-rate balance then
determine the absorbed photon rate.

All dimensional physical quantities below are unit-independent Physlib
objects. Real numbers occur only as coherent-SI readouts, dimensionless
fractions, graph labels, and displayed answer values. In particular, the
absorbed photon rate is an independent field of the setup and is not defined
to be the recorded answer.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Power has physical dimension energy divided by time. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- Action, the dimensional role of ordinary Planck's constant, is energy-time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical power. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- A nonnegative, unit-independent value of ordinary Planck's constant. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative photon-count rate, with dimension inverse time. -/
abbrev PhotonRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Area readout in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  nonnegativeSIReadout area

/-- Length readout in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Length readout in nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthInMeters length * (10 : ℝ) ^ 9

/-- Time readout in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Energy readout in nanojoules. -/
def energyInNanojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy * (10 : ℝ) ^ 9

/-- Power readout in watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  nonnegativeSIReadout power

/-- Speed readout in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  nonnegativeSIReadout speed

/-- Ordinary Planck-constant readout in joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  nonnegativeSIReadout constant

/-- Photon-count rate readout in photons per second. -/
def photonRateInPerSecond (rate : PhotonRateQuantity) : ℝ :=
  nonnegativeSIReadout rate

/-! ## Physical roles and primary-figure vocabulary -/

/-- Angular emission model of the light source. -/
inductive EmissionPattern where
  | isotropicPointSource
  | other
  deriving DecidableEq, Repr

/-- Spectral model of the incident light. -/
inductive LightSpectrum where
  | monochromatic
  | other
  deriving DecidableEq, Repr

/-- Orientation of the detector's absorbing face. -/
inductive DetectorOrientation where
  | facesSource
  | other
  deriving DecidableEq, Repr

/-- The two axes visible in the source-energy graph. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to an axis of the graph. -/
inductive FigureAxisQuantity where
  | elapsedTime
  | emittedEnergy
  deriving DecidableEq, Repr

/-- Unit printed beside an axis of the graph. -/
inductive FigureAxisUnit where
  | seconds
  | nanojoules
  deriving DecidableEq, Repr

/-- Color of the rising trace in the primary raster. -/
inductive FigureTraceColor where
  | pink
  | other
  deriving DecidableEq, Repr

/-!
The primary figure. Its labeled point carries physical time and energy
quantities; the booleans retain the origin, straight-line, and dashed-guide
features visible in the raster.
-/
structure SourceEnergyFigure where
  axisQuantity : FigureAxis → FigureAxisQuantity
  axisUnit : FigureAxis → FigureAxisUnit
  plottedEmittedEnergyAt : TimeQuantity → DimEnergy
  labeledTimeTs : TimeQuantity
  labeledEnergyEs : DimEnergy
  risingTraceColor : FigureTraceColor
  risingTraceIsStraight : Bool
  risingTraceStartsAtOrigin : Bool
  horizontalGuideAtEsIsDashed : Bool
  verticalGuideAtTsIsDashed : Bool

/-!
Independent physical quantities in the experiment. The four rate/energy
fields are observables related by the governing laws below, not definitions
of the desired numerical answer.
-/
structure PhotonDetectorSetup where
  emissionPattern : EmissionPattern
  lightSpectrum : LightSpectrum
  detectorOrientation : DetectorOrientation
  detectorAbsorbingArea : DimArea
  detectorAbsorptivity : ℝ
  incidentWavelength : LengthQuantity
  sourceDetectorDistance : LengthQuantity
  ordinaryPlanckConstant : PlanckConstantQuantity
  vacuumSpeedOfLight : DimSpeed
  sourceRadiantPower : PowerQuantity
  incidentPowerAtDetector : PowerQuantity
  absorbedPowerAtDetector : PowerQuantity
  singlePhotonEnergy : DimEnergy
  absorbedPhotonRate : PhotonRateQuantity
  figure : SourceEnergyFigure

/-! ## Scenario assumptions and figure/data readouts -/

/-- Qualitative roles stated in the prose description. -/
structure MatchesPhotonDetectorScenario
    (setup : PhotonDetectorSetup) : Prop where
  sourceIsIsotropic : setup.emissionPattern = .isotropicPointSource
  incidentLightIsMonochromatic : setup.lightSpectrum = .monochromatic
  absorbingFacePointsTowardSource :
    setup.detectorOrientation = .facesSource

/-!
Scalar readouts given in the problem prose. These premises state detector
geometry, absorptivity, wavelength, and distance; they contain no photon-rate
conclusion.
-/
structure MatchesProblemReadouts
    (setup : PhotonDetectorSetup) : Prop where
  absorbingAreaSquareMeters :
    areaInSquareMeters setup.detectorAbsorbingArea =
      2.00 * (10 : ℝ) ^ (-6 : ℤ)
  absorbsFiftyPercent : setup.detectorAbsorptivity = 0.50
  incidentWavelengthNanometers :
    lengthInNanometers setup.incidentWavelength = 600
  sourceDistanceMeters :
    lengthInMeters setup.sourceDetectorDistance = 12.0

/-!
Literal graph labels and qualitative evidence from image 588. The final field
expresses the straight trace as proportional growth between the origin and the
labeled point, without assuming its slope or the requested photon rate.
-/
structure MatchesSourceEnergyFigure
    (setup : PhotonDetectorSetup) : Prop where
  horizontalAxisIsTime :
    setup.figure.axisQuantity .horizontal = .elapsedTime
  verticalAxisIsEnergy :
    setup.figure.axisQuantity .vertical = .emittedEnergy
  horizontalAxisInSeconds :
    setup.figure.axisUnit .horizontal = .seconds
  verticalAxisInNanojoules :
    setup.figure.axisUnit .vertical = .nanojoules
  traceIsPink : setup.figure.risingTraceColor = .pink
  traceIsStraight : setup.figure.risingTraceIsStraight = true
  traceStartsAtOrigin : setup.figure.risingTraceStartsAtOrigin = true
  horizontalGuideIsDashed :
    setup.figure.horizontalGuideAtEsIsDashed = true
  verticalGuideIsDashed :
    setup.figure.verticalGuideAtTsIsDashed = true
  labeledTimeSeconds : timeInSeconds setup.figure.labeledTimeTs = 2.0
  labeledEnergyNanojoules :
    energyInNanojoules setup.figure.labeledEnergyEs = 7.2
  labeledPointLiesOnTrace :
    energyInJoules
        (setup.figure.plottedEmittedEnergyAt setup.figure.labeledTimeTs) =
      energyInJoules setup.figure.labeledEnergyEs
  straightTraceRelation : ∀ time,
    0 ≤ timeInSeconds time →
    timeInSeconds time ≤ timeInSeconds setup.figure.labeledTimeTs →
    energyInJoules (setup.figure.plottedEmittedEnergyAt time) *
        timeInSeconds setup.figure.labeledTimeTs =
      energyInJoules setup.figure.labeledEnergyEs * timeInSeconds time

/-!
Exact coherent-SI readouts of the two universal constants used by the photon
model. They are calibrated physical data, not consequences about this
detector.
-/
structure MatchesCalibratedConstants
    (setup : PhotonDetectorSetup) : Prop where
  ordinaryPlanckConstantSI :
    planckConstantInJouleSeconds setup.ordinaryPlanckConstant =
      6.62607015 * (10 : ℝ) ^ (-34 : ℤ)
  speedOfLightSI :
    speedInMetersPerSecond setup.vacuumSpeedOfLight = 299792458

/-! ## Governing laws -/

/-!
The five physical relations used in the calculation are: graph slope equals
source radiant power; isotropic power crosses a sphere of area `4 π r²`
uniformly; absorbed power is absorptivity times incident power; `Eγ λ = h c`;
and photon energy balance converts power to count rate. None of these fields
fixes the count rate to a displayed answer value.
-/
structure PhotonAbsorptionLaws
    (setup : PhotonDetectorSetup) : Prop where
  sourcePowerFromGraphSlope :
    powerInWatts setup.sourceRadiantPower *
        timeInSeconds setup.figure.labeledTimeTs =
      energyInJoules setup.figure.labeledEnergyEs
  isotropicGeometricDilution :
    powerInWatts setup.incidentPowerAtDetector *
        (4 * Real.pi *
          (lengthInMeters setup.sourceDetectorDistance) ^ 2) =
      powerInWatts setup.sourceRadiantPower *
        areaInSquareMeters setup.detectorAbsorbingArea
  detectorAbsorbsFixedFraction :
    powerInWatts setup.absorbedPowerAtDetector =
      setup.detectorAbsorptivity *
        powerInWatts setup.incidentPowerAtDetector
  photonEnergyWavelengthRelation :
    energyInJoules setup.singlePhotonEnergy *
        lengthInMeters setup.incidentWavelength =
      planckConstantInJouleSeconds setup.ordinaryPlanckConstant *
        speedInMetersPerSecond setup.vacuumSpeedOfLight
  absorbedPhotonEnergyBalance :
    photonRateInPerSecond setup.absorbedPhotonRate *
        energyInJoules setup.singlePhotonEnergy =
      powerInWatts setup.absorbedPowerAtDetector
  singlePhotonEnergyPositive :
    0 < energyInJoules setup.singlePhotonEnergy

/-! ## Displayed alternatives and current target -/

/-- Answer labels in the order printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed photon rates, in photons per second. -/
def displayedPhotonRateInPerSecond : AnswerChoice → ℝ
  | .A => 12.0
  | .B => 3.0
  | .C => 6.0
  | .D => 9.0

/-- Tolerance corresponding to a rate displayed to one decimal place. -/
def displayedRateTolerance : ℝ := 0.05

/-- The computed physical rate rounds to the displayed value of a choice. -/
def MatchesDisplayedPhotonRate
    (setup : PhotonDetectorSetup) (choice : AnswerChoice) : Prop :=
  |photonRateInPerSecond setup.absorbedPhotonRate -
      displayedPhotonRateInPerSecond choice| ≤ displayedRateTolerance

/-- Exactly one printed alternative matches the computed physical rate. -/
def IsUniqueMatchingPhotonRate
    (setup : PhotonDetectorSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPhotonRate setup choice ∧
    ∀ other : AnswerChoice, other ≠ choice →
      ¬ MatchesDisplayedPhotonRate setup other

/-!
The detector absorbs photons at a rate displayed as `6.0 photons/s`, namely
choice C, and no other printed alternative agrees at the stated precision.

Blueprint: `thm:physics:phyx_mini_0588:target`.
-/
theorem problem_phyx_mini_0588
    (setup : PhotonDetectorSetup)
    (scenario : MatchesPhotonDetectorScenario setup)
    (readouts : MatchesProblemReadouts setup)
    (figure : MatchesSourceEnergyFigure setup)
    (constants : MatchesCalibratedConstants setup)
    (laws : PhotonAbsorptionLaws setup) :
    MatchesDisplayedPhotonRate setup .C ∧
      IsUniqueMatchingPhotonRate setup .C := by
  let area : ℝ := areaInSquareMeters setup.detectorAbsorbingArea
  let wavelength : ℝ := lengthInMeters setup.incidentWavelength
  let distance : ℝ := lengthInMeters setup.sourceDetectorDistance
  let labeledTime : ℝ := timeInSeconds setup.figure.labeledTimeTs
  let labeledEnergy : ℝ := energyInJoules setup.figure.labeledEnergyEs
  let planck : ℝ :=
    planckConstantInJouleSeconds setup.ordinaryPlanckConstant
  let lightSpeed : ℝ :=
    speedInMetersPerSecond setup.vacuumSpeedOfLight
  let sourcePower : ℝ := powerInWatts setup.sourceRadiantPower
  let incidentPower : ℝ := powerInWatts setup.incidentPowerAtDetector
  let absorbedPower : ℝ := powerInWatts setup.absorbedPowerAtDetector
  let photonEnergy : ℝ := energyInJoules setup.singlePhotonEnergy
  let photonRate : ℝ := photonRateInPerSecond setup.absorbedPhotonRate

  have hArea : area = 1 / 500000 := by
    dsimp [area]
    rw [readouts.absorbingAreaSquareMeters]
    norm_num
  have hWavelength : wavelength = 3 / 5000000 := by
    have h := readouts.incidentWavelengthNanometers
    change wavelength * (10 : ℝ) ^ 9 = 600 at h
    norm_num at h ⊢
    linarith
  have hDistance : distance = 12 := by
    have h := readouts.sourceDistanceMeters
    norm_num at h
    simpa [distance] using h
  have hLabeledTime : labeledTime = 2 := by
    have h := figure.labeledTimeSeconds
    norm_num at h
    simpa [labeledTime] using h
  have hLabeledEnergy : labeledEnergy = 9 / 1250000000 := by
    have h := figure.labeledEnergyNanojoules
    change labeledEnergy * (10 : ℝ) ^ 9 = 7.2 at h
    norm_num at h ⊢
    linarith
  have hPlanck :
      planck = 6.62607015 * (10 : ℝ) ^ (-34 : ℤ) := by
    exact constants.ordinaryPlanckConstantSI
  have hLightSpeed : lightSpeed = 299792458 := by
    exact constants.speedOfLightSI
  have hSourceLaw : sourcePower * labeledTime = labeledEnergy := by
    exact laws.sourcePowerFromGraphSlope
  have hDilution :
      incidentPower * (4 * Real.pi * distance ^ 2) =
        sourcePower * area := by
    exact laws.isotropicGeometricDilution
  have hAbsorption :
      absorbedPower = (0.50 : ℝ) * incidentPower := by
    simpa [absorbedPower, incidentPower, readouts.absorbsFiftyPercent] using
      laws.detectorAbsorbsFixedFraction
  have hPhotonLaw : photonEnergy * wavelength = planck * lightSpeed := by
    exact laws.photonEnergyWavelengthRelation
  have hBalance : photonRate * photonEnergy = absorbedPower := by
    exact laws.absorbedPhotonEnergyBalance
  have hPhotonEnergyPositive : 0 < photonEnergy := by
    exact laws.singlePhotonEnergyPositive
  have hPhotonRateNonnegative : 0 ≤ photonRate := by
    dsimp [photonRate, photonRateInPerSecond, nonnegativeSIReadout]
    exact NNReal.coe_nonneg _

  have hSourcePower : sourcePower = 9 / 2500000000 := by
    norm_num [hLabeledTime, hLabeledEnergy] at hSourceLaw ⊢
    linarith
  have hIncidentPi : incidentPower * Real.pi =
      1 / 80000000000000000 := by
    rw [hDistance, hSourcePower, hArea] at hDilution
    norm_num at hDilution ⊢
    nlinarith
  have hPhotonEnergy : photonEnergy =
      (6621486190496429 : ℝ) /
        20000000000000000000000000000000000 := by
    norm_num [hWavelength, hPlanck, hLightSpeed] at hPhotonLaw ⊢
    linarith
  have hRateIncident :
      photonRate * 6621486190496429 =
        incidentPower *
          10000000000000000000000000000000000 := by
    rw [hPhotonEnergy, hAbsorption] at hBalance
    norm_num at hBalance ⊢
    linarith
  have hRatePiScaled :
      photonRate * Real.pi * 6621486190496429 =
        125000000000000000 := by
    linear_combination
      Real.pi * hRateIncident +
        10000000000000000000000000000000000 * hIncidentPi
  have hRatePi :
      photonRate * Real.pi =
        (125000000000000000 : ℝ) / 6621486190496429 := by
    norm_num at hRatePiScaled ⊢
    nlinarith
  have hProductLower :
      photonRate * 3.14 ≤ photonRate * Real.pi := by
    exact mul_le_mul_of_nonneg_left Real.pi_gt_d2.le
      hPhotonRateNonnegative
  have hProductUpper :
      photonRate * Real.pi ≤ photonRate * 3.15 := by
    exact mul_le_mul_of_nonneg_left Real.pi_lt_d2.le
      hPhotonRateNonnegative
  have hRateLower : (5.95 : ℝ) ≤ photonRate := by
    norm_num at hRatePi hProductUpper ⊢
    nlinarith
  have hRateUpper : photonRate ≤ (6.05 : ℝ) := by
    norm_num at hRatePi hProductLower ⊢
    nlinarith

  have hMatchesC : MatchesDisplayedPhotonRate setup .C := by
    simp only [MatchesDisplayedPhotonRate, displayedPhotonRateInPerSecond,
      displayedRateTolerance]
    rw [show photonRateInPerSecond setup.absorbedPhotonRate = photonRate by rfl]
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith
  refine ⟨hMatchesC, hMatchesC, ?_⟩
  intro other hOther hMatchesOther
  fin_cases other <;>
    simp_all [MatchesDisplayedPhotonRate, displayedPhotonRateInPerSecond,
      displayedRateTolerance, photonRate, abs_le] <;>
    norm_num at * <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0588
