import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0944

open Dimension

/-!
# Radio transmission to a satellite over a hemisphere

A transmitter on the earth's surface emits a sinusoidal electromagnetic wave
with average total power `50 kW`.  The idealized radiation is uniform over the
hemisphere above the ground.  The primary figure places a satellite on the
hemisphere at range `r = 100 km` and draws a signal arrow from the transmitter
to the satellite.

Physical lengths, power, irradiance, field amplitudes, and vacuum permeability
are unit-independent Physlib `Dimensionful` quantities.  Real numbers occur
only as coherent-SI readouts, sinusoidal phase data, and displayed numerical
answers.  Physlib's electric and magnetic fields retain the spacetime-vector
roles of the detected fields.

Assumption/target split:

* governing laws: uniform power flux through a hemisphere, the vacuum
  plane-wave relation `E_max = c B_max`, and the average Poynting-flux relation
  `I = E_max B_max / (2 μ₀)`;
* previous-part results: none;
* figure/data readouts: `50 kW`, `r = 100 km`, transmitter/satellite labels,
  the hemispherical dome and signal arrow, and textbook vacuum `μ₀`;
* current targets: exact expressions and rounded SI values for both detected
  amplitudes, together with the unique matching magnetic-field choice B.

No requested amplitude value or answer label occurs in a premise.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension `M L² T⁻³` of power. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M T⁻³` of irradiance (power per area). -/
def irradianceDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M T⁻¹ C⁻¹` of magnetic-field strength. -/
def magneticFieldStrengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M L C⁻²` of vacuum magnetic permeability. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent average power. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- A nonnegative, unit-independent electromagnetic irradiance. -/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim irradianceDimension NNReal)

/-- A nonnegative electric-field amplitude. -/
abbrev ElectricFieldAmplitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative magnetic-field amplitude. -/
abbrev MagneticFieldAmplitudeQuantity : Type :=
  Dimensionful (WithDim magneticFieldStrengthDimension NNReal)

/-- A nonnegative magnetic permeability, used here for vacuum `μ₀`. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- Read a physical length in coherent SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in kilometres. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthInMeters length / 1000

/-- Read an average power in coherent SI watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read an average power in kilowatts. -/
def powerInKilowatts (power : PowerQuantity) : ℝ :=
  powerInWatts power / 1000

/-- Read irradiance in coherent SI watts per square metre. -/
def irradianceInWattsPerSquareMeter (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- Read an electric-field amplitude in coherent SI volts per metre. -/
def electricAmplitudeInVoltsPerMeter
    (amplitude : ElectricFieldAmplitudeQuantity) : ℝ :=
  ((amplitude UnitChoices.SI).val : ℝ)

/-- Read a magnetic-field amplitude in coherent SI teslas. -/
def magneticAmplitudeInTeslas
    (amplitude : MagneticFieldAmplitudeQuantity) : ℝ :=
  ((amplitude UnitChoices.SI).val : ℝ)

/-- Read vacuum permeability in coherent SI newtons per ampere squared. -/
def permeabilityInNewtonsPerAmpereSquared
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  ((permeability UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum light speed, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Physical setup and primary-figure vocabulary -/

/-- Qualitative waveform stated in the problem. -/
inductive Waveform where
  | sinusoidal
  | other
  deriving DecidableEq, Repr

/-- The idealized angular region into which the transmitter radiates. -/
inductive RadiationRegion where
  | hemisphereAboveGround
  | fullSphere
  | other
  deriving DecidableEq, Repr

/-- The two labeled physical objects visible in the primary figure. -/
inductive FigureObject where
  | transmitter
  | satellite
  deriving DecidableEq, Fintype, Repr

/-!
Literal typed content of image `944.png`.  The radius label is a physical
length.  Its `100 km` calibration is imposed separately, rather than stored as
a dimensionless field of the figure.
-/
structure RadioStationSatelliteFigure where
  showsObject : FigureObject → Bool
  printedObjectLabel : FigureObject → String
  showsHemisphericalCoverageDome : Bool
  domeRadiusLabel : LengthQuantity
  showsSignalArrow : Bool
  signalArrowStart : FigureObject
  signalArrowEnd : FigureObject

/-!
The independent source, detector, fields, and amplitude observables.  Neither
amplitude is defined from a displayed answer or from the requested numerical
value.
-/
structure RadioStationSatelliteSetup where
  waveform : Waveform
  radiationRegion : RadiationRegion
  averageTotalPower : PowerQuantity
  transmitterPosition : Space 3
  satellitePosition : Space 3
  satelliteRange : LengthQuantity
  averageIntensityAtSatellite : IrradianceQuantity
  electricField : Electromagnetism.ElectricField 3
  magneticField : Electromagnetism.MagneticField 3
  electricFieldAmplitudeAtSatellite : ElectricFieldAmplitudeQuantity
  magneticFieldAmplitudeAtSatellite : MagneticFieldAmplitudeQuantity
  carrierAngularFrequencyRadiansPerSecond : ℝ
  commonPhaseRadians : ℝ
  electricPolarizationDirection : EuclideanSpace ℝ (Fin 3)
  magneticPolarizationDirection : EuclideanSpace ℝ (Fin 3)
  vacuumPermeability : MagneticPermeabilityQuantity
  figure : RadioStationSatelliteFigure

/-- The literal labels printed next to each object in the supplied image. -/
def expectedFigureLabel : FigureObject → String
  | .transmitter => "Transmitter"
  | .satellite => "Satellite"

/-! ## Source data, figure evidence, and physical parameters -/

/-!
Problem-text and primary-image readouts.  These facts identify the source
power and range and relate the physical setup to the dome, labels, and arrow.
They do not assign either field amplitude.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : RadioStationSatelliteSetup) : Prop where
  waveformIsSinusoidal : setup.waveform = .sinusoidal
  radiatesOnlyAboveGround :
    setup.radiationRegion = .hemisphereAboveGround
  averagePowerKilowatts :
    powerInKilowatts setup.averageTotalPower = 50
  satelliteRangeKilometers :
    lengthInKilometers setup.satelliteRange = 100
  positionsRealizeRange :
    ‖setup.satellitePosition - setup.transmitterPosition‖ =
      lengthInMeters setup.satelliteRange
  bothObjectsShown : ∀ object, setup.figure.showsObject object = true
  printedLabels : ∀ object,
    setup.figure.printedObjectLabel object = expectedFigureLabel object
  coverageDomeShown :
    setup.figure.showsHemisphericalCoverageDome = true
  domeRadiusIsSatelliteRange :
    setup.figure.domeRadiusLabel = setup.satelliteRange
  signalArrowShown : setup.figure.showsSignalArrow = true
  signalArrowFromTransmitter :
    setup.figure.signalArrowStart = .transmitter
  signalArrowToSatellite :
    setup.figure.signalArrowEnd = .satellite

/-- Positivity and nondegeneracy conditions for the radiation model. -/
structure HasPhysicalRadiationParameters
    (setup : RadioStationSatelliteSetup) : Prop where
  powerPositive : 0 < powerInWatts setup.averageTotalPower
  rangePositive : 0 < lengthInMeters setup.satelliteRange
  intensityPositive :
    0 < irradianceInWattsPerSquareMeter
      setup.averageIntensityAtSatellite
  permeabilityPositive :
    0 < permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability
  lightSpeedPositive : 0 < speedOfLightInMetersPerSecond
  angularFrequencyPositive :
    0 < setup.carrierAngularFrequencyRadiansPerSecond

/-!
The standard textbook calibration `μ₀ = 4π × 10⁻⁷ N/A²`.  This is an
independent universal-constant input, not a requested field amplitude.
-/
def UsesTextbookVacuumPermeability
    (setup : RadioStationSatelliteSetup) : Prop :=
  permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability =
    4 * Real.pi * 10 ^ (-7 : ℤ)

/-!
At the satellite, both fields are sinusoidal with a common phase and with the
stored amplitudes as their SI component scales.  Unit polarization vectors
ensure that these scales really are field maxima; no numerical amplitude is
assumed.
-/
structure SatisfiesSinusoidalDetectionModel
    (setup : RadioStationSatelliteSetup) : Prop where
  electricDirectionIsUnit :
    ‖setup.electricPolarizationDirection‖ = 1
  magneticDirectionIsUnit :
    ‖setup.magneticPolarizationDirection‖ = 1
  electricFieldAtSatellite : ∀ time,
    setup.electricField time setup.satellitePosition =
      (electricAmplitudeInVoltsPerMeter
          setup.electricFieldAmplitudeAtSatellite *
        Real.sin
          (setup.carrierAngularFrequencyRadiansPerSecond * time +
            setup.commonPhaseRadians)) •
        setup.electricPolarizationDirection
  magneticFieldAtSatellite : ∀ time,
    setup.magneticField time setup.satellitePosition =
      (magneticAmplitudeInTeslas
          setup.magneticFieldAmplitudeAtSatellite *
        Real.sin
          (setup.carrierAngularFrequencyRadiansPerSecond * time +
            setup.commonPhaseRadians)) •
        setup.magneticPolarizationDirection

/-! ## Governing radiation and plane-wave laws -/

/-!
The equal-above-ground radiation assumption spreads the average power over a
hemisphere of area `2πr²`.  A vacuum plane wave has `E_max = c B_max`, and its
time-averaged Poynting magnitude is `E_max B_max / (2 μ₀)`.  These are general
modeling relations and contain none of the requested numerical conclusions.
-/
structure SatisfiesHemisphericalPlaneWaveLaws
    (setup : RadioStationSatelliteSetup) : Prop where
  uniformHemisphericalFlux :
    irradianceInWattsPerSquareMeter
        setup.averageIntensityAtSatellite =
      powerInWatts setup.averageTotalPower /
        (2 * Real.pi * lengthInMeters setup.satelliteRange ^ 2)
  vacuumAmplitudeRelation :
    electricAmplitudeInVoltsPerMeter
        setup.electricFieldAmplitudeAtSatellite =
      speedOfLightInMetersPerSecond *
        magneticAmplitudeInTeslas
          setup.magneticFieldAmplitudeAtSatellite
  averagePoyntingFlux :
    irradianceInWattsPerSquareMeter
        setup.averageIntensityAtSatellite =
      electricAmplitudeInVoltsPerMeter
          setup.electricFieldAmplitudeAtSatellite *
        magneticAmplitudeInTeslas
          setup.magneticFieldAmplitudeAtSatellite /
        (2 * permeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability)

/-! ## Exact amplitude relations -/

/-!
Solving the positive plane-wave and Poynting relations for `B_max` gives the
standard exact square-root expression.
-/
lemma magneticAmplitude_exact
    (setup : RadioStationSatelliteSetup)
    (hPhysical : HasPhysicalRadiationParameters setup)
    (hLaws : SatisfiesHemisphericalPlaneWaveLaws setup) :
    magneticAmplitudeInTeslas
        setup.magneticFieldAmplitudeAtSatellite =
      Real.sqrt
        (2 * permeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          irradianceInWattsPerSquareMeter
            setup.averageIntensityAtSatellite /
          speedOfLightInMetersPerSecond) := by
  let B :=
    magneticAmplitudeInTeslas setup.magneticFieldAmplitudeAtSatellite
  let E :=
    electricAmplitudeInVoltsPerMeter setup.electricFieldAmplitudeAtSatellite
  let I :=
    irradianceInWattsPerSquareMeter setup.averageIntensityAtSatellite
  let μ :=
    permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability
  let c := speedOfLightInMetersPerSecond
  have hB : 0 ≤ B := by
    dsimp [B, magneticAmplitudeInTeslas]
    positivity
  have hμ : 0 < μ := hPhysical.permeabilityPositive
  have hc : 0 < c := hPhysical.lightSpeedPositive
  have hden : 2 * μ ≠ 0 := mul_ne_zero (by norm_num) hμ.ne'
  have hflux : I * (2 * μ) = E * B := by
    apply (eq_div_iff hden).mp
    exact hLaws.averagePoyntingFlux
  have hfield : E = c * B := hLaws.vacuumAmplitudeRelation
  have hsq : B ^ 2 = 2 * μ * I / c := by
    apply (eq_div_iff hc.ne').2
    calc
      B ^ 2 * c = E * B := by rw [hfield]; ring
      _ = I * (2 * μ) := hflux.symm
      _ = 2 * μ * I := by ring
  change B = Real.sqrt (2 * μ * I / c)
  calc
    B = Real.sqrt (B ^ 2) := (Real.sqrt_sq hB).symm
    _ = Real.sqrt (2 * μ * I / c) := by rw [hsq]

/-- The corresponding exact vacuum relation for `E_max`. -/
lemma electricAmplitude_exact
    (setup : RadioStationSatelliteSetup)
    (hPhysical : HasPhysicalRadiationParameters setup)
    (hLaws : SatisfiesHemisphericalPlaneWaveLaws setup) :
    electricAmplitudeInVoltsPerMeter
        setup.electricFieldAmplitudeAtSatellite =
      speedOfLightInMetersPerSecond *
        Real.sqrt
          (2 * permeabilityInNewtonsPerAmpereSquared
              setup.vacuumPermeability *
            irradianceInWattsPerSquareMeter
              setup.averageIntensityAtSatellite /
            speedOfLightInMetersPerSecond) := by
  rw [hLaws.vacuumAmplitudeRelation,
    magneticAmplitude_exact setup hPhysical hLaws]

/-! ## Displayed choices and numerical conclusions -/

/-- Labels of the four magnetic-field choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-field amplitude in teslas printed beside each answer label. -/
def displayedMagneticAmplitudeInTeslas : AnswerChoice → ℝ
  | .A => (2.2 : ℝ) * 10 ^ (-11 : ℤ)
  | .B => (8.17 : ℝ) * 10 ^ (-11 : ℤ)
  | .C => (1 : ℝ) * 10 ^ (-11 : ℤ)
  | .D => (2.6 : ℝ) * 10 ^ (-11 : ℤ)

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Half of the final displayed digit in the three-digit value of choice B. -/
def magneticChoiceBToleranceInTeslas : ℝ :=
  (0.005 : ℝ) * 10 ^ (-11 : ℤ)

/-- Half of the final displayed digit in `2.45 × 10⁻² V/m`. -/
def electricAmplitudeToleranceInVoltsPerMeter : ℝ :=
  (0.005 : ℝ) * 10 ^ (-2 : ℤ)

/-- A magnetic amplitude rounds to the displayed value of choice B. -/
def MagneticAmplitudeRoundsToChoiceB
    (setup : RadioStationSatelliteSetup) : Prop :=
  |magneticAmplitudeInTeslas setup.magneticFieldAmplitudeAtSatellite -
      displayedMagneticAmplitudeInTeslas .B| <
    magneticChoiceBToleranceInTeslas

/-- An electric amplitude rounds to `2.45 × 10⁻² V/m`. -/
def ElectricAmplitudeRoundsToTwoPointFourFiveTimesTenPowNegTwo
    (setup : RadioStationSatelliteSetup) : Prop :=
  |electricAmplitudeInVoltsPerMeter
        setup.electricFieldAmplitudeAtSatellite -
      (2.45 : ℝ) * 10 ^ (-2 : ℤ)| <
    electricAmplitudeToleranceInVoltsPerMeter

/-- A choice is strictly closer than every distinct displayed alternative. -/
def IsUniqueClosestMagneticAmplitudeChoice
    (setup : RadioStationSatelliteSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative, alternative ≠ choice →
    |magneticAmplitudeInTeslas setup.magneticFieldAmplitudeAtSatellite -
        displayedMagneticAmplitudeInTeslas choice| <
      |magneticAmplitudeInTeslas setup.magneticFieldAmplitudeAtSatellite -
        displayedMagneticAmplitudeInTeslas alternative|

/-!
Uniform spreading over `2πr²`, followed by the vacuum Poynting and amplitude
relations, gives

`B_max ≈ 8.17 × 10⁻¹¹ T` and `E_max ≈ 2.45 × 10⁻² V/m`.

The magnetic amplitude uniquely selects the recorded answer B.  This theorem
formalizes `thm:physics:phyx_mini_0944:target`.  Neither rounded amplitude nor
the answer label is present in any premise.
-/
theorem problem_phyx_mini_0944
    (setup : RadioStationSatelliteSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalRadiationParameters setup)
    (hVacuum : UsesTextbookVacuumPermeability setup)
    (hSinusoidal : SatisfiesSinusoidalDetectionModel setup)
    (hLaws : SatisfiesHemisphericalPlaneWaveLaws setup) :
    magneticAmplitudeInTeslas
        setup.magneticFieldAmplitudeAtSatellite =
      Real.sqrt
        (2 * permeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          irradianceInWattsPerSquareMeter
            setup.averageIntensityAtSatellite /
          speedOfLightInMetersPerSecond) ∧
      electricAmplitudeInVoltsPerMeter
          setup.electricFieldAmplitudeAtSatellite =
        speedOfLightInMetersPerSecond *
          Real.sqrt
            (2 * permeabilityInNewtonsPerAmpereSquared
                setup.vacuumPermeability *
              irradianceInWattsPerSquareMeter
                setup.averageIntensityAtSatellite /
              speedOfLightInMetersPerSecond) ∧
      MagneticAmplitudeRoundsToChoiceB setup ∧
      ElectricAmplitudeRoundsToTwoPointFourFiveTimesTenPowNegTwo setup ∧
      IsUniqueClosestMagneticAmplitudeChoice setup recordedDatasetAnswer := by
  let q : ℝ := (1 : ℝ) / 149896229000000000000
  have hPower :
      powerInWatts setup.averageTotalPower = 50000 := by
    have h := hData.averagePowerKilowatts
    unfold powerInKilowatts at h
    linarith
  have hRange :
      lengthInMeters setup.satelliteRange = 100000 := by
    have h := hData.satelliteRangeKilometers
    unfold lengthInKilometers at h
    linarith
  have hIntensity :
      irradianceInWattsPerSquareMeter
          setup.averageIntensityAtSatellite =
        50000 / (2 * Real.pi * 100000 ^ 2) := by
    rw [hLaws.uniformHemisphericalFlux, hPower, hRange]
  have hPermeability :
      permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability =
        4 * Real.pi * 10 ^ (-7 : ℤ) :=
    hVacuum
  have hLightSpeed :
      speedOfLightInMetersPerSecond = 299792458 := by
    unfold speedOfLightInMetersPerSecond
    rw [DimSpeed.speedOfLight_in_SI]
  have hRadicand :
      2 * permeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          irradianceInWattsPerSquareMeter
            setup.averageIntensityAtSatellite /
          speedOfLightInMetersPerSecond = q := by
    rw [hPermeability, hIntensity, hLightSpeed]
    dsimp [q]
    norm_num [zpow_neg]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hMagneticExact := magneticAmplitude_exact setup hPhysical hLaws
  have hElectricExact := electricAmplitude_exact setup hPhysical hLaws
  have hMagneticValue :
      magneticAmplitudeInTeslas
          setup.magneticFieldAmplitudeAtSatellite =
        Real.sqrt q := by
    rw [hMagneticExact, hRadicand]
  have hElectricValue :
      electricAmplitudeInVoltsPerMeter
          setup.electricFieldAmplitudeAtSatellite =
        299792458 * Real.sqrt q := by
    rw [hElectricExact, hRadicand, hLightSpeed]
  have hRootLower :
      (8.17 : ℝ) * 10 ^ (-11 : ℤ) -
          (0.005 : ℝ) * 10 ^ (-11 : ℤ) <
        Real.sqrt q := by
    rw [Real.lt_sqrt]
    · dsimp [q]
      norm_num [zpow_neg]
    · norm_num [zpow_neg]
  have hRootUpper :
      Real.sqrt q <
        (8.17 : ℝ) * 10 ^ (-11 : ℤ) +
          (0.005 : ℝ) * 10 ^ (-11 : ℤ) := by
    rw [Real.sqrt_lt']
    · dsimp [q]
      norm_num [zpow_neg]
    · norm_num [zpow_neg]
  have hMagneticNumerical :
      |Real.sqrt q - (8.17 : ℝ) * 10 ^ (-11 : ℤ)| <
        (0.005 : ℝ) * 10 ^ (-11 : ℤ) := by
    rw [abs_lt]
    constructor <;> linarith
  have hq : 0 ≤ q := by
    dsimp [q]
    norm_num
  have hSqrtSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hElectricLowerSq :
      ((2.45 : ℝ) * 10 ^ (-2 : ℤ) -
          (0.005 : ℝ) * 10 ^ (-2 : ℤ)) ^ 2 <
        ((299792458 : ℝ) * Real.sqrt q) ^ 2 := by
    rw [mul_pow, hSqrtSq]
    dsimp [q]
    norm_num [zpow_neg]
  have hElectricUpperSq :
      ((299792458 : ℝ) * Real.sqrt q) ^ 2 <
        ((2.45 : ℝ) * 10 ^ (-2 : ℤ) +
          (0.005 : ℝ) * 10 ^ (-2 : ℤ)) ^ 2 := by
    rw [mul_pow, hSqrtSq]
    dsimp [q]
    norm_num [zpow_neg]
  have hElectricNumerical :
      |(299792458 : ℝ) * Real.sqrt q -
          (2.45 : ℝ) * 10 ^ (-2 : ℤ)| <
        (0.005 : ℝ) * 10 ^ (-2 : ℤ) := by
    have hRootNonnegative :
        0 ≤ (299792458 : ℝ) * Real.sqrt q :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg q)
    have hLowerNonnegative :
        0 ≤ (2.45 : ℝ) * 10 ^ (-2 : ℤ) -
          (0.005 : ℝ) * 10 ^ (-2 : ℤ) := by
      norm_num [zpow_neg]
    have hUpperNonnegative :
        0 ≤ (2.45 : ℝ) * 10 ^ (-2 : ℤ) +
          (0.005 : ℝ) * 10 ^ (-2 : ℤ) := by
      norm_num [zpow_neg]
    rw [abs_lt]
    constructor <;> nlinarith
  refine ⟨hMagneticExact, hElectricExact, ?_, ?_, ?_⟩
  · unfold MagneticAmplitudeRoundsToChoiceB
    rw [hMagneticValue]
    simpa only [displayedMagneticAmplitudeInTeslas,
      magneticChoiceBToleranceInTeslas] using hMagneticNumerical
  · unfold ElectricAmplitudeRoundsToTwoPointFourFiveTimesTenPowNegTwo
    rw [hElectricValue]
    simpa only [electricAmplitudeToleranceInVoltsPerMeter] using
      hElectricNumerical
  · unfold IsUniqueClosestMagneticAmplitudeChoice
    simp only [recordedDatasetAnswer]
    intro alternative hAlternative
    rw [hMagneticValue]
    cases alternative with
    | A =>
        simp only [displayedMagneticAmplitudeInTeslas]
        have hPositive :
            0 < Real.sqrt q - (2.2 : ℝ) * 10 ^ (-11 : ℤ) := by
          norm_num [zpow_neg] at hRootLower ⊢
          linarith
        rw [abs_of_pos hPositive]
        apply lt_trans hMagneticNumerical
        norm_num [zpow_neg] at hRootLower ⊢
        linarith
    | B =>
        exact (hAlternative rfl).elim
    | C =>
        simp only [displayedMagneticAmplitudeInTeslas]
        have hPositive :
            0 < Real.sqrt q - (1 : ℝ) * 10 ^ (-11 : ℤ) := by
          norm_num [zpow_neg] at hRootLower ⊢
          linarith
        rw [abs_of_pos hPositive]
        apply lt_trans hMagneticNumerical
        norm_num [zpow_neg] at hRootLower ⊢
        linarith
    | D =>
        simp only [displayedMagneticAmplitudeInTeslas]
        have hPositive :
            0 < Real.sqrt q - (2.6 : ℝ) * 10 ^ (-11 : ℤ) := by
          norm_num [zpow_neg] at hRootLower ⊢
          linarith
        rw [abs_of_pos hPositive]
        apply lt_trans hMagneticNumerical
        norm_num [zpow_neg] at hRootLower ⊢
        linarith

end PhyXMiniProblems.ProblemPhyXMini0944
