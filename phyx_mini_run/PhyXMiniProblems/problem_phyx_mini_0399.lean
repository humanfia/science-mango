import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/-!
# Pressure increase in a warmed automobile tire

This file formalizes problem `phyx_mini_0399`.  A fixed sample of ideal-gas
air in a tire is warmed from `-10 °C` to `10 °C`, starting at `190 kPa`.
The problem asks the solver to supply the rigid-tire approximation: the
interior volume is unchanged during the warming process.

Pressure, volume, and absolute temperature retain their physical roles through
Physlib types.  Real numbers occur only as explicitly unit-labelled readouts,
the calibrated `nR` readout for the fixed gas sample, or displayed answer
values.  As required by the recorded answer, the stated pressure is modeled as
the thermodynamic absolute pressure used in the ideal-gas equation.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0399

open Dimension

/-! ## Physical quantities and named-unit readouts -/

/-- Physical volume of the tire interior, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Convert a stored Physlib absolute temperature to a kelvin readout. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- The exact Celsius-zero offset `273.15 K`. -/
def celsiusZeroInKelvins : ℝ := 27315 / 100

/-- Celsius readout obtained from the physical absolute temperature. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - celsiusZeroInKelvins

/-! ## Tire states, gas sample, and figure vocabulary -/

/-- The tire-air states before and after the automobile is driven. -/
inductive DrivingStage where
  | beforeDriving
  | afterDriving
  deriving DecidableEq, Fintype, Repr

/-- Equation-of-state model assigned to the tire air. -/
inductive GasModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/-- A thermodynamic state of the air inside the tire. -/
structure TireAirState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
The same physical air sample occurs at both stages.  The scalar field is an
explicit SI readout of the sample-dependent quantity `nR`, not a replacement
type for the gas sample.
-/
structure TireAirSample where
  gasModel : GasModel
  amountTimesGasConstantJoulesPerKelvin : ℝ

/-- Components visibly present in the supplied tire illustration. -/
inductive TireFigureComponent where
  | tire
  | wheelRim
  | valveStem
  deriving DecidableEq, Fintype, Repr

/-- Physical observable denoted by a label in the supplied illustration. -/
inductive FigureObservable where
  | tireAirPressure
  deriving DecidableEq, Repr

/-!
Qualitative data transcribed from the bitmap.  The label and arrow identify
the pressure observable at the valve stem; the bitmap supplies no pressure
number.
-/
structure TirePressureFigure where
  componentShown : TireFigureComponent → Bool
  annotationText : String
  arrowTarget : TireFigureComponent
  indicatedObservable : FigureObservable

/-- The fixed gas sample, its two states, and the supplied illustration. -/
structure TireHeatingSetup where
  airSample : TireAirSample
  state : DrivingStage → TireAirState
  temperatureStorageUnit : TemperatureUnit
  figure : TirePressureFigure

/-! ## Problem data and primary-image evidence -/

/-!
Numerical data stated in the prose.  The requested final pressure deliberately
does not occur in this structure.
-/
structure MatchesProblemStatement (setup : TireHeatingSetup) : Prop where
  airUsesIdealGasModel : setup.airSample.gasModel = .ideal
  initialTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.state .beforeDriving).temperature = -10
  initialPressureKilopascals :
    pressureInKilopascals (setup.state .beforeDriving).pressure = 190
  finalTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.state .afterDriving).temperature = 10

/-!
Primary-image evidence: the tire, blue wheel rim, and valve stem are visible,
and the arrow labelled `Air P` points to the valve stem to denote air
pressure.  There is no numerical figure readout to assume.
-/
structure MatchesPrimaryTireFigure (setup : TireHeatingSetup) : Prop where
  tireShown : setup.figure.componentShown .tire = true
  wheelRimShown : setup.figure.componentShown .wheelRim = true
  valveStemShown : setup.figure.componentShown .valveStem = true
  airPressureLabelText : setup.figure.annotationText = "Air P"
  labelArrowTargetsValveStem : setup.figure.arrowTarget = .valveStem
  labelDenotesTireAirPressure :
    setup.figure.indicatedObservable = .tireAirPressure

/-! ## Physical-domain conditions, supplied assumption, and governing law -/

/-- Positivity conditions selecting physically meaningful tire-air states. -/
structure HasPhysicalTireAirParameters (setup : TireHeatingSetup) : Prop where
  amountTimesGasConstantPositive :
    0 < setup.airSample.amountTimesGasConstantJoulesPerKelvin
  pressurePositive : ∀ stage : DrivingStage,
    0 < pressureInPascals (setup.state stage).pressure
  volumePositive : ∀ stage : DrivingStage,
    0 < volumeInCubicMeters (setup.state stage).volume
  absoluteTemperaturePositive : ∀ stage : DrivingStage,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.state stage).temperature

/-!
The one modeling assumption requested by the problem: tire deformation is
neglected, so the air occupies the same volume before and after driving.
-/
structure AssumesConstantTireVolume (setup : TireHeatingSetup) : Prop where
  volumeIsUnchanged :
    (setup.state .afterDriving).volume =
      (setup.state .beforeDriving).volume

/-!
The macroscopic ideal-gas equation `pV = (nR)T`, in coherent SI readouts, at
both states of the same air sample.  This governing law contains no numerical
final pressure.
-/
structure SatisfiesFixedSampleIdealGasLaw (setup : TireHeatingSetup) : Prop where
  idealGasEquationAt : ∀ stage : DrivingStage,
    pressureInPascals (setup.state stage).pressure *
        volumeInCubicMeters (setup.state stage).volume =
      setup.airSample.amountTimesGasConstantJoulesPerKelvin *
        temperatureInKelvins setup.temperatureStorageUnit
          (setup.state stage).temperature

/-! ## Displayed answers and formalization target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Pressure displayed beside each answer, normalized to kilopascals.  In
particular, choice A's `4 MPa` is represented as `4000 kPa`.
-/
def displayedPressureKilopascals : AnswerChoice → ℝ
  | .A => 4000
  | .B => 1022 / 5
  | .C => 154
  | .D => 51 / 5

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The physical pressure rounds to the displayed tenth of a kilopascal. -/
def RoundsToDisplayedTenthKilopascal
    (actualPressureKilopascals : ℝ) (choice : AnswerChoice) : Prop :=
  |actualPressureKilopascals - displayedPressureKilopascals choice| < 1 / 20

/-- The selected answer is closer than every alternative pressure display. -/
def IsUniqueClosestDisplayedPressure
    (actualPressureKilopascals : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualPressureKilopascals - displayedPressureKilopascals choice| <
      |actualPressureKilopascals - displayedPressureKilopascals other|

/-!
At fixed volume for a fixed ideal-gas sample, `p/T` is constant.  Converting
the given Celsius temperatures with the exact offset `273.15 K` gives
`T₁ = 5263/20 K` and `T₂ = 5663/20 K`; hence
`p₂ = 190 · 5663/5263 = 1075970/5263 kPa`, approximately `204.4404 kPa`.
It rounds to `204.4 kPa`, uniquely selecting the recorded answer B.

Blueprint label: `thm:physics:phyx_mini_0399:target`.
-/
theorem new_tire_pressure_is_answer_B
    (setup : TireHeatingSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryTireFigure setup)
    (_physical : HasPhysicalTireAirParameters setup)
    (_constantVolume : AssumesConstantTireVolume setup)
    (_law : SatisfiesFixedSampleIdealGasLaw setup) :
    pressureInKilopascals (setup.state .afterDriving).pressure =
        (1075970 / 5263 : ℝ) ∧
      RoundsToDisplayedTenthKilopascal
        (pressureInKilopascals (setup.state .afterDriving).pressure)
        recordedDatasetAnswer ∧
      IsUniqueClosestDisplayedPressure
        (pressureInKilopascals (setup.state .afterDriving).pressure)
        recordedDatasetAnswer := by
  have hInitialTemperature :
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .beforeDriving).temperature = 5263 / 20 := by
    have h := _problem.initialTemperatureCelsius
    unfold temperatureInDegreesCelsius celsiusZeroInKelvins at h
    norm_num at h ⊢
    linarith
  have hFinalTemperature :
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .afterDriving).temperature = 5663 / 20 := by
    have h := _problem.finalTemperatureCelsius
    unfold temperatureInDegreesCelsius celsiusZeroInKelvins at h
    norm_num at h ⊢
    linarith
  have hInitialPressure :
      pressureInPascals (setup.state .beforeDriving).pressure = 190000 := by
    have h := _problem.initialPressureKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hVolume :
      volumeInCubicMeters (setup.state .afterDriving).volume =
        volumeInCubicMeters (setup.state .beforeDriving).volume :=
    congrArg volumeInCubicMeters _constantVolume.volumeIsUnchanged
  have hLawBefore := _law.idealGasEquationAt .beforeDriving
  have hLawAfter := _law.idealGasEquationAt .afterDriving
  rw [hInitialPressure, hInitialTemperature] at hLawBefore
  rw [hVolume, hFinalTemperature] at hLawAfter
  have hVolumePositive :=
    _physical.volumePositive .beforeDriving
  have hFinalPressure :
      pressureInPascals (setup.state .afterDriving).pressure =
        (1075970000 / 5263 : ℝ) := by
    nlinarith [hLawBefore, hLawAfter, hVolumePositive]
  have hFinalPressureKilopascals :
      pressureInKilopascals (setup.state .afterDriving).pressure =
        (1075970 / 5263 : ℝ) := by
    unfold pressureInKilopascals
    rw [hFinalPressure]
    norm_num
  refine ⟨hFinalPressureKilopascals, ?_, ?_⟩
  · rw [hFinalPressureKilopascals]
    norm_num [RoundsToDisplayedTenthKilopascal, recordedDatasetAnswer,
      displayedPressureKilopascals, abs_of_nonneg, abs_of_nonpos]
  · rw [hFinalPressureKilopascals]
    intro other hOther
    fin_cases other
    · norm_num [recordedDatasetAnswer, displayedPressureKilopascals,
        abs_of_nonneg, abs_of_nonpos]
    · simp [recordedDatasetAnswer] at hOther
    · norm_num [recordedDatasetAnswer, displayedPressureKilopascals,
        abs_of_nonneg, abs_of_nonpos]
    · norm_num [recordedDatasetAnswer, displayedPressureKilopascals,
        abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0399
