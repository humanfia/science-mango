import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

/-!
# IPhO 2026 experimental problem 4, part A.5

This file models the constant-volume thermal pressure coefficient of the
sealed air column `CA`.  Physlib dimensionful quantities distinguish physical
pressure, length, volume, density, and inverse temperature from their scalar
SI readouts.
-/

namespace IPhO2026Problems.IPhO2026_4_A_5

open Dimension

/-- A physical length, independently of the units used to report it. -/
abbrev Length := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical volume, with dimension `L³`. -/
abbrev Volume := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A mass density, with dimension `M L⁻³`. -/
abbrev MassDensity :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ)

/--
The dimension of the constant-volume thermal pressure coefficient, `K⁻¹`.
-/
abbrev ThermalPressureCoefficient :=
  Dimensionful (WithDim Θ𝓭⁻¹ ℝ)

/-- A real-valued SI readout of a Physlib dimensionful quantity. -/
noncomputable def siValue {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/--
The labels used for the apparatus on the source page and in Figure 17.
-/
inductive ApparatusLabel
  | sealedAirColumnCA
  | propyleneGlycolPG
  | innerCylinderIC
  | outerCylinderOC
  | valveD
  | valveE
  deriving DecidableEq, Fintype

/-- Cylinder dimensions retained from Figure 17. -/
structure CylinderDimensions where
  innerRadius : Length
  usableHeight : Length

/--
Figure-derived geometry for the inner cylinder `IC`, outer cylinder `OC`, and
the sealed air column `CA`.
-/
structure Figure17Geometry where
  innerCylinderIC : CylinderDimensions
  outerCylinderOC : CylinderDimensions
  confinedAirColumnLengthCA : Length
  confinedAirVolumeCA : Volume

/--
A thermodynamic state of the sealed air column.

`pressure` is a dimensional pressure and `absoluteTemperature.val` is its
nonnegative scalar reading in kelvin for this experiment.
-/
structure AirColumnState where
  pressure : DimPressure
  absoluteTemperature : Temperature
  volume : Volume

/-- Pressure readout in pascals. -/
noncomputable def pressurePascal (state : AirColumnState) : ℝ :=
  siValue state.pressure

/-- Absolute-temperature readout in kelvin. -/
noncomputable def temperatureKelvin (state : AirColumnState) : ℝ :=
  state.absoluteTemperature.val

/-- Volume readout in cubic metres. -/
noncomputable def volumeCubicMeter (state : AirColumnState) : ℝ :=
  siValue state.volume

/--
All apparatus quantities and recorded states needed for the isochoric heating
run.  The amount and gas constant are scalar SI readouts with their dimensional
roles recorded in their names.
-/
structure IsochoricAirExperiment where
  geometry : Figure17Geometry
  propyleneGlycolHeightPG : Length
  ambientAirDensity : MassDensity
  amountOfAirMol : ℝ
  universalGasConstantJoulePerMolKelvin : ℝ
  referenceState : AirColumnState
  initialRecordedState : AirColumnState
  heatedRecordedState : AirColumnState
  propyleneGlycolIntroducedIntoIC : Prop
  valveDClosed : Prop
  valveEClosed : Prop
  airColumnCASealed : Prop
  pumpHomogenizesWaterTemperature : Prop
  outerCylinderWaterBathHeated : Prop

/--
The numerical source and reference-constant readouts supplied for this part.

The coefficient sought in A.5 is deliberately absent from these readouts.
-/
structure SourceReadouts (experiment : IsochoricAirExperiment) : Prop where
  glycolHeight :
    siValue experiment.propyleneGlycolHeightPG = 0.045
  ambientDensity :
    siValue experiment.ambientAirDensity = 1.12
  referenceTemperature :
    temperatureKelvin experiment.referenceState = 273.15

/-- The prescribed physical procedure for sealing and heating the air column. -/
structure ExperimentalConditions
    (experiment : IsochoricAirExperiment) : Prop where
  glycolIntroduced :
    experiment.propyleneGlycolIntroducedIntoIC
  valveDClosed :
    experiment.valveDClosed
  valveEClosed :
    experiment.valveEClosed
  airColumnSealed :
    experiment.airColumnCASealed
  pumpOperating :
    experiment.pumpHomogenizesWaterTemperature
  waterBathHeated :
    experiment.outerCylinderWaterBathHeated

/-- The molar ideal-gas equation of state `P V = n R T` at one state. -/
noncomputable def SatisfiesIdealGasLawAt
    (experiment : IsochoricAirExperiment)
    (state : AirColumnState) : Prop :=
  pressurePascal state * volumeCubicMeter state =
    experiment.amountOfAirMol *
      experiment.universalGasConstantJoulePerMolKelvin *
        temperatureKelvin state

/--
Governing laws for the run: the air amount is sealed, the volume is fixed, and
the reference and recorded states obey the ideal-gas equation.
-/
structure GoverningLaws (experiment : IsochoricAirExperiment) : Prop where
  fixedReferenceVolume :
    experiment.referenceState.volume =
      experiment.geometry.confinedAirVolumeCA
  fixedInitialVolume :
    experiment.initialRecordedState.volume =
      experiment.geometry.confinedAirVolumeCA
  fixedHeatedVolume :
    experiment.heatedRecordedState.volume =
      experiment.geometry.confinedAirVolumeCA
  idealGasAtReference :
    SatisfiesIdealGasLawAt experiment experiment.referenceState
  idealGasAtInitialReading :
    SatisfiesIdealGasLawAt experiment experiment.initialRecordedState
  idealGasAtHeatedReading :
    SatisfiesIdealGasLawAt experiment experiment.heatedRecordedState

/--
The reusable conclusion of part A.3: on the isochoric plot, pressure is
proportional to absolute temperature.  The same positive slope describes the
reference state and the two readings used to form `ΔP / ΔT`.
-/
noncomputable def PreviousPartA3Linearity
    (experiment : IsochoricAirExperiment) : Prop :=
  ∃ slopePascalPerKelvin : ℝ,
    0 < slopePascalPerKelvin ∧
      pressurePascal experiment.referenceState =
        slopePascalPerKelvin *
          temperatureKelvin experiment.referenceState ∧
      pressurePascal experiment.initialRecordedState =
        slopePascalPerKelvin *
          temperatureKelvin experiment.initialRecordedState ∧
      pressurePascal experiment.heatedRecordedState =
        slopePascalPerKelvin *
          temperatureKelvin experiment.heatedRecordedState

/-- Positivity and nondegeneracy conditions for the physical heating run. -/
structure PhysicalAdmissibility
    (experiment : IsochoricAirExperiment) : Prop where
  airVolumePositive :
    0 < siValue experiment.geometry.confinedAirVolumeCA
  amountPositive :
    0 < experiment.amountOfAirMol
  gasConstantPositive :
    0 < experiment.universalGasConstantJoulePerMolKelvin
  referencePressurePositive :
    0 < pressurePascal experiment.referenceState
  referenceTemperaturePositive :
    0 < temperatureKelvin experiment.referenceState
  nonzeroTemperatureChange :
    temperatureKelvin experiment.heatedRecordedState -
        temperatureKelvin experiment.initialRecordedState ≠ 0

/-- The measured pressure change `ΔP`, in pascals. -/
noncomputable def pressureChangePascal
    (experiment : IsochoricAirExperiment) : ℝ :=
  pressurePascal experiment.heatedRecordedState -
    pressurePascal experiment.initialRecordedState

/-- The measured absolute-temperature change `ΔT`, in kelvin. -/
noncomputable def temperatureChangeKelvin
    (experiment : IsochoricAirExperiment) : ℝ :=
  temperatureKelvin experiment.heatedRecordedState -
    temperatureKelvin experiment.initialRecordedState

/--
Equation (2), `β₀ = (1 / P₀) (ΔP / ΔT)`, interpreted through SI readouts.
-/
noncomputable def MatchesCoefficientDefinition
    (experiment : IsochoricAirExperiment)
    (betaZero : ThermalPressureCoefficient) : Prop :=
  siValue betaZero =
    (1 / pressurePascal experiment.referenceState) *
      (pressureChangePascal experiment /
        temperatureChangeKelvin experiment)

/-- Whether a scalar SI readout lies in a stated uncertainty interval. -/
def WithinUncertainty
    (readout centralValue uncertainty : ℝ) : Prop :=
  |readout - centralValue| ≤ uncertainty

/--
The official experimental result `0.0034 ± 0.0007 K⁻¹`.
-/
noncomputable def MatchesOfficialExperimentalResult
    (betaZero : ThermalPressureCoefficient) : Prop :=
  WithinUncertainty (siValue betaZero) 0.0034 0.0007

/--
Part A.5: determine the constant-volume thermal pressure coefficient of air.

The first conclusion identifies the physical inverse-temperature quantity
using the definition in equation (2).  The second gives the official
experimental uncertainty interval.  The last records that the ideal-gas
reference `1 / 273.15 K` rounds to `0.0037 K⁻¹`.
-/
theorem target
    (experiment : IsochoricAirExperiment)
    (_readouts : SourceReadouts experiment)
    (_conditions : ExperimentalConditions experiment)
    (_laws : GoverningLaws experiment)
    (_admissible : PhysicalAdmissibility experiment)
    (_previousPartA3 : PreviousPartA3Linearity experiment) :
    ∃ betaZero : ThermalPressureCoefficient,
      MatchesCoefficientDefinition experiment betaZero ∧
        MatchesOfficialExperimentalResult betaZero ∧
          WithinUncertainty (1 / 273.15) 0.0037 0.00005 := by
  rcases _previousPartA3 with
    ⟨slopePascalPerKelvin, slope_positive, pressure_reference,
      pressure_initial, pressure_heated⟩
  let betaZero : ThermalPressureCoefficient :=
    CarriesDimension.toDimensionful UnitChoices.SI
      ⟨(1 : ℝ) / 273.15⟩
  have betaZero_si : siValue betaZero = (1 : ℝ) / 273.15 := by
    simp [betaZero, siValue,
      CarriesDimension.toDimensionful_apply_apply]
  refine ⟨betaZero, ?_, ?_, ?_⟩
  · rw [MatchesCoefficientDefinition, betaZero_si,
      pressureChangePascal, temperatureChangeKelvin,
      pressure_reference, pressure_initial, pressure_heated,
      _readouts.referenceTemperature]
    field_simp
    rw [div_self _admissible.nonzeroTemperatureChange]
  · rw [MatchesOfficialExperimentalResult, WithinUncertainty, betaZero_si]
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · rw [WithinUncertainty]
    norm_num [abs_of_nonneg, abs_of_nonpos]

end IPhO2026Problems.IPhO2026_4_A_5
