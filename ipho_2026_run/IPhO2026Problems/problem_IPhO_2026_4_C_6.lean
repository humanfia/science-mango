import Mathlib
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026 experimental problem 4, part C.6

The experiment measures heat transfer from the water in the outer cylinder
(`OC`) to the water in the inner cylinder (`IC`) through an acrylic
cylindrical wall.  This file records the physical dimensions, Figure 17
geometry, experimental traces, governing heat-flow laws, and the C.5 graph
readout used to determine the wall's effective thermal resistance.
-/

noncomputable section

open Dimension
open CarriesDimension

namespace IPhO2026Problems.IPhO2026_4_C_6

/-! ## Dimension-carrying physical quantities -/

/-- Energy dimension, grounded by Physlib's `DimEnergy`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Power, or heat-flow-rate, dimension. -/
def powerDimension : Dimension :=
  energyDimension * T𝓭⁻¹

/-- Thermal resistance dimension `temperature / power` (kelvin per watt in SI). -/
def thermalResistanceDimension : Dimension :=
  Θ𝓭 * powerDimension⁻¹

/-- Specific heat capacity dimension `energy / (mass * temperature)`. -/
def specificHeatCapacityDimension : Dimension :=
  energyDimension * (M𝓭 * Θ𝓭)⁻¹

/-- Thermal conductivity dimension `power / (length * temperature)`. -/
def thermalConductivityDimension : Dimension :=
  powerDimension * (L𝓭 * Θ𝓭)⁻¹

abbrev DimTemperature : Type :=
  Dimensionful (WithDim Θ𝓭 ℝ)

abbrev DimTime : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

abbrev DimLength : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

abbrev DimMass : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

abbrev DimArea : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) ℝ)

/-- Heat energy, using Physlib's grounded dimensional-energy type. -/
abbrev DimHeatEnergy : Type :=
  DimEnergy

abbrev DimHeatFlowRate : Type :=
  Dimensionful (WithDim powerDimension ℝ)

abbrev DimThermalResistance : Type :=
  Dimensionful (WithDim thermalResistanceDimension ℝ)

abbrev DimSpecificHeatCapacity : Type :=
  Dimensionful (WithDim specificHeatCapacityDimension ℝ)

abbrev DimThermalConductivity : Type :=
  Dimensionful (WithDim thermalConductivityDimension ℝ)

abbrev DimTemperatureRate : Type :=
  Dimensionful (WithDim (Θ𝓭 * T𝓭⁻¹) ℝ)

abbrev DimTemperatureGradient : Type :=
  Dimensionful (WithDim (Θ𝓭 * L𝓭⁻¹) ℝ)

abbrev DimInverseTime : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- The real-number readout of a dimensionful quantity in standard SI units. -/
def siReadout {d : Dimension} (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity.1 UnitChoices.SI).val

/-! ## Figure and measurement data -/

/--
The labels `r₁`, `r₂`, and `h` from Figure 17.
The exact numerical dimensions are deliberately left as experimental inputs.
-/
structure Figure17Geometry where
  wallInnerRadius_r1 : DimLength
  wallOuterRadius_r2 : DimLength
  wallHeight_h : DimLength
  innerRadius_positive : 0 < siReadout wallInnerRadius_r1
  wallHasPositiveThickness :
    siReadout wallInnerRadius_r1 < siReadout wallOuterRadius_r2
  wallHeight_positive : 0 < siReadout wallHeight_h

/--
Readouts fixed by the procedure on the official source page.  Temperature is
stored as an absolute dimensionful quantity; the displayed Celsius value is
related to its SI kelvin readout explicitly.
-/
structure ProcedureReadouts where
  innerCylinderWaterLevel : DimLength
  outerCylinderWaterLevel : DimLength
  initialOuterWaterTemperature : DimTemperature
  innerWaterLevel_meters :
    siReadout innerCylinderWaterLevel = 0.10
  outerWaterLevel_meters :
    siReadout outerCylinderWaterLevel = 0.15
  initialOuterTemperature_kelvin :
    siReadout initialOuterWaterTemperature = 65 + 273.15

/-- One simultaneous `t`, `T_IC`, `T_OC` observation from the experiment. -/
structure TemperatureObservation where
  time : DimTime
  innerTemperature_TIC : DimTemperature
  outerTemperature_TOC : DimTemperature

/--
The vertical coordinate of the C.5 graph:
`(T_IC,j - T_IC,j-1) / (t_j - t_j-1)`, in kelvin per second.
-/
def finiteDifferenceInnerRateSI
    (previous current : TemperatureObservation) : ℝ :=
  (siReadout current.innerTemperature_TIC -
      siReadout previous.innerTemperature_TIC) /
    (siReadout current.time - siReadout previous.time)

/--
The horizontal coordinate of the C.5 graph: the interval-average value of
`T_OC - T_IC`, in kelvin.
-/
def averageDrivingTemperatureDifferenceSI
    (previous current : TemperatureObservation) : ℝ :=
  ((siReadout previous.outerTemperature_TOC +
        siReadout current.outerTemperature_TOC) / 2) -
    ((siReadout previous.innerTemperature_TIC +
        siReadout current.innerTemperature_TIC) / 2)

/-- An SI scalar pair `(mean (T_OC - T_IC), finite-difference dT_IC/dt)`. -/
def c5PlotPointSI
    (previous current : TemperatureObservation) : ℝ × ℝ :=
  (averageDrivingTemperatureDifferenceSI previous current,
    finiteDifferenceInnerRateSI previous current)

/-- Linear-fit data read from the graph constructed in C.5. -/
structure C5GraphReadout where
  fittedSlope : DimInverseTime
  slopeUncertaintyPerSecond : ℝ
  fittedSlope_positive : 0 < siReadout fittedSlope
  slopeUncertainty_nonnegative : 0 ≤ slopeUncertaintyPerSecond

/-! ## Experimental system and governing laws -/

/--
The physical system for C.6.  Scalar-valued functions are used only for
measured components after their dimensional roles have been fixed.
-/
structure ThermalExperiment where
  geometry : Figure17Geometry
  procedure : ProcedureReadouts
  observations : List TemperatureObservation
  innerWaterSpecificHeat_c0 : DimSpecificHeatCapacity
  innerWaterMass_m : DimMass
  effectiveWallResistance_RTh : DimThermalResistance
  acrylicConductivity_lambda : DimThermalConductivity
  radialConductionArea_A : DimArea
  innerTemperatureAt : DimTime → DimTemperature
  outerTemperatureAt : DimTime → DimTemperature
  innerTemperatureRateAt : DimTime → DimTemperatureRate
  wallHeatFlowRateAt : DimTime → DimHeatFlowRate
  radialTemperatureGradientAt : DimTime → DimTemperatureGradient
  specificHeat_positive : 0 < siReadout innerWaterSpecificHeat_c0
  innerWaterMass_positive : 0 < siReadout innerWaterMass_m
  wallResistance_positive : 0 < siReadout effectiveWallResistance_RTh
  conductivity_positive : 0 < siReadout acrylicConductivity_lambda
  conductionArea_positive : 0 < siReadout radialConductionArea_A

/--
The heat-transfer model used in the problem:

* `dQ/dt = (T_OC - T_IC) / R_Th`;
* neglecting apparatus heat capacity,
  `dQ/dt = c₀ m dT_IC/dt`;
* radial Fourier conduction,
  `dQ/dt = -λ A dT/dr`.

These are governing laws, not the C.6 resistance answer.
-/
structure GoverningLaws (experiment : ThermalExperiment) : Prop where
  heatFlowThroughWall : ∀ time : DimTime,
    siReadout (experiment.wallHeatFlowRateAt time) =
      (siReadout (experiment.outerTemperatureAt time) -
          siReadout (experiment.innerTemperatureAt time)) /
        siReadout experiment.effectiveWallResistance_RTh
  innerWaterEnergyBalance : ∀ time : DimTime,
    siReadout (experiment.wallHeatFlowRateAt time) =
      siReadout experiment.innerWaterSpecificHeat_c0 *
        siReadout experiment.innerWaterMass_m *
        siReadout (experiment.innerTemperatureRateAt time)
  radialFourierConduction : ∀ time : DimTime,
    siReadout (experiment.wallHeatFlowRateAt time) =
      -(siReadout experiment.acrylicConductivity_lambda) *
        siReadout experiment.radialConductionArea_A *
        siReadout (experiment.radialTemperatureGradientAt time)

/-! ## C.6 target and official sample metadata -/

/--
The official sample is a reported scalar estimate, so its central value and
uncertainty are explicitly labeled in kelvin per watt.
-/
structure ThermalResistanceEstimate where
  centralKelvinPerWatt : ℝ
  uncertaintyKelvinPerWatt : ℝ
  uncertainty_nonnegative : 0 ≤ uncertaintyKelvinPerWatt

/-- Official sample report: `R_Th = 1.17 ± 0.03 K/W`. -/
def officialSampleResistance : ThermalResistanceEstimate where
  centralKelvinPerWatt := 1.17
  uncertaintyKelvinPerWatt := 0.03
  uncertainty_nonnegative := by norm_num

/--
From the previous-part C.5 slope relation

`slope = 1 / (c₀ * m * R_Th)`,

determine the effective acrylic-wall thermal resistance.  The previous-part
relation is an allowed graph-model result; the conclusion below is the current
C.6 target and is not a field of `GoverningLaws` or `ThermalExperiment`.
-/
theorem effectiveWallThermalResistance_from_C5Graph
    (experiment : ThermalExperiment)
    (_laws : GoverningLaws experiment)
    (graph : C5GraphReadout)
    (c5SlopeRelation :
      siReadout graph.fittedSlope =
        1 /
          (siReadout experiment.innerWaterSpecificHeat_c0 *
            siReadout experiment.innerWaterMass_m *
            siReadout experiment.effectiveWallResistance_RTh)) :
    siReadout experiment.effectiveWallResistance_RTh =
      1 /
        (siReadout experiment.innerWaterSpecificHeat_c0 *
          siReadout experiment.innerWaterMass_m *
          siReadout graph.fittedSlope) := by
  rw [c5SlopeRelation]
  field_simp [ne_of_gt experiment.specificHeat_positive,
    ne_of_gt experiment.innerWaterMass_positive,
    ne_of_gt experiment.wallResistance_positive]

end IPhO2026Problems.IPhO2026_4_C_6
