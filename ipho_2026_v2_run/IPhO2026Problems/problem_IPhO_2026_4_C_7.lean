import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, experimental problem 1, part C.7

This file models radial heat conduction through the acrylic wall separating the
inner and outer cylinders.  Scalar functions whose names end in `Kelvin`,
`Joule`, `Watt`, or `Meter` are SI readouts of the corresponding physical
quantities.  The measured geometry, thermal resistance, and thermal
conductivity themselves are dimension-tagged using `Physlib.WithDim`.
-/

namespace IPhO2026Problems
namespace IPhO2026_4_C_7

open Dimension

noncomputable section

/-- The physical dimension of energy, `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of power or heat-flow rate, `M L² T⁻³`. -/
def heatFlowRateDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension `K/W` of thermal resistance. -/
def thermalResistanceDimension : Dimension :=
  Θ𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 * T𝓭 * T𝓭

/-- The dimension `W/(m*K)` of thermal conductivity. -/
def thermalConductivityDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

abbrev LengthQuantity := WithDim L𝓭 ℝ
abbrev EnergyQuantity := WithDim energyDimension ℝ
abbrev HeatFlowRateQuantity := WithDim heatFlowRateDimension ℝ
abbrev ThermalResistanceQuantity := WithDim thermalResistanceDimension ℝ
abbrev ThermalConductivityQuantity := WithDim thermalConductivityDimension ℝ

/-- A central experimental readout together with its standard uncertainty. -/
structure ExperimentalMeasurement (d : Dimension) where
  central : WithDim d ℝ
  standardUncertainty : WithDim d ℝ
  uncertainty_nonnegative : 0 ≤ standardUncertainty.val

/-- Geometric data for the two coaxial cylinders and the water columns. -/
structure CylindricalWallGeometry where
  innerCylinderBoreDiameter : ExperimentalMeasurement L𝓭
  innerCylinderAcrylicThickness : ExperimentalMeasurement L𝓭
  outerCylinderOutsideDiameter : ExperimentalMeasurement L𝓭
  outerCylinderWallThickness : ExperimentalMeasurement L𝓭
  innerWaterHeight : LengthQuantity
  outerWaterHeight : LengthQuantity

/-- Inner radius of the conducting acrylic wall, as an SI readout in meters. -/
def innerRadiusMeter (g : CylindricalWallGeometry) : ℝ :=
  g.innerCylinderBoreDiameter.central.val / 2

/-- Outer radius of the conducting acrylic wall, as an SI readout in meters. -/
def outerRadiusMeter (g : CylindricalWallGeometry) : ℝ :=
  innerRadiusMeter g + g.innerCylinderAcrylicThickness.central.val

/-- The wetted height of the conducting wall is the inner-cylinder water height. -/
def conductingHeightMeter (g : CylindricalWallGeometry) : ℝ :=
  g.innerWaterHeight.val

/-- Area `2πrh` normal to radial conduction at radius `r`. -/
def cylindricalWallAreaSquareMeter (g : CylindricalWallGeometry) (rMeter : ℝ) : ℝ :=
  2 * Real.pi * rMeter * conductingHeightMeter g

/--
The dimensional readouts from Figure 17 and the height setpoints in the
part-C procedure.  Lengths are converted from millimeters or centimeters to
meters.
-/
structure Figure17AndCProcedureReadout (g : CylindricalWallGeometry) : Prop where
  inner_bore_central :
    g.innerCylinderBoreDiameter.central.val = (337 : ℝ) / 10000
  inner_bore_uncertainty :
    g.innerCylinderBoreDiameter.standardUncertainty.val = (1 : ℝ) / 10000
  inner_wall_central :
    g.innerCylinderAcrylicThickness.central.val = (17 : ℝ) / 5000
  inner_wall_uncertainty :
    g.innerCylinderAcrylicThickness.standardUncertainty.val = (1 : ℝ) / 10000
  outer_diameter_central :
    g.outerCylinderOutsideDiameter.central.val = (187 : ℝ) / 2500
  outer_diameter_uncertainty :
    g.outerCylinderOutsideDiameter.standardUncertainty.val = (1 : ℝ) / 10000
  outer_wall_central :
    g.outerCylinderWallThickness.central.val = (17 : ℝ) / 5000
  outer_wall_uncertainty :
    g.outerCylinderWallThickness.standardUncertainty.val = (1 : ℝ) / 10000
  inner_water_height :
    g.innerWaterHeight.val = (1 : ℝ) / 10
  outer_water_height :
    g.outerWaterHeight.val = (3 : ℝ) / 20

/--
The measured and field-valued data for the cylindrical conduction experiment.

`inwardHeatFlowWatt` is positive from the outer cylinder into the inner
cylinder.  `outwardHeatFlowWatt` uses the positive-radial orientation appearing
in the signed Fourier law.
-/
structure CylindricalConductionExperiment where
  wall : CylindricalWallGeometry
  thermalResistance : ExperimentalMeasurement thermalResistanceDimension
  acrylicConductivity : ThermalConductivityQuantity
  innerTemperatureKelvin : ℝ → ℝ
  outerTemperatureKelvin : ℝ → ℝ
  radialTemperatureKelvin : ℝ → ℝ → ℝ
  radialTemperatureGradientKelvinPerMeter : ℝ → ℝ → ℝ
  heatReceivedByInnerJoule : ℝ → ℝ
  inwardHeatFlowWatt : ℝ → ℝ
  outwardHeatFlowWatt : ℝ → ℝ

/-- The reusable result `R_Th = 1.17 ± 0.03 K/W` obtained in part C.6. -/
structure PreviousPartC6Readout (e : CylindricalConductionExperiment) : Prop where
  resistance_central :
    e.thermalResistance.central.val = (117 : ℝ) / 100
  resistance_uncertainty :
    e.thermalResistance.standardUncertainty.val = (3 : ℝ) / 100

/--
The effective-resistance heat-flow model
`dQ_in/dt = (T_OC - T_IC) / R_Th`.
-/
structure HeatResistanceLaw (e : CylindricalConductionExperiment) : Prop where
  resistance_positive :
    0 < e.thermalResistance.central.val
  heat_rate_is_derivative : ∀ t,
    HasDerivAt e.heatReceivedByInnerJoule (e.inwardHeatFlowWatt t) t
  power_from_temperature_difference : ∀ t,
    e.inwardHeatFlowWatt t =
      (e.outerTemperatureKelvin t - e.innerTemperatureKelvin t) /
        e.thermalResistance.central.val

/--
The signed local Fourier law for a quasi-steady cylindrical wall.

The wall heat-flow rate depends on time but not on radius, encoding the
no-radial-storage approximation.  The explicit sign equation states
`dQ_out/dt = -λ A dT/dr`; the separate orientation equation connects it to
heat received by the inner cylinder.
-/
structure RadialFourierLaw (e : CylindricalConductionExperiment) : Prop where
  conductivity_positive :
    0 < e.acrylicConductivity.val
  outward_is_negative_inward : ∀ t,
    e.outwardHeatFlowWatt t = -e.inwardHeatFlowWatt t
  inner_boundary : ∀ t,
    e.radialTemperatureKelvin t (innerRadiusMeter e.wall) =
      e.innerTemperatureKelvin t
  outer_boundary : ∀ t,
    e.radialTemperatureKelvin t (outerRadiusMeter e.wall) =
      e.outerTemperatureKelvin t
  temperature_has_radial_derivative : ∀ t r,
    innerRadiusMeter e.wall ≤ r →
    r ≤ outerRadiusMeter e.wall →
      HasDerivAt (e.radialTemperatureKelvin t)
        (e.radialTemperatureGradientKelvinPerMeter t r) r
  signed_fourier_equation : ∀ t r,
    innerRadiusMeter e.wall ≤ r →
    r ≤ outerRadiusMeter e.wall →
      e.outwardHeatFlowWatt t =
        -e.acrylicConductivity.val * cylindricalWallAreaSquareMeter e.wall r *
          e.radialTemperatureGradientKelvinPerMeter t r

/--
Integrating the local radial Fourier equation across the acrylic wall gives
the logarithmic temperature-difference relation.
-/
theorem radial_fourier_temperature_difference
    (e : CylindricalConductionExperiment)
    (hFourier : RadialFourierLaw e)
    (t : ℝ)
    (hInnerRadius : 0 < innerRadiusMeter e.wall)
    (hRadii : innerRadiusMeter e.wall < outerRadiusMeter e.wall)
    (hHeight : 0 < conductingHeightMeter e.wall) :
    e.outerTemperatureKelvin t - e.innerTemperatureKelvin t =
      e.inwardHeatFlowWatt t *
          Real.log (outerRadiusMeter e.wall / innerRadiusMeter e.wall) /
        (e.acrylicConductivity.val * 2 * Real.pi * conductingHeightMeter e.wall) := by
  sorry

/--
Combining the resistance model with radial Fourier conduction determines the
acrylic conductivity.
-/
theorem acrylic_conductivity_formula
    (e : CylindricalConductionExperiment)
    (hResistance : HeatResistanceLaw e)
    (hFourier : RadialFourierLaw e)
    (t : ℝ)
    (hInnerRadius : 0 < innerRadiusMeter e.wall)
    (hRadii : innerRadiusMeter e.wall < outerRadiusMeter e.wall)
    (hHeight : 0 < conductingHeightMeter e.wall)
    (hOuterHotter : e.innerTemperatureKelvin t < e.outerTemperatureKelvin t) :
    e.acrylicConductivity.val =
      Real.log (outerRadiusMeter e.wall / innerRadiusMeter e.wall) /
        (2 * Real.pi * conductingHeightMeter e.wall *
          e.thermalResistance.central.val) := by
  sorry

/--
First-order root-sum-square propagation of the independent diameter,
wall-thickness, and thermal-resistance standard uncertainties through the
cylindrical-wall conductivity formula.  No height uncertainty is included
because the source gives the 10 cm height as a setpoint without an uncertainty.
-/
def conductivityStandardUncertainty
    (g : CylindricalWallGeometry)
    (thermalResistance : ExperimentalMeasurement thermalResistanceDimension) : ℝ :=
  let d := g.innerCylinderBoreDiameter.central.val
  let uD := g.innerCylinderBoreDiameter.standardUncertainty.val
  let w := g.innerCylinderAcrylicThickness.central.val
  let uW := g.innerCylinderAcrylicThickness.standardUncertainty.val
  let h := conductingHeightMeter g
  let rTh := thermalResistance.central.val
  let uRTh := thermalResistance.standardUncertainty.val
  let sensitivityDiameter :=
    (-2 * w / (d * (d + 2 * w))) / (2 * Real.pi * h * rTh)
  let sensitivityThickness :=
    (2 / (d + 2 * w)) / (2 * Real.pi * h * rTh)
  let sensitivityResistance :=
    -Real.log ((d + 2 * w) / d) / (2 * Real.pi * h * rTh ^ 2)
  Real.sqrt
    ((sensitivityDiameter * uD) ^ 2 +
     (sensitivityThickness * uW) ^ 2 +
     (sensitivityResistance * uRTh) ^ 2)

/-- `actual` rounds to `reported` at a given reporting step. -/
def RoundsTo (step actual reported : ℝ) : Prop :=
  0 < step ∧ abs (actual - reported) ≤ step / 2

/--
The Figure 17 dimensions and the C.6 resistance readout give the official
sample report `λ = 0.25 ± 0.01 W/(m*K)`.  The first component rounds the
conductivity itself; the second rounds its propagated standard uncertainty.
-/
theorem official_sample_conductivity
    (e : CylindricalConductionExperiment)
    (hFigure : Figure17AndCProcedureReadout e.wall)
    (hPrevious : PreviousPartC6Readout e)
    (hResistance : HeatResistanceLaw e)
    (hFourier : RadialFourierLaw e)
    (t : ℝ)
    (hOuterHotter : e.innerTemperatureKelvin t < e.outerTemperatureKelvin t) :
    RoundsTo ((1 : ℝ) / 100) e.acrylicConductivity.val ((1 : ℝ) / 4) ∧
      RoundsTo ((1 : ℝ) / 100)
        (conductivityStandardUncertainty e.wall e.thermalResistance)
        ((1 : ℝ) / 100) := by
  sorry

end

end IPhO2026_4_C_7
end IPhO2026Problems
