import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026 experimental problem 4, part C.6

The experiment measures heat transfer from the outer cylinder (OC) to the
inner cylinder (IC) through a thin acrylic cylindrical wall.  The declarations
below keep physical quantities dimensionful and take scalar readouts only in
the SI unit system.
-/

noncomputable section

open Dimension

namespace IPhO2026Problems
namespace IPhO2026_4_C_6

/-! ## Dimensioned quantities and their SI readouts -/

/-- A length quantity, whose SI readout is in metres. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A time quantity, whose SI readout is in seconds. -/
abbrev DimTime : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A mass quantity, whose SI readout is in kilograms. -/
abbrev DimMass : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- An absolute temperature or temperature difference, with SI readout in kelvin. -/
abbrev DimTemperature : Type := Dimensionful (WithDim Θ𝓭 ℝ)

/-- The dimension of a heat-flow rate (power), `kg m² s⁻³`. -/
def heatFlowRateDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension of a temperature rate, `K s⁻¹`. -/
def temperatureRateDimension : Dimension := Θ𝓭 * T𝓭⁻¹

/-- The dimension of the slope in the C.5 graph, `s⁻¹`. -/
def inverseTimeDimension : Dimension := T𝓭⁻¹

/-- The dimension of specific heat capacity, `J kg⁻¹ K⁻¹`. -/
def specificHeatCapacityDimension : Dimension :=
  L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

/-- The dimension of thermal resistance, `K W⁻¹`. -/
def thermalResistanceDimension : Dimension :=
  Θ𝓭 * T𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The dimension of thermal conductivity, `W m⁻¹ K⁻¹`. -/
def thermalConductivityDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

/-- The dimension of a radial temperature gradient, `K m⁻¹`. -/
def temperatureGradientDimension : Dimension := Θ𝓭 * L𝓭⁻¹

abbrev DimHeatFlowRate : Type :=
  Dimensionful (WithDim heatFlowRateDimension ℝ)

abbrev DimTemperatureRate : Type :=
  Dimensionful (WithDim temperatureRateDimension ℝ)

abbrev DimInverseTime : Type :=
  Dimensionful (WithDim inverseTimeDimension ℝ)

abbrev DimSpecificHeatCapacity : Type :=
  Dimensionful (WithDim specificHeatCapacityDimension ℝ)

abbrev DimThermalResistance : Type :=
  Dimensionful (WithDim thermalResistanceDimension ℝ)

abbrev DimThermalConductivity : Type :=
  Dimensionful (WithDim thermalConductivityDimension ℝ)

abbrev DimTemperatureGradient : Type :=
  Dimensionful (WithDim temperatureGradientDimension ℝ)

/-- The real-valued SI component of a dimensionful quantity. -/
def siValue {d : Dimension} (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  (q UnitChoices.SI).val

/-- The SI area component, in square metres. -/
def areaInSquareMetres (a : DimArea) : ℝ :=
  ((a UnitChoices.SI).val : ℝ)

/-- Construct a dimensionful quantity from a real SI component. -/
def quantityOfSI (d : Dimension) (value : ℝ) :
    Dimensionful (WithDim d ℝ) :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-! ## Figure 17 and the recorded run -/

/--
The geometry and water heights attached to Figure 17.  The source page for
C.6 does not reproduce the numerical cylinder radii, so they remain explicit
dimensionful inputs.  The two water heights are fixed by the experimental
procedure.
-/
structure Figure17Dimensions where
  innerWallRadius : DimLength
  outerWallRadius : DimLength
  conductionHeight : DimLength
  conductionArea : DimArea
  innerCylinderWaterHeight : DimLength
  outerCylinderWaterHeight : DimLength

/--
Geometric constraints from the nested cylindrical apparatus.  The area
relation uses the mean wall radius, appropriate for the stated slim-wall
Fourier model.
-/
def Figure17Dimensions.Valid (g : Figure17Dimensions) : Prop :=
  0 < siValue g.innerWallRadius ∧
  siValue g.innerWallRadius < siValue g.outerWallRadius ∧
  0 < siValue g.conductionHeight ∧
  areaInSquareMetres g.conductionArea =
    2 * Real.pi *
      ((siValue g.innerWallRadius + siValue g.outerWallRadius) / 2) *
      siValue g.conductionHeight ∧
  siValue g.innerCylinderWaterHeight = 0.10 ∧
  siValue g.outerCylinderWaterHeight = 0.15

/--
All physical records used in C.6.  Real arguments named `t_s` and `r_m`
are scalar coordinates in seconds and metres; every recorded physical value
is still a dimensionful quantity.
-/
structure ThermalExperiment where
  geometry : Figure17Dimensions
  innerWaterMass : DimMass
  waterSpecificHeatCapacity : DimSpecificHeatCapacity
  effectiveWallThermalResistance : DimThermalResistance
  acrylicThermalConductivity : DimThermalConductivity
  transferredHeat : ℝ → DimEnergy
  outerToInnerHeatFlowRate : ℝ → DimHeatFlowRate
  innerTemperature : ℝ → DimTemperature
  outerTemperature : ℝ → DimTemperature
  innerTemperatureRate : ℝ → DimTemperatureRate
  wallTemperature : ℝ → ℝ → DimTemperature
  outwardRadialTemperatureGradient : ℝ → DimTemperatureGradient

/-- Positivity conditions for the material parameters appearing in denominators. -/
def ThermalExperiment.ValidParameters (e : ThermalExperiment) : Prop :=
  0 < siValue e.innerWaterMass ∧
  0 < siValue e.waterSpecificHeatCapacity ∧
  0 < siValue e.effectiveWallThermalResistance ∧
  0 < siValue e.acrylicThermalConductivity

/--
The governing model.  The sign convention is explicit: heat flow is positive
from OC to IC, while the radial derivative is taken outwards, hence the minus
sign in Fourier's law.  The calorimetry equation has no apparatus heat-capacity
term, encoding the instructed approximation.
-/
structure ThermalExperiment.SatisfiesLaws (e : ThermalExperiment) : Prop where
  heatFlowIsHeatDerivative :
    ∀ t_s : ℝ,
      HasDerivAt
        (fun τ_s => siValue (e.transferredHeat τ_s))
        (siValue (e.outerToInnerHeatFlowRate t_s))
        t_s
  innerTemperatureRateIsDerivative :
    ∀ t_s : ℝ,
      HasDerivAt
        (fun τ_s => siValue (e.innerTemperature τ_s))
        (siValue (e.innerTemperatureRate t_s))
        t_s
  outwardGradientIsRadialDerivative :
    ∀ t_s : ℝ,
      HasDerivAt
        (fun r_m => siValue (e.wallTemperature t_s r_m))
        (siValue (e.outwardRadialTemperatureGradient t_s))
        ((siValue e.geometry.innerWallRadius +
          siValue e.geometry.outerWallRadius) / 2)
  heatFlowResistanceLaw :
    ∀ t_s : ℝ,
      siValue (e.outerToInnerHeatFlowRate t_s) =
        (siValue (e.outerTemperature t_s) -
          siValue (e.innerTemperature t_s)) /
        siValue e.effectiveWallThermalResistance
  innerWaterCalorimetry :
    ∀ t_s : ℝ,
      siValue (e.outerToInnerHeatFlowRate t_s) =
        siValue e.waterSpecificHeatCapacity *
        siValue e.innerWaterMass *
        siValue (e.innerTemperatureRate t_s)
  radialFourierLaw :
    ∀ t_s : ℝ,
      siValue (e.outerToInnerHeatFlowRate t_s) =
        -siValue e.acrylicThermalConductivity *
        areaInSquareMetres e.geometry.conductionArea *
        siValue (e.outwardRadialTemperatureGradient t_s)

/-! ## The C.5 graph and its experimental uncertainty -/

/--
The finite-difference graph constructed in C.5.  Its horizontal coordinate is
the interval-average `T_OC - T_IC`, its vertical coordinate is the corresponding
finite-difference IC heating rate, and its fitted line passes through the origin.
-/
structure C5GraphReadout (e : ThermalExperiment) where
  sampleTimeInSeconds : ℕ → ℝ
  finiteDifferenceRateKPerSecond : ℕ → ℝ
  averageTemperatureGapK : ℕ → ℝ
  fittedSlope : DimInverseTime
  sampleTimesIncrease :
    ∀ j : ℕ, sampleTimeInSeconds j < sampleTimeInSeconds (j + 1)
  finiteDifferenceRateDefinition :
    ∀ j : ℕ,
      finiteDifferenceRateKPerSecond j =
        (siValue (e.innerTemperature (sampleTimeInSeconds (j + 1))) -
          siValue (e.innerTemperature (sampleTimeInSeconds j))) /
        (sampleTimeInSeconds (j + 1) - sampleTimeInSeconds j)
  averageGapDefinition :
    ∀ j : ℕ,
      averageTemperatureGapK j =
        ((siValue (e.outerTemperature (sampleTimeInSeconds j)) -
            siValue (e.innerTemperature (sampleTimeInSeconds j))) +
          (siValue (e.outerTemperature (sampleTimeInSeconds (j + 1))) -
            siValue (e.innerTemperature (sampleTimeInSeconds (j + 1))))) / 2
  linearThroughOrigin :
    ∀ j : ℕ,
      finiteDifferenceRateKPerSecond j =
        siValue fittedSlope * averageTemperatureGapK j
  containsNonzeroGap :
    ∃ j : ℕ, averageTemperatureGapK j ≠ 0

/--
The reusable conclusion of part C.5, stated locally because the problem policy
forbids importing a sibling Lean output.
-/
structure C5PreviousPartResult
    (e : ThermalExperiment) (graph : C5GraphReadout e) : Prop where
  slopeLaw :
    siValue graph.fittedSlope =
      1 /
        (siValue e.waterSpecificHeatCapacity *
          siValue e.innerWaterMass *
          siValue e.effectiveWallThermalResistance)

/-- A fitted C.5 slope together with its symmetric absolute uncertainty. -/
structure SlopeMeasurement where
  nominalSlope : DimInverseTime
  slopeUncertainty : DimInverseTime

/--
The measured interval covers the true fitted slope.  Its strict lower endpoint
is positive, which preserves the physically relevant positive-slope branch
when taking reciprocals.
-/
def SlopeMeasurement.ValidFor
    (measurement : SlopeMeasurement) (actualSlope : DimInverseTime) : Prop :=
  0 ≤ siValue measurement.slopeUncertainty ∧
  siValue measurement.slopeUncertainty < siValue measurement.nominalSlope ∧
  |siValue actualSlope - siValue measurement.nominalSlope| ≤
    siValue measurement.slopeUncertainty

/-- A resistance estimate with a symmetric absolute uncertainty in `K/W`. -/
structure ResistanceEstimate where
  nominalResistance : DimThermalResistance
  resistanceUncertainty : DimThermalResistance

/-- The official sample readout `1.17 ± 0.03 K/W`. -/
def officialSampleEstimate : ResistanceEstimate where
  nominalResistance := quantityOfSI thermalResistanceDimension 1.17
  resistanceUncertainty := quantityOfSI thermalResistanceDimension 0.03

/-! ## Current C.6 conclusions -/

/--
The effective wall resistance is obtained by solving the C.5 slope relation.
No C.6 answer is included in the hypotheses: `previousPart.slopeLaw` is exactly
the reusable C.5 conclusion recorded in the source.
-/
theorem determineEffectiveWallThermalResistance
    (e : ThermalExperiment)
    (geometryValid : e.geometry.Valid)
    (parametersValid : e.ValidParameters)
    (laws : e.SatisfiesLaws)
    (graph : C5GraphReadout e)
    (previousPart : C5PreviousPartResult e graph) :
    siValue e.effectiveWallThermalResistance =
      1 /
        (siValue e.waterSpecificHeatCapacity *
          siValue e.innerWaterMass *
          siValue graph.fittedSlope) := by
  sorry

/--
Propagation of a symmetric C.5 slope uncertainty through the reciprocal
resistance formula.  The resulting interval is asymmetric in principle; this
theorem gives a conservative symmetric bound about the nominal reciprocal.
-/
theorem determineEffectiveWallThermalResistanceWithUncertainty
    (e : ThermalExperiment)
    (geometryValid : e.geometry.Valid)
    (parametersValid : e.ValidParameters)
    (laws : e.SatisfiesLaws)
    (graph : C5GraphReadout e)
    (previousPart : C5PreviousPartResult e graph)
    (measurement : SlopeMeasurement)
    (measurementValid : measurement.ValidFor graph.fittedSlope) :
    |siValue e.effectiveWallThermalResistance -
        1 /
          (siValue e.waterSpecificHeatCapacity *
            siValue e.innerWaterMass *
            siValue measurement.nominalSlope)| ≤
      siValue measurement.slopeUncertainty /
        (siValue e.waterSpecificHeatCapacity *
          siValue e.innerWaterMass *
          siValue measurement.nominalSlope *
          (siValue measurement.nominalSlope -
            siValue measurement.slopeUncertainty)) := by
  sorry

/-- The two scalar SI components of the official sample estimate. -/
theorem officialSampleEstimateReadout :
    siValue officialSampleEstimate.nominalResistance = 1.17 ∧
    siValue officialSampleEstimate.resistanceUncertainty = 0.03 := by
  sorry

end IPhO2026_4_C_6
end IPhO2026Problems
