import Mathlib
import Physlib.Units.WithDim.Pressure

/-!
# IPhO 2026 experimental problem 4, part B.4

The inner cylinder (IC) contains a fixed amount of dry air together with water
vapour.  Its water level is adjusted using the outer container (OC), syringe,
and valve E in Figure 19 so that, in the idealized model used in this
subquestion, the total gas pressure is atmospheric.

All scalar readouts below are expressed in the SI unit named in the field.
They are paired with `Physlib` dimensionful quantities so that pressure,
length, volume, area, and absolute temperature retain their physical roles.
-/

namespace IPhO2026Problems.IPhO2026_4_B_4

noncomputable section

/-- A pressure together with its calibrated scalar readout in pascals. -/
structure PressureMeasurement where
  quantity : DimPressure
  pascalReadout : ℝ
  calibrated :
    quantity =
      CarriesDimension.toDimensionful UnitChoices.SI ⟨pascalReadout⟩

/-- A length together with its calibrated scalar readout in metres. -/
structure LengthMeasurement where
  quantity : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  metreReadout : ℝ
  calibrated :
    quantity =
      CarriesDimension.toDimensionful UnitChoices.SI ⟨metreReadout⟩

/-- An area together with its calibrated scalar readout in square metres. -/
structure AreaMeasurement where
  quantity :
    Dimensionful (WithDim (Dimension.L𝓭 * Dimension.L𝓭) ℝ)
  squareMetreReadout : ℝ
  calibrated :
    quantity =
      CarriesDimension.toDimensionful UnitChoices.SI
        ⟨squareMetreReadout⟩

/-- A volume together with its calibrated scalar readout in cubic metres. -/
structure VolumeMeasurement where
  quantity :
    Dimensionful
      (WithDim
        (Dimension.L𝓭 * Dimension.L𝓭 * Dimension.L𝓭) ℝ)
  cubicMetreReadout : ℝ
  calibrated :
    quantity =
      CarriesDimension.toDimensionful UnitChoices.SI
        ⟨cubicMetreReadout⟩

/-- An absolute temperature together with its calibrated kelvin readout. -/
structure AbsoluteTemperatureMeasurement where
  quantity : Dimensionful (WithDim Dimension.Θ𝓭 ℝ)
  kelvinReadout : ℝ
  calibrated :
    quantity =
      CarriesDimension.toDimensionful UnitChoices.SI ⟨kelvinReadout⟩

/-- The scalar and dimensionful readouts for one equilibrium state of the gas
inside the inner cylinder. -/
structure InnerCylinderGasState where
  temperature : AbsoluteTemperatureMeasurement
  gasColumnHeight : LengthMeasurement
  gasVolume : VolumeMeasurement
  totalPressure : PressureMeasurement
  dryAirPartialPressure : PressureMeasurement
  waterVaporPartialPressure : PressureMeasurement

/-- The Figure 19 apparatus data needed in B.4.  The same uniform inner
cylinder cross-section is used at the reference and measured states. -/
structure Figure19Apparatus where
  innerCylinderCrossSection : AreaMeasurement
  atmosphericPressure : PressureMeasurement
  referenceState : InnerCylinderGasState
  measuredState : InnerCylinderGasState

/-- Official sample readout from the preceding graph extrapolation, B.3:
`H₀ = 5.9 cm`.  B.4 is stated for a general measured `H₀`, so this constant is
recorded but is not assumed by the main theorem. -/
def officialB3ReferenceHeightMetre : ℝ := 59 / 1000

/-- Official sample volume corresponding to the B.3 extrapolation:
`V₀ = 53.4 mL`. -/
def officialB3ReferenceVolumeCubicMetre : ℝ := 534 / 10000000

/-- The reference temperature `T₀ = 273.15 K` specified by the experiment. -/
def icePointTemperatureKelvin : ℝ := 27315 / 100

/-- The gas-constant readout prescribed for the later vapor-pressure fit. -/
def universalGasConstantJoulePerMoleKelvin : ℝ := 831 / 100

/-- Parameters appearing in the Clausius--Clapeyron relation quoted before
B.4.  This is kept separate from the B.4 dry-air calibration model: the
quoted law uses a positive reference saturation pressure, whereas B.4 asks
the experimenter to neglect vapor pressure in the extrapolated reference
state. -/
structure ClausiusClapeyronContext where
  referenceTemperature : AbsoluteTemperatureMeasurement
  referenceVaporPressure : PressureMeasurement
  molarLatentHeatJoulePerMole : ℝ
  universalGasConstantJoulePerMoleKelvin : ℝ
  referenceTemperature_pos : 0 < referenceTemperature.kelvinReadout
  referenceVaporPressure_pos :
    0 < referenceVaporPressure.pascalReadout
  molarLatentHeat_pos : 0 < molarLatentHeatJoulePerMole
  universalGasConstant_pos :
    0 < universalGasConstantJoulePerMoleKelvin

/-- The logarithmic Clausius--Clapeyron law from the experimental problem.
It exposes both positivity and the equation, so it is a constraining physical
relation rather than an opaque predicate.  It is contextual for later parts
and is not an assumption of `vaporPressurePascal_eq`. -/
def ObeysClausiusClapeyron
    (context : ClausiusClapeyronContext)
    (vaporPressurePascalAtTemperatureKelvin : ℝ → ℝ) : Prop :=
  ∀ temperatureKelvin : ℝ,
    0 < temperatureKelvin →
      0 < vaporPressurePascalAtTemperatureKelvin temperatureKelvin ∧
        Real.log
            (vaporPressurePascalAtTemperatureKelvin temperatureKelvin /
              context.referenceVaporPressure.pascalReadout) =
          -(context.molarLatentHeatJoulePerMole /
              context.universalGasConstantJoulePerMoleKelvin) *
            (1 / temperatureKelvin -
              1 / context.referenceTemperature.kelvinReadout)

/-- Governing laws and figure readouts used for B.4.

The two `icOc...PressureBalance` equations are the exact idealization of the
approximately atmospheric IC pressure produced by matching the water levels.
The final requested expression for vapor pressure is deliberately not a field
of this structure.
-/
structure B4Assumptions (apparatus : Figure19Apparatus) : Prop where
  atmosphericPressure_pos :
    0 < apparatus.atmosphericPressure.pascalReadout
  crossSection_pos :
    0 < apparatus.innerCylinderCrossSection.squareMetreReadout
  referenceTemperature_is_ice_point :
    apparatus.referenceState.temperature.kelvinReadout =
      icePointTemperatureKelvin
  referenceTemperature_pos :
    0 < apparatus.referenceState.temperature.kelvinReadout
  measuredTemperature_pos :
    0 < apparatus.measuredState.temperature.kelvinReadout
  referenceHeight_pos :
    0 < apparatus.referenceState.gasColumnHeight.metreReadout
  measuredHeight_pos :
    0 < apparatus.measuredState.gasColumnHeight.metreReadout
  referenceCylinderGeometry :
    apparatus.referenceState.gasVolume.cubicMetreReadout =
      apparatus.innerCylinderCrossSection.squareMetreReadout *
        apparatus.referenceState.gasColumnHeight.metreReadout
  measuredCylinderGeometry :
    apparatus.measuredState.gasVolume.cubicMetreReadout =
      apparatus.innerCylinderCrossSection.squareMetreReadout *
        apparatus.measuredState.gasColumnHeight.metreReadout
  referenceDaltonLaw :
    apparatus.referenceState.totalPressure.pascalReadout =
      apparatus.referenceState.dryAirPartialPressure.pascalReadout +
        apparatus.referenceState.waterVaporPartialPressure.pascalReadout
  measuredDaltonLaw :
    apparatus.measuredState.totalPressure.pascalReadout =
      apparatus.measuredState.dryAirPartialPressure.pascalReadout +
        apparatus.measuredState.waterVaporPartialPressure.pascalReadout
  icOcReferencePressureBalance :
    apparatus.referenceState.totalPressure.pascalReadout =
      apparatus.atmosphericPressure.pascalReadout
  icOcMeasuredPressureBalance :
    apparatus.measuredState.totalPressure.pascalReadout =
      apparatus.atmosphericPressure.pascalReadout
  referenceVaporPressureNegligible :
    apparatus.referenceState.waterVaporPartialPressure.pascalReadout = 0
  measuredVaporPressure_nonneg :
    0 ≤ apparatus.measuredState.waterVaporPartialPressure.pascalReadout
  dryAirIdealGasConservation :
    apparatus.referenceState.dryAirPartialPressure.pascalReadout *
          apparatus.referenceState.gasVolume.cubicMetreReadout /
        apparatus.referenceState.temperature.kelvinReadout =
      apparatus.measuredState.dryAirPartialPressure.pascalReadout *
          apparatus.measuredState.gasVolume.cubicMetreReadout /
        apparatus.measuredState.temperature.kelvinReadout

/-- In the Figure 19 idealized pressure-balance model,

`Pᵥ = P_atm * (1 - H₀ * T / (H * T₀))`.

Here every symbol denotes the corresponding SI scalar readout carried by
`apparatus`. -/
theorem vaporPressurePascal_eq
    (apparatus : Figure19Apparatus)
    (h : B4Assumptions apparatus) :
    apparatus.measuredState.waterVaporPartialPressure.pascalReadout =
      apparatus.atmosphericPressure.pascalReadout *
        (1 -
          apparatus.referenceState.gasColumnHeight.metreReadout *
              apparatus.measuredState.temperature.kelvinReadout /
            (apparatus.measuredState.gasColumnHeight.metreReadout *
              apparatus.referenceState.temperature.kelvinReadout)) := by
  sorry

end

end IPhO2026Problems.IPhO2026_4_B_4
