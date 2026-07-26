import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

/-!
# Two-bulb constant-volume gas thermometer

Two gas-containing bulbs are kept at fixed volume in separate water baths.  A
mercury manometer reads the pressure in the measuring bulb minus the pressure
in the reference bulb.  The reference bath is held at the triple point of
water while the other bath is first at the boiling point and then at an
unknown temperature.

The supplied image is unrelated to this scenario (it shows critical-angle
rays in water), so there are no trustworthy bulb or manometer dimensions to
extract from it.  The labels below come from the textual experiment instead.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0157

open Dimension

/-- A physical volume, represented consistently across choices of units. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/--
One gas bulb together with the quantities held fixed during all three runs.
`amountOfGasMoles` is a scalar readout in moles, while `fixedVolume` retains
its physical length-cubed dimension.
-/
structure ConstantVolumeGasBulb where
  fixedVolume : GasVolume
  amountOfGasMoles : ℝ

/--
The physical apparatus and its named temperatures.  The order of arguments
of `manometerPressureDifference referenceBath measuringBath` fixes the sign:
the displayed pressure is measuring-bulb pressure minus reference-bulb
pressure.
-/
structure TwoBulbGasThermometer where
  referenceBulb : ConstantVolumeGasBulb
  measuringBulb : ConstantVolumeGasBulb
  triplePointTemperature : Temperature
  boilingPointTemperature : Temperature
  unknownTemperature : Temperature
  referenceBulbPressure : Temperature → DimPressure
  measuringBulbPressure : Temperature → DimPressure
  manometerPressureDifference : Temperature → Temperature → DimPressure

/-- Positivity conditions selecting the physical branch of the apparatus. -/
structure HasPhysicalGasThermometerParameters
    (setup : TwoBulbGasThermometer) : Prop where
  referenceVolumePositive :
    0 < (setup.referenceBulb.fixedVolume UnitChoices.SI).val
  measuringVolumePositive :
    0 < (setup.measuringBulb.fixedVolume UnitChoices.SI).val
  referenceGasAmountPositive :
    0 < setup.referenceBulb.amountOfGasMoles
  measuringGasAmountPositive :
    0 < setup.measuringBulb.amountOfGasMoles
  triplePointTemperaturePositive :
    0 < setup.triplePointTemperature.toReal
  boilingPointTemperaturePositive :
    0 < setup.boilingPointTemperature.toReal
  unknownTemperaturePositive :
    0 < setup.unknownTemperature.toReal

/--
The governing laws, kept separate from the numerical observations.

At fixed gas amount and volume, the ideal-gas law `P V = n R T` says that
pressure is proportional to absolute temperature.  The two cross-multiplied
relations state this without introducing a unit-dependent proportionality
constant.  The final field is the differential-pressure law implemented by
the mercury manometer.
-/
structure SatisfiesConstantVolumeIdealGasThermometry
    (setup : TwoBulbGasThermometer) : Prop where
  referencePressureProportionalToTemperature :
    ∀ (first second : Temperature) (units : UnitChoices),
      ((setup.referenceBulbPressure first) units).val * second.toReal =
        ((setup.referenceBulbPressure second) units).val * first.toReal
  measuringPressureProportionalToTemperature :
    ∀ (first second : Temperature) (units : UnitChoices),
      ((setup.measuringBulbPressure first) units).val * second.toReal =
        ((setup.measuringBulbPressure second) units).val * first.toReal
  manometerReadsPressureDifference :
    ∀ (referenceBath measuringBath : Temperature) (units : UnitChoices),
      ((setup.manometerPressureDifference referenceBath measuringBath) units).val =
        ((setup.measuringBulbPressure measuringBath) units).val -
          ((setup.referenceBulbPressure referenceBath) units).val

/--
The standard temperature calibration and the three manometer readouts from
the problem.  The first run places both baths at the triple point; the next
two retain the reference bath at the triple point and put the measuring bath
at the boiling point or at the unknown temperature, respectively.
-/
structure HasGasThermometerCalibrationData
    (setup : TwoBulbGasThermometer) : Prop where
  triplePointKelvinReadout :
    setup.triplePointTemperature.toReal = 273
  boilingPointKelvinReadout :
    setup.boilingPointTemperature.toReal = 373
  noDifferenceAtTriplePoint :
    ∀ units : UnitChoices,
      ((setup.manometerPressureDifference
          setup.triplePointTemperature setup.triplePointTemperature) units).val = 0
  boilingPointDifferenceIs120Torr :
    ∀ units : UnitChoices,
      ((setup.manometerPressureDifference
          setup.triplePointTemperature setup.boilingPointTemperature) units).val =
        120 * (DimPressure.torr units).val
  unknownDifferenceIs90Torr :
    ∀ units : UnitChoices,
      ((setup.manometerPressureDifference
          setup.triplePointTemperature setup.unknownTemperature) units).val =
        90 * (DimPressure.torr units).val

/--
The unknown bath has temperature 348 K (answer choice D).

The calibration data are the premises; in particular, the 348 K conclusion
does not occur in the apparatus, governing-law, or data structures.

Blueprint label: `thm:physics:phyx_mini_0157:target`.
-/
theorem unknownTemperature_eq_348_kelvin
    (setup : TwoBulbGasThermometer)
    (_physical : HasPhysicalGasThermometerParameters setup)
    (_laws : SatisfiesConstantVolumeIdealGasThermometry setup)
    (_data : HasGasThermometerCalibrationData setup) :
    setup.unknownTemperature.toReal = 348 := by
  have htorr : 0 < (DimPressure.torr UnitChoices.SI).val := by
    norm_num [DimPressure.torr, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have hzero := _data.noDifferenceAtTriplePoint UnitChoices.SI
  rw [_laws.manometerReadsPressureDifference] at hzero
  have hboil := _data.boilingPointDifferenceIs120Torr UnitChoices.SI
  rw [_laws.manometerReadsPressureDifference] at hboil
  have hunknown := _data.unknownDifferenceIs90Torr UnitChoices.SI
  rw [_laws.manometerReadsPressureDifference] at hunknown
  have hpropBoil := _laws.measuringPressureProportionalToTemperature
    setup.triplePointTemperature setup.boilingPointTemperature UnitChoices.SI
  have hpropUnknown := _laws.measuringPressureProportionalToTemperature
    setup.triplePointTemperature setup.unknownTemperature UnitChoices.SI
  rw [_data.triplePointKelvinReadout, _data.boilingPointKelvinReadout] at hpropBoil
  rw [_data.triplePointKelvinReadout] at hpropUnknown
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0157
