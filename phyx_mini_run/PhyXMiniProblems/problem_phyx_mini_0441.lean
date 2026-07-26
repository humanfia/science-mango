import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/-!
# Pressure of automobile-tire air after warming

Air in an automobile tire warms from `-10 °C` to `10 °C`; its initial
pressure is `190 kPa`.  The supplied raster shows a tire, wheel, valve stem,
and an arrow labelled `Air P` pointing toward the valve stem.

The explicitly supplied modeling assumption is that the tire's interior
volume does not change appreciably while driving.  The air is treated as a
sealed, fixed ideal-gas sample.  Since the source does not say whether its
`190 kPa` is an absolute or gauge reading, the physical state always stores
absolute pressure while a separate, unconstrained interpretation controls the
reported readout.  The final result therefore includes the ambient-pressure
correction for the gauge branch; the recorded answer is recovered only in the
absolute-reading branch.  Pressure, volume, temperature, and the molar gas
constant retain physical dimensions.  Real numbers occur only as named unit
readouts, mole readouts, and answer displays.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0441

open Dimension

/-! ## Dimensionful quantities and calibrated readouts -/

/-- Interior gas volume, carrying the physical dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
The molar gas constant, carrying energy-per-temperature dimension.  Physlib's
dimension vector has no amount-of-substance coordinate, so the inverse-mole
role is recorded by the type name and paired with an explicit mole readout.
-/
abbrev MolarGasConstant : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Read a dimensionful pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a dimensionful pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read the tire's physical interior volume in cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read the molar gas constant in joules per mole-kelvin. -/
def molarGasConstantInSI (gasConstant : MolarGasConstant) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-- Read an absolute temperature in kelvins from its storage unit. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Exact Celsius zero offset, expressed in kelvins. -/
def celsiusZeroInKelvins : ℝ := 27315 / 100

/-- Celsius readout of a Physlib absolute temperature. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - celsiusZeroInKelvins

/-! ## Tire states, physical model, and figure vocabulary -/

/-- The two tire-air states named in the prose. -/
inductive TireCondition where
  | initially
  | afterDriving
  deriving DecidableEq, Repr

/-- The process described between the two states. -/
inductive AutomobileUse where
  | drivenForAWhile
  deriving DecidableEq, Repr

/-- Equation-of-state model assigned to the tire air. -/
inductive GasModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/-- Gas species relevant to the problem. -/
inductive GasSpecies where
  | air
  | other
  deriving DecidableEq, Repr

/-- Whether a pressure readout is absolute or relative to the atmosphere. -/
inductive PressureInterpretation where
  | absolute
  | gauge
  deriving DecidableEq, Repr

/-- State of the valve stem during the drive. -/
inductive ValveCondition where
  | sealed
  | open
  deriving DecidableEq, Repr

/-- Mechanical idealization used for the tire interior. -/
inductive TireVolumeModel where
  | rigidConstantVolumeApproximation
  | deformable
  deriving DecidableEq, Repr

/-- Tire features visible in the primary raster. -/
inductive TireFeature where
  | tireBody
  | tread
  | wheelRim
  | valveStem
  deriving DecidableEq, Repr

/-- Color used for the central wheel rim in the primary raster. -/
inductive FigureColor where
  | lightBlue
  | other
  deriving DecidableEq, Repr

/-- The text attached to the pressure arrow in the primary raster. -/
inductive FigureLabel where
  | airP
  deriving DecidableEq, Repr

/-- Perspective in which the tire is drawn. -/
inductive FigureView where
  | threeDimensional
  deriving DecidableEq, Repr

/-- Qualitative labels and geometry transcribed from the supplied image. -/
structure AutomobileTireFigure where
  featureVisible : TireFeature → Bool
  rimColor : FigureColor
  pressureArrowVisible : Bool
  pressureArrowTarget : TireFeature
  pressureLabelVisible : Bool
  pressureLabel : FigureLabel
  view : FigureView

/-- Absolute pressure, volume, and absolute temperature at one tire condition. -/
structure TireAirState where
  absolutePressure : DimPressure
  interiorVolume : GasVolume
  temperature : Temperature

/--
The same physical air sample is used at both conditions.  Its amount is an
explicit scalar readout in moles rather than a replacement type for the gas.
-/
structure TireAirSample where
  species : GasSpecies
  amountInMoles : ℝ

/-!
All independent data in the tire model.  In particular, the final pressure is
an unconstrained `DimPressure` field until the assumptions and ideal-gas law
are imposed; it is not defined from the requested answer.
-/
structure AutomobileTireAirSetup where
  airSample : TireAirSample
  gasModel : GasModel
  stateAt : TireCondition → TireAirState
  molarGasConstant : MolarGasConstant
  temperatureStorageUnit : TemperatureUnit
  ambientAbsolutePressure : DimPressure
  pressureInterpretation : PressureInterpretation
  valveConditionDuringDrive : ValveCondition
  volumeModel : TireVolumeModel
  automobileUse : AutomobileUse
  figure : AutomobileTireFigure

/--
The pressure displayed to the reader.  An absolute report is the thermodynamic
pressure itself; a gauge report subtracts the ambient absolute pressure.
-/
def reportedPressureInKilopascals
    (setup : AutomobileTireAirSetup) (condition : TireCondition) : ℝ :=
  match setup.pressureInterpretation with
  | .absolute =>
      pressureInKilopascals (setup.stateAt condition).absolutePressure
  | .gauge =>
      pressureInKilopascals (setup.stateAt condition).absolutePressure -
        pressureInKilopascals setup.ambientAbsolutePressure

/-! ## Source facts, explicit idealizations, and governing physics -/

/--
Numerical data stated in the prose.  This structure contains no numerical
value for the final pressure.
-/
structure MatchesProblemStatement (setup : AutomobileTireAirSetup) : Prop where
  automobileWasDrivenForAWhile :
    setup.automobileUse = .drivenForAWhile
  initialTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.stateAt .initially).temperature = -10
  initialPressureKilopascals :
    reportedPressureInKilopascals setup .initially = 190
  finalTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.stateAt .afterDriving).temperature = 10

/-- Figure-derived facts; the raster contains no numerical pressure readout. -/
structure MatchesPrimaryFigure (setup : AutomobileTireAirSetup) : Prop where
  tireBodyVisible : setup.figure.featureVisible .tireBody = true
  treadPatternVisible : setup.figure.featureVisible .tread = true
  wheelRimVisible : setup.figure.featureVisible .wheelRim = true
  valveStemVisible : setup.figure.featureVisible .valveStem = true
  rimIsLightBlue : setup.figure.rimColor = .lightBlue
  pressureArrowShown : setup.figure.pressureArrowVisible = true
  pressureArrowPointsToValveStem :
    setup.figure.pressureArrowTarget = .valveStem
  airPressureLabelShown : setup.figure.pressureLabelVisible = true
  labelReadsAirP : setup.figure.pressureLabel = .airP
  tireDrawnInThreeDimensions : setup.figure.view = .threeDimensional

/-!
Explicit modeling choices needed to infer a pressure relation.  The requested
self-supplied assumption is `interiorVolumeUnchanged`; the sealed fixed-sample
and ideal-gas idealizations are also made explicit.  The pressure
interpretation is deliberately not fixed here because the source does not say
whether `190 kPa` is absolute or gauge pressure.
-/
structure UsesIdealizedRigidSealedTireModel
    (setup : AutomobileTireAirSetup) : Prop where
  sampleIsAir : setup.airSample.species = .air
  gasBehavesIdeally : setup.gasModel = .ideal
  valveRemainsSealed :
    setup.valveConditionDuringDrive = .sealed
  usesRigidVolumeApproximation :
    setup.volumeModel = .rigidConstantVolumeApproximation
  interiorVolumeUnchanged :
    (setup.stateAt .initially).interiorVolume =
      (setup.stateAt .afterDriving).interiorVolume
  temperatureStorageIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin

/-- Positivity conditions selecting physically meaningful ideal-gas states. -/
structure HasPhysicalTireAirParameters
    (setup : AutomobileTireAirSetup) : Prop where
  gasAmountPositive : 0 < setup.airSample.amountInMoles
  molarGasConstantPositive :
    0 < molarGasConstantInSI setup.molarGasConstant
  absolutePressurePositive : ∀ condition,
    0 < pressureInPascals (setup.stateAt condition).absolutePressure
  ambientAbsolutePressurePositive :
    0 < pressureInPascals setup.ambientAbsolutePressure
  volumePositive : ∀ condition,
    0 < volumeInCubicMeters (setup.stateAt condition).interiorVolume
  absoluteTemperaturePositive : ∀ condition,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.stateAt condition).temperature

/-!
The macroscopic ideal-gas equation `pV = nRT`, in coherent SI readouts, at
each condition.  It is a general governing law and does not assign a value to
the final pressure.
-/
structure SatisfiesTireIdealGasLaw
    (setup : AutomobileTireAirSetup) : Prop where
  idealGasLawAt : ∀ condition,
    pressureInPascals (setup.stateAt condition).absolutePressure *
        volumeInCubicMeters (setup.stateAt condition).interiorVolume =
      setup.airSample.amountInMoles *
        molarGasConstantInSI setup.molarGasConstant *
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.stateAt condition).temperature

/-! ## Derived pressure and displayed answer -/

/-!
For a fixed amount of ideal gas in a fixed volume, pressure is proportional to
absolute temperature.  This relation is a derived conclusion, not one of the
law or scenario fields above.
-/
lemma finalPressure_temperatureRatio
    (setup : AutomobileTireAirSetup)
    (_problem : MatchesProblemStatement setup)
    (_model : UsesIdealizedRigidSealedTireModel setup)
    (_physical : HasPhysicalTireAirParameters setup)
    (_laws : SatisfiesTireIdealGasLaw setup) :
    pressureInKilopascals (setup.stateAt .afterDriving).absolutePressure =
      pressureInKilopascals (setup.stateAt .initially).absolutePressure *
        temperatureInKelvins setup.temperatureStorageUnit
            (setup.stateAt .afterDriving).temperature /
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.stateAt .initially).temperature := by
  sorry

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Kilopascal value printed beside each answer label. -/
def AnswerChoice.pressureInKilopascals : AnswerChoice → ℝ
  | .A => 220
  | .B => 2131 / 10
  | .C => 200
  | .D => 1022 / 5

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
`RoundsToOneDecimal actual displayed` says that `displayed` is the result of
rounding `actual` to the nearest tenth, with a half-open tie convention.
-/
def RoundsToOneDecimal (actual displayed : ℝ) : Prop :=
  displayed - 1 / 20 ≤ actual ∧ actual < displayed + 1 / 20

/-!
The source leaves the pressure convention unspecified.  Under the ideal-gas
model the exact reported final pressure is `56630 / 277 kPa` plus a correction
of zero for an absolute reading, or
`(400 / 5263) * ambientPressure` for a gauge reading.  Consequently the
recorded answer D, `204.4 kPa`, follows only under the absolute-reading
interpretation; the gauge branch remains symbolic because the source gives no
ambient pressure.

Blueprint label: `thm:physics:phyx_mini_0441:target`.
-/
theorem finalPressure_roundsTo_204_point_4_kPa_answerD
    (setup : AutomobileTireAirSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_model : UsesIdealizedRigidSealedTireModel setup)
    (_physical : HasPhysicalTireAirParameters setup)
    (_laws : SatisfiesTireIdealGasLaw setup) :
    reportedPressureInKilopascals setup .afterDriving =
      56630 / 277 +
        (match setup.pressureInterpretation with
        | .absolute => 0
        | .gauge =>
            pressureInKilopascals setup.ambientAbsolutePressure *
              400 / 5263) ∧
      (setup.pressureInterpretation = .absolute →
        RoundsToOneDecimal
          (reportedPressureInKilopascals setup .afterDriving)
          recordedAnswerChoice.pressureInKilopascals) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0441
