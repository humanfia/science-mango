import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0345

open Dimension

/-!
# Internal-energy change of a rapidly rising helium balloon

A large research balloon initially contains `2.00 * 10^3 m^3` of helium at
`1.00 atm` and `15.0 degrees Celsius`.  It rises rapidly to an altitude where
the atmospheric pressure is `0.900 atm`.  The helium is modeled as a
monatomic ideal gas, and the rapid ascent is idealized as adiabatic.

Pressure and energy use Physlib's ready-made dimensionful types.  Volume is a
unit-independent length-cubed quantity, while real numbers below are explicit
SI readouts, dimensionless ratios, schematic figure coordinates, or displayed
multiple-choice values.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A physical gas volume, independent of the selected system of units. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Read a gas volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read an energy in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Physlib's `Temperature.toReal` is the absolute-temperature projection.  In
this model its selected scale is kelvin, as required by the ideal-gas law.
-/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Physical states and source-figure vocabulary -/

/-- The two endpoint states of the ascent. -/
inductive BalloonState where
  | groundLevel
  | higherAltitude
  deriving DecidableEq, Repr

/-- The altitude labels supplied by the problem text. -/
inductive AltitudeLabel where
  | groundLevel
  | higherAltitude
  deriving DecidableEq, Repr

/-- The gas species carried by the research balloon. -/
inductive BalloonGas where
  | helium
  | other
  deriving DecidableEq, Repr

/-- The thermodynamic model applied to the balloon gas. -/
inductive GasModel where
  | monatomicIdealGas
  | other
  deriving DecidableEq, Repr

/-- Qualitative speed of the ascent described in the source. -/
inductive AscentProtocol where
  | rapid
  | slow
  deriving DecidableEq, Repr

/-- Heat-exchange regime during the ascent. -/
inductive HeatExchangeRegime where
  | negligibleDuringAscent
  | appreciable
  deriving DecidableEq, Repr

/-- The two balloon drawings in the supplied raster image. -/
inductive FigureBalloon where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Fill colors visible in the supplied image. -/
inductive FigureBalloonColor where
  | warmOrange
  | beige
  deriving DecidableEq, Repr

/-- Envelope patterns visible in the supplied image. -/
inductive FigureBalloonPattern where
  | checker
  | stitchedGrid
  deriving DecidableEq, Repr

/-- Landscape elements drawn below the two balloons. -/
inductive LandscapeFeature where
  | hills
  | smallBuildings
  | silo
  | trees
  deriving DecidableEq, Repr

/-!
Primary-image information is kept separately from thermodynamic quantities.
The coordinates and rendered sizes are schematic scalar readouts, not physical
altitudes or gas volumes.
-/
structure ResearchBalloonFigure where
  depictedState : FigureBalloon → BalloonState
  verticalCoordinate : FigureBalloon → ℝ
  renderedSize : FigureBalloon → ℝ
  color : FigureBalloon → FigureBalloonColor
  pattern : FigureBalloon → FigureBalloonPattern
  basketVisible : FigureBalloon → Bool
  landscapeVisible : LandscapeFeature → Bool
  containsText : Bool

/-!
The independent physical quantities of the balloon and its ascent.

`heliumAmountInMoles` and
`molarGasConstantJoulesPerMoleKelvin` are named scalar readouts in explicit
units; pressure, volume, absolute temperature, heat, work, and internal energy
remain physical quantities.  No final energy-change value is stored here.
-/
structure HeliumBalloonAscent where
  gas : BalloonGas
  gasModel : GasModel
  altitudeLabel : BalloonState → AltitudeLabel
  ascentProtocol : AscentProtocol
  heatExchangeRegime : HeatExchangeRegime
  heliumAmountInMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  adiabaticIndexGamma : ℝ
  atmosphericPressure : BalloonState → DimPressure
  heliumPressure : BalloonState → DimPressure
  heliumVolume : BalloonState → GasVolume
  heliumTemperature : BalloonState → Temperature
  heliumInternalEnergy : BalloonState → DimEnergy
  heatTransferredToHelium : DimEnergy
  workDoneByHelium : DimEnergy
  figure : ResearchBalloonFigure

/-! ## Scenario, figure/data readouts, and physical laws -/

/-- Qualitative facts stated in the prose, without any requested answer. -/
structure MatchesBalloonScenario (setup : HeliumBalloonAscent) : Prop where
  gasIsHelium : setup.gas = .helium
  heliumIsMonatomicIdealGas : setup.gasModel = .monatomicIdealGas
  initialStateAtGround : setup.altitudeLabel .groundLevel = .groundLevel
  finalStateAtHigherAltitude :
    setup.altitudeLabel .higherAltitude = .higherAltitude
  ascentIsRapid : setup.ascentProtocol = .rapid
  heatExchangeIsNegligible :
    setup.heatExchangeRegime = .negligibleDuringAscent

/-!
Transcription of the supplied image.  The upper orange checker-pattern balloon
is rendered above and larger than the lower beige stitched-grid balloon; both
have baskets.  The image contains the listed landscape objects and no text.
Its rendered-size inequality is not identified with a numerical gas volume.
-/
structure MatchesPrimaryFigure (setup : HeliumBalloonAscent) : Prop where
  upperDepictsHigherState :
    setup.figure.depictedState .upper = .higherAltitude
  lowerDepictsGroundState :
    setup.figure.depictedState .lower = .groundLevel
  upperIsHigherInImage :
    setup.figure.verticalCoordinate .lower <
      setup.figure.verticalCoordinate .upper
  upperIsRenderedLarger :
    setup.figure.renderedSize .lower < setup.figure.renderedSize .upper
  upperColor : setup.figure.color .upper = .warmOrange
  lowerColor : setup.figure.color .lower = .beige
  upperPattern : setup.figure.pattern .upper = .checker
  lowerPattern : setup.figure.pattern .lower = .stitchedGrid
  bothBasketsVisible :
    ∀ balloon : FigureBalloon, setup.figure.basketVisible balloon = true
  allLandscapeFeaturesVisible :
    ∀ feature : LandscapeFeature, setup.figure.landscapeVisible feature = true
  noTextInFigure : setup.figure.containsText = false

/-!
Numerical readouts stated in the problem.  The initial helium pressure is one
standard atmosphere, the initial volume is `2000 m^3`, and `15 degrees
Celsius` is encoded using the exact Celsius-to-kelvin offset `273.15`.  The
only final-state datum is the ambient pressure `0.900 atm`; equality of the
helium and ambient endpoint pressures is a governing law below.
-/
structure MatchesProblemReadouts (setup : HeliumBalloonAscent) : Prop where
  initialHeliumPressure :
    ∀ units : UnitChoices,
      (setup.heliumPressure .groundLevel units).val =
        (DimPressure.standardAtmosphere units).val
  initialVolumeCubicMeters :
    volumeInCubicMeters (setup.heliumVolume .groundLevel) = 2000
  initialTemperatureCelsius :
    temperatureInKelvins (setup.heliumTemperature .groundLevel) -
        (27315 / 100 : ℝ) =
      15
  finalAtmosphericPressure :
    ∀ units : UnitChoices,
      (setup.atmosphericPressure .higherAltitude units).val =
        (9 / 10 : ℝ) *
          (DimPressure.standardAtmosphere units).val

/-- Positivity and nondegeneracy conditions for the thermodynamic model. -/
structure HasPhysicalBalloonParameters (setup : HeliumBalloonAscent) : Prop where
  heliumAmountPositive : 0 < setup.heliumAmountInMoles
  molarGasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  adiabaticIndexGreaterThanOne : 1 < setup.adiabaticIndexGamma
  heliumPressurePositive :
    ∀ state, 0 < pressureInPascals (setup.heliumPressure state)
  atmosphericPressurePositive :
    ∀ state, 0 < pressureInPascals (setup.atmosphericPressure state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.heliumVolume state)
  temperaturePositive :
    ∀ state, 0 < temperatureInKelvins (setup.heliumTemperature state)
  internalEnergyPositive :
    ∀ state, 0 < energyInJoules (setup.heliumInternalEnergy state)

/-!
Governing endpoint laws for the idealized ascent:

* the flexible balloon is in mechanical equilibrium with the atmosphere at
  each endpoint;
* `P V = n R T` and `U = (3/2) n R T` hold for monatomic ideal helium;
* monatomic helium has adiabatic index `gamma = 5/3`;
* the adiabatic endpoint relation is
  `T₂/T₁ = (P₂/P₁)^((gamma-1)/gamma)`;
* negligible heat exchange is idealized as `Q = 0`, and the first law is
  `Delta U = Q - W_by_gas`.

These are generic physical relations between independently stored quantities.
They contain neither a numerical internal-energy change nor an answer choice.
-/
structure SatisfiesRapidAdiabaticIdealGasLaws
    (setup : HeliumBalloonAscent) : Prop where
  endpointMechanicalEquilibrium :
    ∀ (state : BalloonState) (units : UnitChoices),
      (setup.heliumPressure state units).val =
        (setup.atmosphericPressure state units).val
  idealGasLawSI :
    ∀ state : BalloonState,
      pressureInPascals (setup.heliumPressure state) *
          volumeInCubicMeters (setup.heliumVolume state) =
        setup.heliumAmountInMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
            temperatureInKelvins (setup.heliumTemperature state)
  monatomicInternalEnergyLawSI :
    ∀ state : BalloonState,
      energyInJoules (setup.heliumInternalEnergy state) =
        (3 / 2 : ℝ) * setup.heliumAmountInMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
            temperatureInKelvins (setup.heliumTemperature state)
  monatomicAdiabaticIndex : setup.adiabaticIndexGamma = (5 / 3 : ℝ)
  adiabaticPressureTemperatureRelation :
    temperatureInKelvins (setup.heliumTemperature .higherAltitude) /
          temperatureInKelvins (setup.heliumTemperature .groundLevel) =
      Real.rpow
        (pressureInPascals (setup.heliumPressure .higherAltitude) /
          pressureInPascals (setup.heliumPressure .groundLevel))
        ((setup.adiabaticIndexGamma - 1) / setup.adiabaticIndexGamma)
  negligibleHeatTransfer :
    energyInJoules setup.heatTransferredToHelium = 0
  firstLawSI :
    energyInJoules (setup.heliumInternalEnergy .higherAltitude) -
        energyInJoules (setup.heliumInternalEnergy .groundLevel) =
      energyInJoules setup.heatTransferredToHelium -
        energyInJoules setup.workDoneByHelium

/-! ## Derived quantities and displayed answers -/

/-- The requested final-minus-initial internal-energy change, in joules. -/
def internalEnergyChangeInJoules (setup : HeliumBalloonAscent) : ℝ :=
  energyInJoules (setup.heliumInternalEnergy .higherAltitude) -
    energyInJoules (setup.heliumInternalEnergy .groundLevel)

/-- Labels of the four displayed numerical answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Internal-energy change in joules printed beside each answer label. -/
def displayedEnergyChangeInJoules : AnswerChoice → ℝ
  | .A => -1650000000
  | .B => -12500000
  | .C => -19500000
  | .D => -1450

/-- Dataset answer metadata, kept separate from every theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A choice is uniquely closest to an exact modeled energy change. -/
def IsUniqueClosestDisplayedAnswer
    (changeInJoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |changeInJoules - displayedEnergyChangeInJoules choice| <
      |changeInJoules - displayedEnergyChangeInJoules other|

/-!
The pressure ratio and monatomic adiabatic exponent determine
`T₂ = 288.15 * (0.9)^(2/5) K`.  This is an intermediate physical conclusion,
not a premise.
-/
lemma final_temperature_from_adiabatic_expansion
    (setup : HeliumBalloonAscent)
    (_scenario : MatchesBalloonScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_physical : HasPhysicalBalloonParameters setup)
    (_laws : SatisfiesRapidAdiabaticIdealGasLaws setup) :
    temperatureInKelvins (setup.heliumTemperature .higherAltitude) =
      (28815 / 100 : ℝ) * Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have hGroundPressure :
      pressureInPascals (setup.heliumPressure .groundLevel) = 101325 := by
    calc
      pressureInPascals (setup.heliumPressure .groundLevel) =
          pressureInPascals DimPressure.standardAtmosphere :=
        _data.initialHeliumPressure UnitChoices.SI
      _ = 101325 := hStandardAtmosphere
  have hFinalPressure :
      pressureInPascals (setup.heliumPressure .higherAltitude) =
        (9 / 10 : ℝ) * 101325 := by
    calc
      pressureInPascals (setup.heliumPressure .higherAltitude) =
          pressureInPascals (setup.atmosphericPressure .higherAltitude) :=
        _laws.endpointMechanicalEquilibrium .higherAltitude UnitChoices.SI
      _ = (9 / 10 : ℝ) *
          pressureInPascals DimPressure.standardAtmosphere :=
        _data.finalAtmosphericPressure UnitChoices.SI
      _ = (9 / 10 : ℝ) * 101325 := by rw [hStandardAtmosphere]
  have hPressureRatio :
      pressureInPascals (setup.heliumPressure .higherAltitude) /
          pressureInPascals (setup.heliumPressure .groundLevel) =
        (9 / 10 : ℝ) := by
    rw [hFinalPressure, hGroundPressure]
    norm_num
  have hExponent :
      (setup.adiabaticIndexGamma - 1) / setup.adiabaticIndexGamma =
        (2 / 5 : ℝ) := by
    rw [_laws.monatomicAdiabaticIndex]
    norm_num
  have hTemperatureRatio :
      temperatureInKelvins (setup.heliumTemperature .higherAltitude) /
          temperatureInKelvins (setup.heliumTemperature .groundLevel) =
        Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) := by
    simpa [hPressureRatio, hExponent] using
      _laws.adiabaticPressureTemperatureRelation
  have hGroundTemperature :
      temperatureInKelvins (setup.heliumTemperature .groundLevel) =
        (28815 / 100 : ℝ) := by
    have h := _data.initialTemperatureCelsius
    linarith
  have hGroundTemperatureNe :
      temperatureInKelvins (setup.heliumTemperature .groundLevel) ≠ 0 :=
    ne_of_gt (_physical.temperaturePositive .groundLevel)
  have hFinalTemperature :
      temperatureInKelvins (setup.heliumTemperature .higherAltitude) =
        Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) *
          temperatureInKelvins (setup.heliumTemperature .groundLevel) :=
    (div_eq_iff hGroundTemperatureNe).mp hTemperatureRatio
  rw [hFinalTemperature, hGroundTemperature]
  ring

/-!
Eliminating `n R T₁` with the initial ideal-gas law gives the exact modeled
energy change

`(3/2) * 101325 * 2000 * ((0.9)^(2/5) - 1)` joules.
-/
lemma internal_energy_change_exact
    (setup : HeliumBalloonAscent)
    (_scenario : MatchesBalloonScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_physical : HasPhysicalBalloonParameters setup)
    (_laws : SatisfiesRapidAdiabaticIdealGasLaws setup) :
    internalEnergyChangeInJoules setup =
      (3 / 2 : ℝ) * 101325 * 2000 *
        (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have hGroundPressure :
      pressureInPascals (setup.heliumPressure .groundLevel) = 101325 := by
    calc
      pressureInPascals (setup.heliumPressure .groundLevel) =
          pressureInPascals DimPressure.standardAtmosphere :=
        _data.initialHeliumPressure UnitChoices.SI
      _ = 101325 := hStandardAtmosphere
  have hGroundTemperature :
      temperatureInKelvins (setup.heliumTemperature .groundLevel) =
        (28815 / 100 : ℝ) := by
    have h := _data.initialTemperatureCelsius
    linarith
  have hFinalTemperature :=
    final_temperature_from_adiabatic_expansion setup _scenario _data
      _physical _laws
  have hGroundIdealGas := _laws.idealGasLawSI .groundLevel
  rw [hGroundPressure, _data.initialVolumeCubicMeters, hGroundTemperature] at hGroundIdealGas
  rw [internalEnergyChangeInJoules,
    _laws.monatomicInternalEnergyLawSI .higherAltitude,
    _laws.monatomicInternalEnergyLawSI .groundLevel, hFinalTemperature,
    hGroundTemperature]
  calc
    _ = (3 / 2 : ℝ) *
          (setup.heliumAmountInMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
              (28815 / 100 : ℝ)) *
          (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) := by ring
    _ = (3 / 2 : ℝ) * 101325 * 2000 *
          (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) := by
      rw [← hGroundIdealGas]
      ring

/-!
The exact adiabatic-model result is approximately `-1.25446 * 10^7 J`, so
the displayed `-1.25 * 10^7 J` value is the unique closest choice, answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0345:target`.
-/
theorem problem_phyx_mini_0345
    (setup : HeliumBalloonAscent)
    (_scenario : MatchesBalloonScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemReadouts setup)
    (_physical : HasPhysicalBalloonParameters setup)
    (_laws : SatisfiesRapidAdiabaticIdealGasLaws setup) :
    internalEnergyChangeInJoules setup =
        (3 / 2 : ℝ) * 101325 * 2000 *
          (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) ∧
      IsUniqueClosestDisplayedAnswer
        (internalEnergyChangeInJoules setup) .B := by
  have hExact := internal_energy_change_exact setup _scenario _data
    _physical _laws
  have hPower :
      (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ)) ^ 5 = (81 / 100 : ℝ) := by
    calc
      (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ)) ^ 5 =
          Real.rpow (9 / 10 : ℝ) ((2 / 5 : ℝ) * 5) :=
        (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 9 / 10)
          (2 / 5 : ℝ) 5).symm
      _ = Real.rpow (9 / 10 : ℝ) 2 := by norm_num
      _ = (9 / 10 : ℝ) ^ (2 : ℕ) := Real.rpow_natCast _ _
      _ = (81 / 100 : ℝ) := by norm_num
  have hPowerLower :
      (95872 / 100000 : ℝ) <
        Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) := by
    apply ((show Odd 5 by decide).pow_lt_pow).mp
    rw [hPower]
    norm_num
  have hPowerUpper :
      Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) <
        (9588 / 10000 : ℝ) := by
    apply ((show Odd 5 by decide).pow_lt_pow).mp
    rw [hPower]
    norm_num
  constructor
  · exact hExact
  · rw [hExact]
    intro other hOther
    cases other with
    | A =>
        change
          |(3 / 2 : ℝ) * 101325 * 2000 *
              (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) -
                (-12500000)| <
            |(3 / 2 : ℝ) * 101325 * 2000 *
              (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) -
                (-1650000000)|
        rw [abs_of_neg (by nlinarith), abs_of_pos (by nlinarith)]
        nlinarith
    | B => exact (hOther rfl).elim
    | C =>
        change
          |(3 / 2 : ℝ) * 101325 * 2000 *
              (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) -
                (-12500000)| <
            |(3 / 2 : ℝ) * 101325 * 2000 *
              (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) -
                (-19500000)|
        rw [abs_of_neg (by nlinarith), abs_of_pos (by nlinarith)]
        nlinarith
    | D =>
        change
          |(3 / 2 : ℝ) * 101325 * 2000 *
              (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) -
                (-12500000)| <
            |(3 / 2 : ℝ) * 101325 * 2000 *
              (Real.rpow (9 / 10 : ℝ) (2 / 5 : ℝ) - 1) -
                (-1450)|
        rw [abs_of_neg (by nlinarith), abs_of_neg (by nlinarith)]
        nlinarith

end PhyXMiniProblems.ProblemPhyXMini0345
