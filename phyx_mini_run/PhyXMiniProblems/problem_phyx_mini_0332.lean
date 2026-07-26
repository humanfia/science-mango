import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0332

open Dimension

/-!
# Heat of reaction in a bombardier beetle

Two chemicals stored in separate reservoirs react in an abdominal chamber and
warm the resulting spray from `20 °C` to `100 °C`.  Their common specific heat
capacity is that of water, `4.19 × 10³ J/(kg K)`.  The requested heat of
reaction is the released energy per unit mass.

Specific heat, specific energy, speed, and length are represented by Physlib
`Dimensionful` quantities.  Absolute temperatures use Physlib's `Temperature`.
Real numbers occur only as readouts in named units and as the displayed answer
values.  The supplied image contributes qualitative evidence that a beetle is
emitting a defensive cloud; it contains no printed labels.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Physlib's nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/--
Energy per unit mass, with dimension `L² T⁻²`, read in `J/kg` in coherent SI
units.
-/
abbrev SpecificEnergyQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/--
Specific heat capacity, with dimension `L² T⁻² Θ⁻¹`, read in `J/(kg K)` in
coherent SI units.
-/
abbrev SpecificHeatCapacityQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Read a physical length in the selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read the beetle's body length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a physical speed in the selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed { UnitChoices.SI with
    length := lengthUnit, time := timeUnit }).val : ℝ)

/-- Read a speed in meters per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Read a speed in kilometers per hour. -/
def speedInKilometersPerHour (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.kilometers TimeUnit.hours speed

/-- Read a specific energy in joules per kilogram. -/
def specificEnergyInJoulesPerKilogram
    (energy : SpecificEnergyQuantity) : ℝ :=
  ((energy UnitChoices.SI).val : ℝ)

/-- Read a specific heat capacity in joules per kilogram-kelvin. -/
def specificHeatInJoulesPerKilogramKelvin
    (specificHeat : SpecificHeatCapacityQuantity) : ℝ :=
  ((specificHeat UnitChoices.SI).val : ℝ)

/-!
The `Temperature` values in this problem are consistently read in kelvins.
Subtracting `273.15` supplies the corresponding absolute Celsius readout.
-/
def temperatureInDegreesCelsius (temperature : Temperature) : ℝ :=
  temperature.toReal - 27315 / 100

/-! ## Physical roles and image-derived features -/

/-- The three material roles named in the reaction narrative. -/
inductive ReactionMaterial where
  | firstReservoirChemical
  | secondReservoirChemical
  | reactedSpray
  deriving DecidableEq, Repr

/-- The two thermal stages relevant to the calorimetry calculation. -/
inductive ReactionStage where
  | beforeReaction
  | warmedSpray
  deriving DecidableEq, Repr

/-- Location of the chemical reaction in the beetle. -/
inductive ReactionLocation where
  | abdominalReactionChamber
  deriving DecidableEq, Repr

/-- Location from which the defensive spray leaves the beetle. -/
inductive SprayOutlet where
  | movableAbdomenTip
  deriving DecidableEq, Repr

/-- Qualitative pressure regime described in the problem. -/
inductive ChamberPressureRegime where
  | highEnoughToDriveJet
  deriving DecidableEq, Repr

/--
Qualitative facts visible in the supplied image.  The numerical body length is
given by the prose accompanying the image rather than by a printed scale.
-/
structure BombardierBeetleFigure where
  showsBeetle : Bool
  showsHumanFingerContact : Bool
  showsDefensiveSprayCloud : Bool
  hasPrintedTextOrLabels : Bool

/-!
The physical quantities in the bombardier-beetle calorimetry model.

The heat of reaction is an independent dimensionful field.  In particular, it
is not defined to be the requested numerical answer; only the governing
calorimetry law below relates it to the temperature rise and specific heat.
-/
structure BombardierBeetleCalorimetrySetup where
  figure : BombardierBeetleFigure
  temperature : ReactionStage → Temperature
  specificHeatCapacity : ReactionMaterial → SpecificHeatCapacityQuantity
  waterSpecificHeatCapacity : SpecificHeatCapacityQuantity
  heatOfReactionPerUnitMass : SpecificEnergyQuantity
  maximumJetSpeed : SpeedQuantity
  bodyLength : LengthQuantity
  reactionLocation : ReactionLocation
  sprayOutlet : SprayOutlet
  chamberPressureRegime : ChamberPressureRegime

/--
The temperature increase expressed in Celsius degrees.  A Celsius interval and
a kelvin interval have the same scale, so this is also the kelvin rise used by
the SI calorimetry relation.
-/
def temperatureRiseInKelvins
    (setup : BombardierBeetleCalorimetrySetup) : ℝ :=
  temperatureInDegreesCelsius (setup.temperature .warmedSpray) -
    temperatureInDegreesCelsius (setup.temperature .beforeReaction)

/-! ## Figure/data readouts and governing law -/

/-!
Measurements stated in the prose and qualitative readouts from the primary
image.  `68 km/h` is the source's rounded parenthetical conversion of
`19 m/s`, so it is recorded with a half-kilometer-per-hour tolerance.

No value of the heat of reaction appears in this structure.
-/
structure MatchesBombardierBeetleProblemData
    (setup : BombardierBeetleCalorimetrySetup) : Prop where
  initialTemperatureCelsius :
    temperatureInDegreesCelsius (setup.temperature .beforeReaction) = 20
  finalTemperatureCelsius :
    temperatureInDegreesCelsius (setup.temperature .warmedSpray) = 100
  waterSpecificHeatJoulesPerKilogramKelvin :
    specificHeatInJoulesPerKilogramKelvin
        setup.waterSpecificHeatCapacity = 4190
  chemicalsAndSprayMatchWater :
    ∀ material,
      setup.specificHeatCapacity material = setup.waterSpecificHeatCapacity
  maximumJetSpeedMetersPerSecond :
    speedInMetersPerSecond setup.maximumJetSpeed = 19
  roundedJetSpeedKilometersPerHour :
    |speedInKilometersPerHour setup.maximumJetSpeed - 68| ≤ 1 / 2
  beetleBodyLengthCentimeters :
    lengthInCentimeters setup.bodyLength = 2
  reactionOccursInAbdominalChamber :
    setup.reactionLocation = .abdominalReactionChamber
  sprayLeavesMovableAbdomenTip :
    setup.sprayOutlet = .movableAbdomenTip
  pressureDrivesJet :
    setup.chamberPressureRegime = .highEnoughToDriveJet
  figureShowsBeetle : setup.figure.showsBeetle = true
  figureShowsFingerContact : setup.figure.showsHumanFingerContact = true
  figureShowsSprayCloud : setup.figure.showsDefensiveSprayCloud = true
  figureHasNoPrintedLabels : setup.figure.hasPrintedTextOrLabels = false

/-!
The governing constant-specific-heat calorimetry relation per unit mass,

`q / m = c ΔT`.

This is a general physical law instantiated with the reacted spray's specific
heat and the observed temperature rise.  It does not contain the simplified
numeric heat or any answer-choice value.
-/
structure SatisfiesBombardierBeetleCalorimetryLaw
    (setup : BombardierBeetleCalorimetrySetup) : Prop where
  releasedHeatRaisesSprayTemperature :
    specificEnergyInJoulesPerKilogram setup.heatOfReactionPerUnitMass =
      specificHeatInJoulesPerKilogramKelvin
          (setup.specificHeatCapacity .reactedSpray) *
        temperatureRiseInKelvins setup

/-!
The stated initial and final temperatures give an `80 K` temperature rise.
This is a derived result, not a field of either premise structure.
-/
lemma temperatureRiseInKelvins_eq_eighty
    (setup : BombardierBeetleCalorimetrySetup)
    (_data : MatchesBombardierBeetleProblemData setup) :
    temperatureRiseInKelvins setup = 80 := by
  unfold temperatureRiseInKelvins
  rw [_data.finalTemperatureCelsius, _data.initialTemperatureCelsius]
  norm_num

/-! ## Displayed answers -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Joule-per-kilogram value printed beside each answer label. -/
def answerHeatOfReactionJoulesPerKilogram : AnswerChoice → ℝ
  | .A => 340000
  | .B => 312000
  | .C => 322000
  | .D => 202000

/-- Dataset metadata records answer A; this definition is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- A displayed choice is uniquely closest to the derived specific energy. -/
def IsUniqueClosestDisplayedAnswer
    (setup : BombardierBeetleCalorimetrySetup)
    (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |specificEnergyInJoulesPerKilogram setup.heatOfReactionPerUnitMass -
        answerHeatOfReactionJoulesPerKilogram choice| <
      |specificEnergyInJoulesPerKilogram setup.heatOfReactionPerUnitMass -
        answerHeatOfReactionJoulesPerKilogram other|

/-!
The calorimetry law gives the unrounded value

`(4.19 × 10³ J/(kg K)) (100 - 20 K) = 335200 J/kg`.

Among the displayed rounded values, `3.4 × 10⁵ J/kg` is uniquely closest, so
the selected answer is A.

This formalizes blueprint label `thm:physics:phyx_mini_0332:target`.
-/
theorem problem_phyx_mini_0332
    (setup : BombardierBeetleCalorimetrySetup)
    (_data : MatchesBombardierBeetleProblemData setup)
    (_calorimetry : SatisfiesBombardierBeetleCalorimetryLaw setup) :
    specificEnergyInJoulesPerKilogram setup.heatOfReactionPerUnitMass =
        335200 ∧
      IsUniqueClosestDisplayedAnswer setup .A := by
  have hRise := temperatureRiseInKelvins_eq_eighty setup _data
  have hHeat :
      specificEnergyInJoulesPerKilogram setup.heatOfReactionPerUnitMass =
        335200 := by
    rw [_calorimetry.releasedHeatRaisesSprayTemperature,
      _data.chemicalsAndSprayMatchWater,
      _data.waterSpecificHeatJoulesPerKilogramKelvin, hRise]
    norm_num
  constructor
  · exact hHeat
  · unfold IsUniqueClosestDisplayedAnswer
    intro other hother
    rw [hHeat]
    cases other with
    | A => exact (hother rfl).elim
    | B => norm_num [answerHeatOfReactionJoulesPerKilogram]
    | C => norm_num [answerHeatOfReactionJoulesPerKilogram]
    | D => norm_num [answerHeatOfReactionJoulesPerKilogram]

end PhyXMiniProblems.ProblemPhyXMini0332
