import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0486

open Dimension

/-!
# Heating an iron nail with repeated hammer blows

A `1.20 kg` hammer head moving at `7.5 m/s` is stopped by each impact.  An
iron nail of mass `14 g` receives eight such blows in quick succession and is
assumed to absorb all of the hammer head's lost kinetic energy.

Mass, speed, energy, specific heat capacity, and temperature difference are
represented by Physlib's unit-independent dimensionful quantities.  Real
numbers occur only as named coherent-SI readouts, displayed answer values, or
dimensionless counts.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical mass carrying dimension `M`. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical speed carrying dimension `L T⁻¹`. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed physical energy carrying dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/--
A nonnegative specific heat capacity carrying dimension `L² T⁻² Θ⁻¹`.
Its coherent-SI readout is in joules per kilogram-kelvin.
-/
abbrev SpecificHeatCapacityQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- A nonnegative physical temperature difference carrying dimension `Θ`. -/
abbrev TemperatureDifferenceQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a specific heat capacity in joules per kilogram-kelvin. -/
def specificHeatInJoulesPerKilogramKelvin
    (specificHeat : SpecificHeatCapacityQuantity) : ℝ :=
  ((specificHeat UnitChoices.SI).val : ℝ)

/-- Read a temperature difference in kelvins. -/
def temperatureDifferenceInKelvins
    (difference : TemperatureDifferenceQuantity) : ℝ :=
  ((difference UnitChoices.SI).val : ℝ)

/--
The numerical size of a temperature interval is the same in kelvins and
degrees Celsius.  This readout names that fact for the requested temperature
rise, without treating an absolute Celsius temperature as a vector quantity.
-/
def temperatureRiseInDegreesCelsius
    (rise : TemperatureDifferenceQuantity) : ℝ :=
  temperatureDifferenceInKelvins rise

/-! ## Physical bodies, timing, and primary-figure vocabulary -/

/-- Physical objects distinguishable in the supplied image. -/
inductive FigureObject where
  | hammerHead
  | hammerHandle
  | nail
  | woodBlock
  deriving DecidableEq, Fintype, Repr

/-- Material roles stated in the prose or visible in the supplied image. -/
inductive MaterialKind where
  | iron
  | wood
  | unspecifiedMetal
  deriving DecidableEq, Repr

/-- Timing of the repeated hammer impacts. -/
inductive ImpactTiming where
  | quickSuccession
  | separatedWithCooling
  deriving DecidableEq, Repr

/--
Qualitative data transcribed from primary image `486.png`.  The image shows no
numeric annotation, so all numerical data remain in the prose-data predicate
below.
-/
structure HammerNailFigure where
  objectShown : FigureObject → Bool
  hammerHeadAttachedToHandle : Bool
  hammerMovingTowardNail : Bool
  nailPartiallyInsertedIntoWood : Bool
  woodGrainVisible : Bool
  motionStrokesVisible : Bool
  numericAnnotationShown : Bool

/-!
Independent quantities of the impact-heating experiment.  In particular, the
nail's temperature rise and the three energy observables are not defined from
an answer choice; the governing laws below constrain them.
-/
structure HammerNailHeatingSetup where
  material : FigureObject → MaterialKind
  hammerHeadMass : MassQuantity
  hammerSpeedBeforeImpact : SpeedQuantity
  hammerSpeedAfterImpact : SpeedQuantity
  nailMass : MassQuantity
  ironSpecificHeat : SpecificHeatCapacityQuantity
  kineticEnergyLostPerBlow : EnergyQuantity
  totalKineticEnergyLost : EnergyQuantity
  thermalEnergyAbsorbedByNail : EnergyQuantity
  nailTemperatureRise : TemperatureDifferenceQuantity
  blowCount : ℕ
  impactTiming : ImpactTiming
  figure : HammerNailFigure

/-! ## Problem data, material calibration, and governing laws -/

/-!
Numerical and qualitative information supplied directly by the problem and
primary image.  The nail-mass readout uses kilograms, so `14 g = 14/1000 kg`.
This predicate contains neither a specific-heat calibration nor a requested
temperature-rise value.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : HammerNailHeatingSetup) : Prop where
  hammerHeadMassKilograms :
    massInKilograms setup.hammerHeadMass = 120 / 100
  hammerSpeedBeforeImpactMetersPerSecond :
    speedInMetersPerSecond setup.hammerSpeedBeforeImpact = 75 / 10
  hammerBroughtToRest :
    speedInMetersPerSecond setup.hammerSpeedAfterImpact = 0
  nailMassKilograms :
    massInKilograms setup.nailMass = 14 / 1000
  eightBlows : setup.blowCount = 8
  blowsOccurInQuickSuccession : setup.impactTiming = .quickSuccession
  nailIsIron : setup.material .nail = .iron
  hammerHeadIsMetal : setup.material .hammerHead = .unspecifiedMetal
  hammerHandleIsWood : setup.material .hammerHandle = .wood
  blockIsWood : setup.material .woodBlock = .wood
  everyFigureObjectIsShown :
    ∀ object, setup.figure.objectShown object = true
  headIsAttachedToHandle :
    setup.figure.hammerHeadAttachedToHandle = true
  hammerApproachesNail : setup.figure.hammerMovingTowardNail = true
  nailEntersWood : setup.figure.nailPartiallyInsertedIntoWood = true
  woodGrainIsVisible : setup.figure.woodGrainVisible = true
  motionIsIndicated : setup.figure.motionStrokesVisible = true
  imageHasNoNumericAnnotation :
    setup.figure.numericAnnotationShown = false

/-!
The rounded classroom value `450 J/(kg K)` for the specific heat capacity of
iron.  The source does not print a property table, so this independent material
calibration is explicit rather than hidden in a definition or in the target.
-/
structure UsesRoundedIronSpecificHeat
    (setup : HammerNailHeatingSetup) : Prop where
  ironSpecificHeatJoulesPerKilogramKelvin :
    specificHeatInJoulesPerKilogramKelvin setup.ironSpecificHeat = 450

/-- Positivity and ordering conditions selecting the physical impact branch. -/
structure HasPhysicalImpactParameters
    (setup : HammerNailHeatingSetup) : Prop where
  hammerHeadMassPositive : 0 < massInKilograms setup.hammerHeadMass
  nailMassPositive : 0 < massInKilograms setup.nailMass
  incidentSpeedPositive :
    0 < speedInMetersPerSecond setup.hammerSpeedBeforeImpact
  finalSpeedNotGreaterThanIncidentSpeed :
    speedInMetersPerSecond setup.hammerSpeedAfterImpact ≤
      speedInMetersPerSecond setup.hammerSpeedBeforeImpact
  ironSpecificHeatPositive :
    0 < specificHeatInJoulesPerKilogramKelvin setup.ironSpecificHeat

/-!
Governing impact and calorimetry laws:

* each blow loses the hammer head's change in translational kinetic energy,
  `ΔK = (1/2) m (v_before² - v_after²)`;
* the energy losses of the identical blows add;
* the nail absorbs all of that energy; and
* constant-specific-heat calorimetry gives `Q = m c ΔT`.

These relations are generic in the setup quantities.  They contain no
numerical temperature rise and no displayed answer choice.
-/
structure ObeysImpactEnergyAndCalorimetryLaws
    (setup : HammerNailHeatingSetup) : Prop where
  translationalKineticEnergyLossPerBlow :
    energyInJoules setup.kineticEnergyLostPerBlow =
      (1 / 2 : ℝ) * massInKilograms setup.hammerHeadMass *
        (speedInMetersPerSecond setup.hammerSpeedBeforeImpact ^ 2 -
          speedInMetersPerSecond setup.hammerSpeedAfterImpact ^ 2)
  identicalBlowEnergiesAdd :
    energyInJoules setup.totalKineticEnergyLost =
      (setup.blowCount : ℝ) *
        energyInJoules setup.kineticEnergyLostPerBlow
  nailAbsorbsAllLostEnergy :
    setup.thermalEnergyAbsorbedByNail = setup.totalKineticEnergyLost
  constantSpecificHeatCalorimetry :
    energyInJoules setup.thermalEnergyAbsorbedByNail =
      massInKilograms setup.nailMass *
        specificHeatInJoulesPerKilogramKelvin setup.ironSpecificHeat *
          temperatureDifferenceInKelvins setup.nailTemperatureRise

/-!
The impact and calorimetry model predicts the exact unrounded temperature rise
`300/7 K`, approximately `42.857 K`.  This is a derived result, not a premise.
-/
lemma nailTemperatureRise_exact
    (setup : HammerNailHeatingSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_calibration : UsesRoundedIronSpecificHeat setup)
    (_physical : HasPhysicalImpactParameters setup)
    (_laws : ObeysImpactEnergyAndCalorimetryLaws setup) :
    temperatureDifferenceInKelvins setup.nailTemperatureRise =
      (300 / 7 : ℝ) := by
  have hEnergyPerBlow := _laws.translationalKineticEnergyLossPerBlow
  rw [_problem.hammerHeadMassKilograms,
    _problem.hammerSpeedBeforeImpactMetersPerSecond,
    _problem.hammerBroughtToRest] at hEnergyPerBlow
  norm_num at hEnergyPerBlow
  have hTotalEnergy := _laws.identicalBlowEnergiesAdd
  rw [_problem.eightBlows, hEnergyPerBlow] at hTotalEnergy
  norm_num at hTotalEnergy
  have hAbsorbedEnergy :
      energyInJoules setup.thermalEnergyAbsorbedByNail =
        energyInJoules setup.totalKineticEnergyLost := by
    rw [_laws.nailAbsorbsAllLostEnergy]
  have hCalorimetry := _laws.constantSpecificHeatCalorimetry
  rw [hAbsorbedEnergy, hTotalEnergy, _problem.nailMassKilograms,
    _calibration.ironSpecificHeatJoulesPerKilogramKelvin] at hCalorimetry
  norm_num at hCalorimetry ⊢
  linarith

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Whole-degree Celsius temperature-rise value printed beside each choice. -/
def displayedTemperatureRiseDegreesCelsius : AnswerChoice → ℝ
  | .A => 28
  | .B => 52
  | .C => 34
  | .D => 43

/-- Dataset metadata records answer choice D. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- The modeled rise rounds to the whole-degree value shown by a choice. -/
def RoundsToDisplayedWholeDegree
    (setup : HammerNailHeatingSetup) (choice : AnswerChoice) : Prop :=
  |temperatureRiseInDegreesCelsius setup.nailTemperatureRise -
      displayedTemperatureRiseDegreesCelsius choice| < (1 / 2 : ℝ)

/-- The selected displayed rise is closer than every alternative. -/
def IsUniqueClosestDisplayedTemperatureRise
    (setup : HammerNailHeatingSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |temperatureRiseInDegreesCelsius setup.nailTemperatureRise -
        displayedTemperatureRiseDegreesCelsius choice| <
      |temperatureRiseInDegreesCelsius setup.nailTemperatureRise -
        displayedTemperatureRiseDegreesCelsius other|

/-!
Eight blows supply `270 J`; dividing by the nail heat capacity
`(0.014 kg)(450 J/(kg K))` gives `300/7 K`.  Thus the rise rounds to `43 °C`,
and D is uniquely closest among the displayed choices.

This formalizes blueprint label `thm:physics:phyx_mini_0486:target`.
-/
theorem problem_phyx_mini_0486
    (setup : HammerNailHeatingSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_calibration : UsesRoundedIronSpecificHeat setup)
    (_physical : HasPhysicalImpactParameters setup)
    (_laws : ObeysImpactEnergyAndCalorimetryLaws setup) :
    RoundsToDisplayedWholeDegree setup recordedAnswerChoice ∧
      IsUniqueClosestDisplayedTemperatureRise
        setup recordedAnswerChoice := by
  have hRise := nailTemperatureRise_exact setup _problem _calibration _physical _laws
  have hRiseCelsius :
      temperatureRiseInDegreesCelsius setup.nailTemperatureRise =
        (300 / 7 : ℝ) := by
    exact hRise
  constructor
  · rw [RoundsToDisplayedWholeDegree, hRiseCelsius]
    norm_num [recordedAnswerChoice, displayedTemperatureRiseDegreesCelsius,
      abs_of_nonpos]
  · rw [IsUniqueClosestDisplayedTemperatureRise]
    intro other hOther
    rw [hRiseCelsius]
    fin_cases other
    · norm_num [recordedAnswerChoice, displayedTemperatureRiseDegreesCelsius,
        abs_of_nonneg, abs_of_nonpos]
    · norm_num [recordedAnswerChoice, displayedTemperatureRiseDegreesCelsius,
        abs_of_nonneg, abs_of_nonpos]
    · norm_num [recordedAnswerChoice, displayedTemperatureRiseDegreesCelsius,
        abs_of_nonneg, abs_of_nonpos]
    · simp [recordedAnswerChoice] at hOther

end PhyXMiniProblems.ProblemPhyXMini0486
