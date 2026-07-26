import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0456

open Dimension

/-!
# Equilibrium temperature of a composite automobile engine

An automobile engine contains a cast-iron block, an aluminum head, steel
parts, engine oil, and glycerine antifreeze. Every component begins at
`5 °C`; the engine then absorbs a net `7000 kJ` and reaches one steady,
uniform temperature.

Mass, absorbed heat, absolute temperature, and specific heat capacity are
represented by physical quantity types. Real numbers occur only as calibrated
readouts in named units, temperature differences, and displayed
multiple-choice values.
-/

/-! ## Physical quantities and calibrated readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/--
Mass-specific heat capacity, of dimension
`length² / (time² * temperature)`. Its SI readout is in
joules per kilogram-kelvin.
-/
abbrev SpecificHeatCapacityQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Read a physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a physical energy in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Read a specific heat capacity in joules per kilogram-kelvin. -/
def specificHeatInJoulesPerKilogramKelvin
    (capacity : SpecificHeatCapacityQuantity) : ℝ :=
  ((capacity UnitChoices.SI).val : ℝ)

/-!
Physlib's `Temperature` represents absolute temperature on a
zero-preserving scale. This structure couples it to the affine Celsius
readout printed in the exercise, with the absolute magnitude calibrated in
kelvins.
-/
structure CelsiusTemperatureReading where
  absoluteKelvinTemperature : Temperature
  degreesCelsius : ℝ
  kelvinCalibration :
    absoluteKelvinTemperature.toReal = degreesCelsius + 27315 / 100

/-! ## Engine composition and primary-figure vocabulary -/

/-- The five thermally significant engine components listed in the prose. -/
inductive EngineComponent where
  | block
  | head
  | steelParts
  | engineOil
  | antifreeze
  deriving DecidableEq, Fintype, Repr

/-- The material assigned to each thermally significant component. -/
inductive ThermalMaterial where
  | castIron
  | aluminum
  | steel
  | oil
  | glycerine
  deriving DecidableEq, Fintype, Repr

/-- The material composition specified for each engine component. -/
def EngineComponent.material : EngineComponent → ThermalMaterial
  | .block => .castIron
  | .head => .aluminum
  | .steelParts => .steel
  | .engineOil => .oil
  | .antifreeze => .glycerine

/-- Mechanical objects visibly represented in the supplied cutaway raster. -/
inductive FigureObject where
  | engineAssembly
  | cylinderBanks
  | pistons
  | connectingRods
  | crankshaft
  | rockerArms
  | pulley
  | canister
  deriving DecidableEq, Fintype, Repr

/-- Literal text labels visible in the supplied raster. -/
inductive FigureLabel where
  | automobileEngine
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrangement of the two cylinder banks in the raster. -/
inductive CylinderBankArrangement where
  | vee
  | inline
  | other
  deriving DecidableEq, Repr

/-!
Qualitative evidence retained from the primary image. The raster identifies
the apparatus as an automobile engine and shows its cutaway geometry, but it
contains no printed thermal datum or answer value.
-/
structure SuppliedEngineFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  cylinderBankArrangement : CylinderBankArrangement
  isCutawaySchematic : Bool
  hasPrintedThermalData : Bool

/-!
Independent physical observables and material properties of the heating
experiment. The final uniform temperature is a free physical reading; it is
not defined from the recorded answer or from `80 °C`.
-/
structure CompositeEngineHeatingSetup where
  componentMass : EngineComponent → MassQuantity
  specificHeatCapacity : ThermalMaterial → SpecificHeatCapacityQuantity
  initialTemperature : EngineComponent → CelsiusTemperatureReading
  finalUniformTemperature : CelsiusTemperatureReading
  netHeatAbsorbed : DimEnergy
  reachesSteadyUniformTemperature : Bool
  usesConstantSpecificHeatModel : Bool
  figure : SuppliedEngineFigure

/-- Celsius readout of the common equilibrium temperature being requested. -/
def finalTemperatureInDegreesCelsius
    (setup : CompositeEngineHeatingSetup) : ℝ :=
  setup.finalUniformTemperature.degreesCelsius

/-- Heat capacity of one component in joules per kelvin. -/
def componentHeatCapacityInJoulesPerKelvin
    (setup : CompositeEngineHeatingSetup)
    (component : EngineComponent) : ℝ :=
  massInKilograms (setup.componentMass component) *
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity component.material)

/-- Sum of the five component heat capacities in joules per kelvin. -/
def totalHeatCapacityInJoulesPerKelvin
    (setup : CompositeEngineHeatingSetup) : ℝ :=
  ∑ component : EngineComponent,
    componentHeatCapacityInJoulesPerKelvin setup component

/-! ## Assumptions from the prose, raster, and calorimetry model -/

/-- Qualitative process conditions explicitly described in the problem. -/
structure MatchesCompositeEngineHeatingScenario
    (setup : CompositeEngineHeatingSetup) : Prop where
  equilibriumIsSteadyAndUniform :
    setup.reachesSteadyUniformTemperature = true
  constantSpecificHeatApproximation :
    setup.usesConstantSpecificHeatModel = true

/-!
The five masses, common initial temperature, and absorbed energy printed in
the problem. No field mentions the final temperature or an answer choice.
-/
structure MatchesProblemReadouts
    (setup : CompositeEngineHeatingSetup) : Prop where
  castIronBlockMassKilograms :
    massInKilograms (setup.componentMass .block) = 100
  aluminumHeadMassKilograms :
    massInKilograms (setup.componentMass .head) = 20
  steelPartsMassKilograms :
    massInKilograms (setup.componentMass .steelParts) = 20
  engineOilMassKilograms :
    massInKilograms (setup.componentMass .engineOil) = 5
  glycerineAntifreezeMassKilograms :
    massInKilograms (setup.componentMass .antifreeze) = 6
  everyInitialTemperatureIsFiveCelsius :
    ∀ component,
      (setup.initialTemperature component).degreesCelsius = 5
  absorbedNetHeatKilojoules :
    energyInKilojoules setup.netHeatAbsorbed = 7000

/-!
Standard reference values for the five material specific heats. These are
supplemental textbook data required by the numerical question rather than
values printed in the problem. None is a final-temperature assertion.
-/
structure UsesReferenceEngineMaterialThermalData
    (setup : CompositeEngineHeatingSetup) : Prop where
  castIronSpecificHeat :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity .castIron) = 450
  aluminumSpecificHeat :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity .aluminum) = 900
  steelSpecificHeat :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity .steel) = 450
  engineOilSpecificHeat :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity .oil) = 2000
  glycerineSpecificHeat :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity .glycerine) = 2400

/-- Qualitative facts read from the primary automobile-engine raster. -/
structure MatchesSuppliedEngineFigure
    (figure : SuppliedEngineFigure) : Prop where
  everyRepresentedObjectIsShown :
    ∀ object, figure.showsObject object = true
  automobileEngineLabelIsShown :
    figure.showsLabel .automobileEngine = true
  cylinderBanksFormAVee :
    figure.cylinderBankArrangement = .vee
  imageIsACutawaySchematic : figure.isCutawaySchematic = true
  noPrintedThermalData : figure.hasPrintedThermalData = false

/-- Positivity conditions selecting a physical heating experiment. -/
structure HasPhysicalCompositeEngineParameters
    (setup : CompositeEngineHeatingSetup) : Prop where
  componentMassPositive :
    ∀ component, 0 < massInKilograms (setup.componentMass component)
  specificHeatPositive :
    ∀ material,
      0 < specificHeatInJoulesPerKilogramKelvin
        (setup.specificHeatCapacity material)
  absorbedHeatPositive : 0 < energyInJoules setup.netHeatAbsorbed
  initialAbsoluteTemperaturePositive :
    ∀ component,
      0 < (setup.initialTemperature component).absoluteKelvinTemperature.toReal
  finalAbsoluteTemperaturePositive :
    0 < setup.finalUniformTemperature.absoluteKelvinTemperature.toReal

/-!
The governing composite-body calorimetry law

`Q = ∑ᵢ mᵢ cᵢ (T_final - T_initial,i)`.

Because Celsius and kelvin increments have the same size, the calibrated
Celsius differences may be used with SI specific heats. The equation relates
the unknown final temperature to the input data but does not assign it the
requested numerical value.
-/
structure SatisfiesCompositeEngineCalorimetryLaw
    (setup : CompositeEngineHeatingSetup) : Prop where
  absorbedHeatEqualsTotalSensibleHeat :
    energyInJoules setup.netHeatAbsorbed =
      ∑ component : EngineComponent,
        componentHeatCapacityInJoulesPerKelvin setup component *
          (finalTemperatureInDegreesCelsius setup -
            (setup.initialTemperature component).degreesCelsius)

/-! ## Displayed choices and current target -/

/-- Labels of the four temperatures printed in the answer list. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Celsius values printed beside the four answer labels. -/
def displayedTemperatureInDegreesCelsius : AnswerChoice → ℝ
  | .A => 50
  | .B => 60
  | .C => 100
  | .D => 80

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The final reading rounds to a displayed whole-ten Celsius value. -/
def RoundsToDisplayedTemperature
    (setup : CompositeEngineHeatingSetup) (choice : AnswerChoice) : Prop :=
  |finalTemperatureInDegreesCelsius setup -
      displayedTemperatureInDegreesCelsius choice| < 5

/-- A displayed choice is at least as close as every displayed temperature. -/
def IsClosestDisplayedTemperature
    (setup : CompositeEngineHeatingSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |finalTemperatureInDegreesCelsius setup -
        displayedTemperatureInDegreesCelsius choice| ≤
      |finalTemperatureInDegreesCelsius setup -
        displayedTemperatureInDegreesCelsius other|

/-- The selected choice is the unique closest displayed temperature. -/
def IsUniqueClosestDisplayedTemperature
    (setup : CompositeEngineHeatingSetup) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedTemperature setup choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedTemperature setup other → other = choice

/-!
The five reference heat capacities give a total heat capacity of
`96400 J/K`. The absorbed `7,000,000 J` therefore raises the engine from
`5 °C` to about `77.6 °C`, which rounds to and uniquely selects the displayed
`80 °C` answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0456:target`.
-/
theorem problem_phyx_mini_0456
    (setup : CompositeEngineHeatingSetup)
    (hScenario : MatchesCompositeEngineHeatingScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hThermalData : UsesReferenceEngineMaterialThermalData setup)
    (hFigure : MatchesSuppliedEngineFigure setup.figure)
    (hPhysical : HasPhysicalCompositeEngineParameters setup)
    (hCalorimetry : SatisfiesCompositeEngineCalorimetryLaw setup) :
    RoundsToDisplayedTemperature setup .D ∧
      IsUniqueClosestDisplayedTemperature setup .D := by
  have hEnergy : energyInJoules setup.netHeatAbsorbed = 7000000 := by
    have h := hReadouts.absorbedNetHeatKilojoules
    norm_num [energyInKilojoules] at h ⊢
    linarith
  have hComponents : (Finset.univ : Finset EngineComponent) =
      {.block, .head, .steelParts, .engineOil, .antifreeze} := by
    decide
  have hBalance := hCalorimetry.absorbedHeatEqualsTotalSensibleHeat
  rw [hEnergy, hComponents] at hBalance
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hBalance
  norm_num [componentHeatCapacityInJoulesPerKelvin, EngineComponent.material,
    hReadouts.castIronBlockMassKilograms,
    hReadouts.aluminumHeadMassKilograms,
    hReadouts.steelPartsMassKilograms,
    hReadouts.engineOilMassKilograms,
    hReadouts.glycerineAntifreezeMassKilograms,
    hReadouts.everyInitialTemperatureIsFiveCelsius,
    hThermalData.castIronSpecificHeat,
    hThermalData.aluminumSpecificHeat,
    hThermalData.steelSpecificHeat,
    hThermalData.engineOilSpecificHeat,
    hThermalData.glycerineSpecificHeat] at hBalance
  have hFinal :
      finalTemperatureInDegreesCelsius setup = (18705 / 241 : ℝ) := by
    norm_num
    linarith [hBalance]
  constructor
  · unfold RoundsToDisplayedTemperature
    rw [hFinal]
    norm_num [displayedTemperatureInDegreesCelsius]
  · unfold IsUniqueClosestDisplayedTemperature
    constructor
    · intro other
      cases other <;> rw [hFinal] <;>
        norm_num [IsClosestDisplayedTemperature,
          displayedTemperatureInDegreesCelsius]
    · intro other hOther
      cases other
      · have h := hOther .D
        rw [hFinal] at h
        norm_num [IsClosestDisplayedTemperature,
          displayedTemperatureInDegreesCelsius] at h
      · have h := hOther .D
        rw [hFinal] at h
        norm_num [IsClosestDisplayedTemperature,
          displayedTemperatureInDegreesCelsius] at h
      · have h := hOther .D
        rw [hFinal] at h
        norm_num [IsClosestDisplayedTemperature,
          displayedTemperatureInDegreesCelsius] at h
      · rfl

end PhyXMiniProblems.ProblemPhyXMini0456
