import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0348

open Dimension

/-!
# Net work of a three-process ideal-gas engine cycle

The engine contains `0.350 mol` of a diatomic ideal gas. Its directed cycle
has an isochoric leg `1 → 2`, an adiabatic leg `2 → 3`, and an isobaric
leg `3 → 1`. The pressure--volume diagram labels the three absolute
temperatures as `300 K`, `600 K`, and `492 K`, and places states 1 and 3 on
the horizontal `1.00 atm` line.

Pressure, volume, and work are unit-independent physical quantities.
Temperature uses Physlib's absolute `Temperature` type. Physlib currently
has no amount-of-substance base dimension, so the gas amount is an abstract
type equipped with an explicit mole readout. Real scalars below are used only
for named-unit readouts, dimensionless diagram coordinates, the dimensionless
heat-capacity ratio, and displayed answer values.
-/

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A signed physical energy, used for work done by the gas. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Read a physical energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- The three equilibrium states labelled in the pressure--volume diagram. -/
inductive CycleState where
  | state1
  | state2
  | state3
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs of the engine cycle. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed cycle leg. -/
def legSource : CycleLeg → CycleState
  | .oneToTwo => .state1
  | .twoToThree => .state2
  | .threeToOne => .state3

/-- Final state of each directed cycle leg. -/
def legTarget : CycleLeg → CycleState
  | .oneToTwo => .state2
  | .twoToThree => .state3
  | .threeToOne => .state1

/-- Thermodynamic constraint assigned to a cycle leg. -/
inductive ProcessKind where
  | constantVolume
  | adiabatic
  | constantPressure
  deriving DecidableEq, Repr

/-- Molecular model of the gas named in the problem. -/
inductive GasMolecularStructure where
  | monatomic
  | diatomic
  | other
  deriving DecidableEq, Repr

/-- Physical quantities represented by the two diagram axes. -/
inductive DiagramAxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Qualitative shapes of the three blue paths in the primary figure. -/
inductive DiagramPathShape where
  | vertical
  | downwardCurved
  | horizontal
  deriving DecidableEq, Repr

/-!
Data read from the primary raster. The coordinates are dimensionless drawing
coordinates used only to record the relative placement of the black points.
Physical pressures, volumes, and temperatures are stored separately in
`IdealGasEngineCycleSetup`.
-/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : DiagramAxisQuantity
  verticalAxisQuantity : DiagramAxisQuantity
  showsOriginLabelO : Bool
  showsStateLabel : CycleState → Bool
  showsDirectedArrow : CycleLeg → Bool
  pathShape : CycleLeg → DiagramPathShape
  horizontalCoordinate : CycleState → ℝ
  verticalCoordinate : CycleState → ℝ
  displayedTemperatureKelvin : CycleState → ℝ
  displayedReferencePressureAtmospheres : ℝ

/-!
Independent physical quantities and observables of the heat-engine cycle.
The net work is an independent `EnergyQuantity`; it is not defined from an
answer choice or from a segment-work formula.
-/
structure IdealGasEngineCycleSetup (AmountOfSubstance : Type) where
  gasMolecularStructure : GasMolecularStructure
  gasAmount : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  pressureAt : CycleState → DimPressure
  volumeAt : CycleState → VolumeQuantity
  temperatureAt : CycleState → Temperature
  temperatureStorageUnit : TemperatureUnit
  heatCapacityRatioGamma : ℝ
  universalGasConstantJoulesPerMoleKelvin : ℝ
  processKind : CycleLeg → ProcessKind
  workDoneByGasOnLeg : CycleLeg → EnergyQuantity
  netWorkDoneByGas : EnergyQuantity
  figure : PressureVolumeDiagram

/-- Convert a stored absolute temperature to a kelvin readout. -/
def temperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance)
    (state : CycleState) : ℝ :=
  let unitRatio : NNReal :=
    setup.temperatureStorageUnit / TemperatureUnit.kelvin
  (setup.temperatureAt state).toReal * (unitRatio : ℝ)

/-- Mole readout of the physical amount of gas carried around the cycle. -/
def gasAmountInMoles
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance) : ℝ :=
  setup.amountInMoles setup.gasAmount

/-!
Qualitative and numerical information read from the primary pressure--volume
diagram. It records the axes, labels, arrows, point geometry, temperature
labels, and the `1.00 atm` reference line. It contains no work value.
-/
structure MatchesPrimaryPressureVolumeDiagram
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  originLabelShown : setup.figure.showsOriginLabelO = true
  everyStateLabelShown :
    ∀ state, setup.figure.showsStateLabel state = true
  everyDirectedArrowShown :
    ∀ leg, setup.figure.showsDirectedArrow leg = true
  oneToTwoDrawnVertical :
    setup.figure.pathShape .oneToTwo = .vertical
  twoToThreeDrawnAsDownwardCurve :
    setup.figure.pathShape .twoToThree = .downwardCurved
  threeToOneDrawnHorizontal :
    setup.figure.pathShape .threeToOne = .horizontal
  state1AndState2ShareHorizontalCoordinate :
    setup.figure.horizontalCoordinate .state1 =
      setup.figure.horizontalCoordinate .state2
  state3LiesRightOfState1 :
    setup.figure.horizontalCoordinate .state1 <
      setup.figure.horizontalCoordinate .state3
  state1AndState3ShareVerticalCoordinate :
    setup.figure.verticalCoordinate .state1 =
      setup.figure.verticalCoordinate .state3
  state2LiesAboveState1 :
    setup.figure.verticalCoordinate .state1 <
      setup.figure.verticalCoordinate .state2
  displayedTemperatureAtState1 :
    setup.figure.displayedTemperatureKelvin .state1 = 300
  displayedTemperatureAtState2 :
    setup.figure.displayedTemperatureKelvin .state2 = 600
  displayedTemperatureAtState3 :
    setup.figure.displayedTemperatureKelvin .state3 = 492
  displayedTemperaturesMatchPhysicalStates :
    ∀ state,
      temperatureInKelvin setup state =
        setup.figure.displayedTemperatureKelvin state
  displayedReferencePressure :
    setup.figure.displayedReferencePressureAtmospheres = 1
  state1OnReferencePressureLine :
    pressureInAtmospheres (setup.pressureAt .state1) =
      setup.figure.displayedReferencePressureAtmospheres
  state3OnReferencePressureLine :
    pressureInAtmospheres (setup.pressureAt .state3) =
      setup.figure.displayedReferencePressureAtmospheres

/-!
Problem-statement data not supplied solely by the raster: the gas is
diatomic, its amount is `0.350 mol`, its heat-capacity ratio is `1.40`, and
the three directed legs have the stated process types. No work value occurs
here.
-/
structure MatchesProblemDescription
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance) : Prop where
  gasIsDiatomic : setup.gasMolecularStructure = .diatomic
  gasAmountMoles : gasAmountInMoles setup = 7 / 20
  heatCapacityRatio : setup.heatCapacityRatioGamma = 7 / 5
  oneToTwoIsConstantVolume :
    setup.processKind .oneToTwo = .constantVolume
  twoToThreeIsAdiabatic :
    setup.processKind .twoToThree = .adiabatic
  threeToOneIsConstantPressure :
    setup.processKind .threeToOne = .constantPressure

/-- Positive and nondegenerate parameters of the physical gas states. -/
structure HasPhysicalIdealGasCycleParameters
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance) : Prop where
  gasAmountPositive : 0 < gasAmountInMoles setup
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.pressureAt state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.volumeAt state)
  absoluteTemperaturePositive :
    ∀ state, 0 < temperatureInKelvin setup state
  heatCapacityRatioGreaterThanOne :
    1 < setup.heatCapacityRatioGamma
  gasConstantPositive :
    0 < setup.universalGasConstantJoulesPerMoleKelvin

/-!
Governing relations for the ideal-gas cycle, written in coherent SI readouts:

* every state satisfies `pV = nRT`;
* an isochoric leg keeps volume fixed and does no boundary work;
* an adiabatic leg obeys the Poisson temperature--volume relation and
  `W = nR(Tᵢ - T_f)/(γ - 1)`;
* an isobaric leg keeps pressure fixed and has work `W = p(V_f - Vᵢ)`;
* cycle work is the sum of the work on the three directed legs.

These laws are generic over states and legs and contain no requested answer.
-/
structure SatisfiesIdealGasCycleLaws
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance) : Prop where
  idealGasLaw :
    ∀ state,
      pressureInPascals (setup.pressureAt state) *
          volumeInCubicMeters (setup.volumeAt state) =
        gasAmountInMoles setup *
          setup.universalGasConstantJoulesPerMoleKelvin *
            temperatureInKelvin setup state
  constantVolumeLaw :
    ∀ leg,
      setup.processKind leg = .constantVolume →
        setup.volumeAt (legSource leg) = setup.volumeAt (legTarget leg)
  constantVolumeWorkLaw :
    ∀ leg,
      setup.processKind leg = .constantVolume →
        energyInJoules (setup.workDoneByGasOnLeg leg) = 0
  adiabaticTemperatureVolumeLaw :
    ∀ leg,
      setup.processKind leg = .adiabatic →
        temperatureInKelvin setup (legSource leg) /
            temperatureInKelvin setup (legTarget leg) =
          Real.rpow
            (volumeInCubicMeters (setup.volumeAt (legTarget leg)) /
              volumeInCubicMeters (setup.volumeAt (legSource leg)))
            (setup.heatCapacityRatioGamma - 1)
  adiabaticWorkLaw :
    ∀ leg,
      setup.processKind leg = .adiabatic →
        energyInJoules (setup.workDoneByGasOnLeg leg) =
          gasAmountInMoles setup *
            setup.universalGasConstantJoulesPerMoleKelvin *
              (temperatureInKelvin setup (legSource leg) -
                temperatureInKelvin setup (legTarget leg)) /
                  (setup.heatCapacityRatioGamma - 1)
  constantPressureLaw :
    ∀ leg,
      setup.processKind leg = .constantPressure →
        setup.pressureAt (legSource leg) = setup.pressureAt (legTarget leg)
  constantPressureWorkLaw :
    ∀ leg,
      setup.processKind leg = .constantPressure →
        energyInJoules (setup.workDoneByGasOnLeg leg) =
          pressureInPascals (setup.pressureAt (legSource leg)) *
            (volumeInCubicMeters (setup.volumeAt (legTarget leg)) -
              volumeInCubicMeters (setup.volumeAt (legSource leg)))
  netWorkBalance :
    energyInJoules setup.netWorkDoneByGas =
      energyInJoules (setup.workDoneByGasOnLeg .oneToTwo) +
        energyInJoules (setup.workDoneByGasOnLeg .twoToThree) +
          energyInJoules (setup.workDoneByGasOnLeg .threeToOne)

/-!
The conventional molar gas constant, represented to the precision used in
the multiple-choice computation: `R = 8.314 J mol⁻¹ K⁻¹`.
-/
def UsesStandardMolarGasConstant
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance) : Prop :=
  setup.universalGasConstantJoulesPerMoleKelvin = 4157 / 500

/-- Labels of the four work choices printed by the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Joule value displayed beside each multiple-choice label. -/
def displayedWorkInJoules : AnswerChoice → ℝ
  | .A => 150
  | .B => 220
  | .C => 505
  | .D => 320

/-- The source dataset records answer label B; this is metadata, not a premise. -/
def recordedDatasetAnswerChoice : AnswerChoice := .B

/-- A choice is at least as close to the calculated work as every choice. -/
def IsNearestDisplayedWork
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |energyInJoules setup.netWorkDoneByGas - displayedWorkInJoules choice| ≤
      |energyInJoules setup.netWorkDoneByGas - displayedWorkInJoules other|

/-- A choice is the unique nearest displayed work value. -/
def IsUniqueNearestDisplayedWork
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance)
    (choice : AnswerChoice) : Prop :=
  IsNearestDisplayedWork setup choice ∧
    ∀ other : AnswerChoice,
      IsNearestDisplayedWork setup other → other = choice

/-!
The generic process-work laws reduce the cycle work to an expression in the
amount, gas constant, heat-capacity ratio, and endpoint temperatures. This
derived formula still contains no answer-choice value.
-/
lemma netWorkInJoules_eq_temperature_formula
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance)
    (hDescription : MatchesProblemDescription setup)
    (hPhysical : HasPhysicalIdealGasCycleParameters setup)
    (hLaws : SatisfiesIdealGasCycleLaws setup) :
    energyInJoules setup.netWorkDoneByGas =
      gasAmountInMoles setup *
        setup.universalGasConstantJoulesPerMoleKelvin *
          ((temperatureInKelvin setup .state2 -
                temperatureInKelvin setup .state3) /
              (setup.heatCapacityRatioGamma - 1) +
            (temperatureInKelvin setup .state1 -
              temperatureInKelvin setup .state3)) := by
  have hWorkOneToTwo :=
    hLaws.constantVolumeWorkLaw .oneToTwo
      hDescription.oneToTwoIsConstantVolume
  have hWorkTwoToThree :=
    hLaws.adiabaticWorkLaw .twoToThree
      hDescription.twoToThreeIsAdiabatic
  have hWorkThreeToOne :=
    hLaws.constantPressureWorkLaw .threeToOne
      hDescription.threeToOneIsConstantPressure
  have hPressureThreeToOne :=
    hLaws.constantPressureLaw .threeToOne
      hDescription.threeToOneIsConstantPressure
  have hPressureReadout :
      pressureInPascals (setup.pressureAt .state3) =
        pressureInPascals (setup.pressureAt .state1) :=
    congrArg pressureInPascals hPressureThreeToOne
  have hIdealGasAtOne := hLaws.idealGasLaw .state1
  have hIdealGasAtThree := hLaws.idealGasLaw .state3
  have hIsobaricWork :
      pressureInPascals (setup.pressureAt .state3) *
          (volumeInCubicMeters (setup.volumeAt .state1) -
            volumeInCubicMeters (setup.volumeAt .state3)) =
        gasAmountInMoles setup *
          setup.universalGasConstantJoulesPerMoleKelvin *
            (temperatureInKelvin setup .state1 -
              temperatureInKelvin setup .state3) := by
    rw [hPressureReadout]
    rw [hPressureReadout] at hIdealGasAtThree
    nlinarith [hIdealGasAtOne, hIdealGasAtThree]
  rw [hLaws.netWorkBalance, hWorkOneToTwo, hWorkTwoToThree,
    hWorkThreeToOne]
  simp only [legSource, legTarget] at hWorkTwoToThree hWorkThreeToOne ⊢
  rw [hIsobaricWork]
  ring

/-!
With `n = 0.350 mol`, `R = 8.314 J mol⁻¹ K⁻¹`, `γ = 1.40`, and the
three displayed temperatures, the model gives `226.9722 J`. This is uniquely
closest to the supplied choice `220 J`, so the recorded answer is B.

This formalizes `thm:physics:phyx_mini_0348:target`.
-/
theorem problem_phyx_mini_0348
    {AmountOfSubstance : Type}
    (setup : IdealGasEngineCycleSetup AmountOfSubstance)
    (hFigure : MatchesPrimaryPressureVolumeDiagram setup)
    (hDescription : MatchesProblemDescription setup)
    (hPhysical : HasPhysicalIdealGasCycleParameters setup)
    (hLaws : SatisfiesIdealGasCycleLaws setup)
    (hGasConstant : UsesStandardMolarGasConstant setup) :
    energyInJoules setup.netWorkDoneByGas = (1134861 / 5000 : ℝ) ∧
      IsUniqueNearestDisplayedWork setup .B := by
  have hTemperatureOne : temperatureInKelvin setup .state1 = 300 :=
    (hFigure.displayedTemperaturesMatchPhysicalStates .state1).trans
      hFigure.displayedTemperatureAtState1
  have hTemperatureTwo : temperatureInKelvin setup .state2 = 600 :=
    (hFigure.displayedTemperaturesMatchPhysicalStates .state2).trans
      hFigure.displayedTemperatureAtState2
  have hTemperatureThree : temperatureInKelvin setup .state3 = 492 :=
    (hFigure.displayedTemperaturesMatchPhysicalStates .state3).trans
      hFigure.displayedTemperatureAtState3
  change setup.universalGasConstantJoulesPerMoleKelvin = 4157 / 500 at hGasConstant
  have hNetWork :=
    netWorkInJoules_eq_temperature_formula setup hDescription hPhysical hLaws
  rw [hDescription.gasAmountMoles, hGasConstant,
    hDescription.heatCapacityRatio, hTemperatureOne,
    hTemperatureTwo, hTemperatureThree] at hNetWork
  norm_num at hNetWork
  refine ⟨hNetWork, ?_⟩
  constructor
  · intro other
    rw [hNetWork]
    cases other <;> norm_num [displayedWorkInJoules]
  · intro other hOther
    cases other with
    | A =>
        exfalso
        have h := hOther .B
        rw [hNetWork] at h
        norm_num [displayedWorkInJoules] at h
    | B => rfl
    | C =>
        exfalso
        have h := hOther .B
        rw [hNetWork] at h
        norm_num [displayedWorkInJoules] at h
    | D =>
        exfalso
        have h := hOther .B
        rw [hNetWork] at h
        norm_num [displayedWorkInJoules] at h

end PhyXMiniProblems.ProblemPhyXMini0348
