import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0474

/-!
# Efficiency of a Carnot heat engine

A Carnot engine absorbs `2000 J` from a hot reservoir at `500 K`, rejects
heat to a cold reservoir at `350 K`, and delivers work.  The supplied figure
marks the rejected heat, work, and efficiency as unknown.

Temperatures and energy transfers retain their physical roles through
Physlib's `Temperature` and `DimEnergy` types.  Real numbers below occur only
as explicitly unit-labelled readouts, a dimensionless efficiency, or displayed
answer-choice percentages.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- Absolute thermodynamic temperature. -/
abbrev TemperatureQuantity : Type := Temperature

/-- A physical heat or work quantity, carrying the dimension of energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical energy quantity in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val / (DimEnergy.joule UnitChoices.SI).val

/-- Read an absolute temperature in kelvins from its stated storage unit. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : TemperatureQuantity) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Heat engine and primary-figure vocabulary -/

/-- The thermodynamic role of the device in the problem. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- The reversible ideal engine model specified by the problem. -/
inductive HeatEngineModel where
  | carnot
  deriving DecidableEq, Repr

/-- The two reservoirs with which the engine exchanges heat. -/
inductive Reservoir where
  | hot
  | cold
  deriving DecidableEq, Fintype, Repr

/-- Locations joined by the arrows in the primary diagram. -/
inductive DiagramNode where
  | hotReservoir
  | engine
  | coldReservoir
  | exterior
  deriving DecidableEq, Repr

/-- Directed energy-transfer arrows shown in the primary diagram. -/
inductive DiagramArrow where
  | heatInput
  | heatRejected
  | workOutput
  deriving DecidableEq, Fintype, Repr

/-- Geometric orientation of an arrow in the primary diagram. -/
inductive ArrowOrientation where
  | downward
  | rightward
  deriving DecidableEq, Repr

/-- Textual quantity labels printed in the primary diagram. -/
inductive FigureLabel where
  | hotTemperature
  | heatInput
  | workOutput
  | efficiency
  | rejectedHeat
  | coldTemperature
  deriving DecidableEq, Fintype, Repr

/-- Raw label and arrow information transcribed from the primary bitmap. -/
structure HeatEngineDiagram where
  labelShown : FigureLabel → Bool
  labelMarkedUnknown : FigureLabel → Bool
  arrowStart : DiagramArrow → DiagramNode
  arrowFinish : DiagramArrow → DiagramNode
  arrowOrientation : DiagramArrow → ArrowOrientation

/--
The physical Carnot-engine setup.  Reservoir heat transfers and net work are
stored as positive energy magnitudes; the efficiency is dimensionless.
-/
structure CarnotHeatEngineSetup where
  deviceRole : ThermodynamicDeviceRole
  model : HeatEngineModel
  temperatureStorageUnit : TemperatureUnit
  reservoirTemperature : Reservoir → TemperatureQuantity
  heatAbsorbedFromHotReservoir : EnergyQuantity
  heatRejectedToColdReservoir : EnergyQuantity
  netWorkOutput : EnergyQuantity
  thermalEfficiency : ℝ
  figure : HeatEngineDiagram

/-! ## Scenario, primary-image data, and governing laws -/

/-- The prose identifies the device as a Carnot heat engine. -/
structure MatchesProblemStatement (setup : CarnotHeatEngineSetup) : Prop where
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  engineUsesCarnotModel : setup.model = .carnot

/--
Figure-derived data and geometry.  The image supplies only the hot input heat
and the two reservoir temperatures; rejected heat, work, and efficiency remain
explicitly marked unknown.
-/
structure MatchesPrimaryHeatEngineFigure
    (setup : CarnotHeatEngineSetup) : Prop where
  temperaturesStoredInKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  hotReservoirTemperatureKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .hot) = 500
  coldReservoirTemperatureKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .cold) = 350
  absorbedHeatJoules :
    energyInJoules setup.heatAbsorbedFromHotReservoir = 2000
  everyQuantityLabelIsShown :
    ∀ label : FigureLabel, setup.figure.labelShown label = true
  suppliedLabelsAreNotUnknown :
    setup.figure.labelMarkedUnknown .hotTemperature = false ∧
      setup.figure.labelMarkedUnknown .heatInput = false ∧
        setup.figure.labelMarkedUnknown .coldTemperature = false
  requestedLabelsAreUnknown :
    setup.figure.labelMarkedUnknown .workOutput = true ∧
      setup.figure.labelMarkedUnknown .efficiency = true ∧
        setup.figure.labelMarkedUnknown .rejectedHeat = true
  heatInputArrow :
    setup.figure.arrowStart .heatInput = .hotReservoir ∧
      setup.figure.arrowFinish .heatInput = .engine ∧
        setup.figure.arrowOrientation .heatInput = .downward
  rejectedHeatArrow :
    setup.figure.arrowStart .heatRejected = .engine ∧
      setup.figure.arrowFinish .heatRejected = .coldReservoir ∧
        setup.figure.arrowOrientation .heatRejected = .downward
  workOutputArrow :
    setup.figure.arrowStart .workOutput = .engine ∧
      setup.figure.arrowFinish .workOutput = .exterior ∧
        setup.figure.arrowOrientation .workOutput = .rightward

/-- Positivity and ordering conditions for a physically operating engine. -/
structure HasPhysicalCarnotEngineParameters
    (setup : CarnotHeatEngineSetup) : Prop where
  hotTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .hot)
  coldTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.reservoirTemperature .cold)
  coldTemperatureBelowHot :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.reservoirTemperature .cold) <
      temperatureInKelvins setup.temperatureStorageUnit
        (setup.reservoirTemperature .hot)
  absorbedHeatPositive :
    0 < energyInJoules setup.heatAbsorbedFromHotReservoir
  rejectedHeatNonnegative :
    0 ≤ energyInJoules setup.heatRejectedToColdReservoir
  netWorkOutputNonnegative :
    0 ≤ energyInJoules setup.netWorkOutput
  efficiencyInPhysicalRange :
    0 ≤ setup.thermalEfficiency ∧ setup.thermalEfficiency < 1

/-!
Governing relations for one complete reversible Carnot cycle.  Heat magnitudes
are positive: the first law gives `W = Q_H - Q_C`, efficiency is `W / Q_H`,
and reversibility gives `Q_C / Q_H = T_C / T_H`.  None of these fields fixes
the requested numerical efficiency.
-/
structure SatisfiesCarnotHeatEngineLaws
    (setup : CarnotHeatEngineSetup) : Prop where
  cycleEnergyBalance :
    energyInJoules setup.netWorkOutput =
      energyInJoules setup.heatAbsorbedFromHotReservoir -
        energyInJoules setup.heatRejectedToColdReservoir
  thermalEfficiencyDefinition :
    setup.thermalEfficiency =
      energyInJoules setup.netWorkOutput /
        energyInJoules setup.heatAbsorbedFromHotReservoir
  reversibleHeatTemperatureRatio :
    energyInJoules setup.heatRejectedToColdReservoir /
        energyInJoules setup.heatAbsorbedFromHotReservoir =
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.reservoirTemperature .cold) /
        temperatureInKelvins setup.temperatureStorageUnit
          (setup.reservoirTemperature .hot)

/-! ## Derived transfers and the displayed answer -/

/-- The reversible heat ratio determines `1400 J` of rejected heat. -/
lemma rejectedHeat_inJoules_eq_1400
    (setup : CarnotHeatEngineSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryHeatEngineFigure setup)
    (_physical : HasPhysicalCarnotEngineParameters setup)
    (_laws : SatisfiesCarnotHeatEngineLaws setup) :
    energyInJoules setup.heatRejectedToColdReservoir = 1400 := by
  have heatRatio := _laws.reversibleHeatTemperatureRatio
  rw [_figure.absorbedHeatJoules,
    _figure.coldReservoirTemperatureKelvins,
    _figure.hotReservoirTemperatureKelvins] at heatRatio
  norm_num at heatRatio ⊢
  linarith

/-- The first law then determines `600 J` of net work output. -/
lemma netWorkOutput_inJoules_eq_600
    (setup : CarnotHeatEngineSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryHeatEngineFigure setup)
    (_physical : HasPhysicalCarnotEngineParameters setup)
    (_laws : SatisfiesCarnotHeatEngineLaws setup) :
    energyInJoules setup.netWorkOutput = 600 := by
  rw [_laws.cycleEnergyBalance, _figure.absorbedHeatJoules,
    rejectedHeat_inJoules_eq_1400 setup _problem _figure _physical _laws]
  norm_num

/-- Labels attached to the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Efficiency percentage printed beside each answer label. -/
def AnswerChoice.efficiencyPercent : AnswerChoice → ℝ
  | .A => 36
  | .B => 30
  | .C => 28
  | .D => 45

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The Carnot efficiency is `1 - 350 / 500 = 3 / 10`, hence `30%`, the value
printed for answer choice B.

Blueprint label: `thm:physics:phyx_mini_0474:target`.
-/
theorem carnotEfficiency_eq_recordedAnswerB
    (setup : CarnotHeatEngineSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryHeatEngineFigure setup)
    (_physical : HasPhysicalCarnotEngineParameters setup)
    (_laws : SatisfiesCarnotHeatEngineLaws setup) :
    setup.thermalEfficiency = (3 / 10 : ℝ) ∧
      100 * setup.thermalEfficiency =
        recordedAnswerChoice.efficiencyPercent ∧
      recordedAnswerChoice = .B := by
  have efficiencyValue := _laws.thermalEfficiencyDefinition
  rw [netWorkOutput_inJoules_eq_600 setup _problem _figure _physical _laws,
    _figure.absorbedHeatJoules] at efficiencyValue
  norm_num at efficiencyValue
  refine ⟨efficiencyValue, ?_, rfl⟩
  rw [efficiencyValue]
  norm_num [recordedAnswerChoice, AnswerChoice.efficiencyPercent]

end PhyXMiniProblems.ProblemPhyXMini0474
