import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0351

open Dimension

/-!
# Efficiency of a three-leg helium heat-engine cycle

The supplied `p`--`V` diagram shows the directed cycle `a -> b -> c -> a`.
The leg `a -> b` is vertical (constant volume), `b -> c` is the stated
isothermal expansion, and `c -> a` is horizontal (constant pressure).

Pressure, volume, heat, work, and internal energy are represented by
unit-independent Physlib quantities.  Real numbers occur only as explicit SI
readouts, the amount read in moles, and the dimensionless efficiency.  The
efficiency is an independent field constrained by the heat-engine law below;
it is not defined to equal an answer choice.  The stated pressures and the
standard monatomic ideal-gas laws imply an efficiency of about `20.6%`, so the
dataset's recorded `8.7%` answer is retained only as source metadata.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical volume, independent of the selected unit system. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a Physlib absolute temperature in kelvins for this SI model. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Cycle, gas, process, and figure vocabulary -/

/-- The three labelled thermodynamic states in the supplied figure. -/
inductive ThermodynamicState where
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs of the cycle. -/
inductive CycleLeg where
  | ab
  | bc
  | ca
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed cycle leg. -/
def legStart : CycleLeg → ThermodynamicState
  | .ab => .a
  | .bc => .b
  | .ca => .c

/-- Final state of each directed cycle leg. -/
def legFinish : CycleLeg → ThermodynamicState
  | .ab => .b
  | .bc => .c
  | .ca => .a

/-- Thermodynamic process types used in the problem. -/
inductive ThermodynamicProcessKind where
  | isochoric
  | isothermal
  | isobaric
  deriving DecidableEq, Repr

/-- The working-gas species stated in the problem. -/
inductive GasSpecies where
  | helium
  deriving DecidableEq, Repr

/-- Qualitative locations of state markers in the raster diagram. -/
inductive FigureStatePosition where
  | lowerLeft
  | upperLeft
  | lowerRight
  deriving DecidableEq, Repr

/-- Shapes of the three blue directed paths in the raster diagram. -/
inductive FigurePathShape where
  | vertical
  | curvedDownwardRight
  | horizontal
  deriving DecidableEq, Repr

/-- Literal labels, marker locations, and directed paths in the supplied image. -/
structure SuppliedPVCycleFigure where
  verticalAxisLabel : String
  horizontalAxisLabel : String
  originLabel : String
  stateLabel : ThermodynamicState → String
  statePosition : ThermodynamicState → FigureStatePosition
  arrowShown : CycleLeg → Bool
  arrowStart : CycleLeg → ThermodynamicState
  arrowFinish : CycleLeg → ThermodynamicState
  pathShape : CycleLeg → FigurePathShape

/-!
The physical heat engine.  Heat is positive into the gas and work is positive
when done by the gas.  Consequently both are signed `DimEnergy` quantities.
`molarGasConstantJoulesPerMoleKelvin` is an explicit coherent-SI readout, and
`thermalEfficiency` is dimensionless.
-/
structure HeliumHeatEngineCycle where
  workingGas : GasSpecies
  amountOfSubstanceMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  maximumTemperature : Temperature
  maximumTemperatureCelsiusReadout : ℝ
  processKind : CycleLeg → ThermodynamicProcessKind
  pressure : ThermodynamicState → DimPressure
  volume : ThermodynamicState → GasVolume
  temperature : ThermodynamicState → Temperature
  internalEnergy : ThermodynamicState → DimEnergy
  heatIntoGas : CycleLeg → DimEnergy
  workByGas : CycleLeg → DimEnergy
  cycleNetWork : DimEnergy
  cycleHeatInput : DimEnergy
  thermalEfficiency : ℝ
  suppliedFigure : SuppliedPVCycleFigure

/-! ## Scenario, readout, and figure assumptions -/

/-- The gas identity and the thermodynamic interpretation of the three legs. -/
structure MatchesHeatEngineScenario (setup : HeliumHeatEngineCycle) : Prop where
  gasIsHelium : setup.workingGas = .helium
  legABIsIsochoric : setup.processKind .ab = .isochoric
  legBCIsIsothermal : setup.processKind .bc = .isothermal
  legCAIsIsobaric : setup.processKind .ca = .isobaric

/-- The numerical information printed in the problem statement. -/
structure MatchesProblemReadouts (setup : HeliumHeatEngineCycle) : Prop where
  amountIsTwoMoles : setup.amountOfSubstanceMoles = 2
  maximumTemperatureIs327Celsius :
    setup.maximumTemperatureCelsiusReadout = 327
  celsiusToKelvinCalibration :
    temperatureInKelvins setup.maximumTemperature =
      setup.maximumTemperatureCelsiusReadout + 273.15
  maximumTemperatureAttainedAtLabelledState :
    ∃ state, setup.temperature state = setup.maximumTemperature
  labelledTemperaturesDoNotExceedMaximum :
    ∀ state,
      temperatureInKelvins (setup.temperature state) ≤
        temperatureInKelvins setup.maximumTemperature
  pressureAtAIsOneHundredKilopascals :
    pressureInPascals (setup.pressure .a) = 100000
  pressureAtCIsOneHundredKilopascals :
    pressureInPascals (setup.pressure .c) = 100000
  pressureAtBIsThreeHundredKilopascals :
    pressureInPascals (setup.pressure .b) = 300000

/-- Positivity assumptions selecting the physical branch of the model. -/
structure HasPhysicalHeatEngineParameters
    (setup : HeliumHeatEngineCycle) : Prop where
  amountPositive : 0 < setup.amountOfSubstanceMoles
  molarGasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.pressure state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.volume state)
  temperaturePositive :
    ∀ state, 0 < temperatureInKelvins (setup.temperature state)
  heatInputPositive : 0 < energyInJoules setup.cycleHeatInput

/-- Data transcribed directly from the primary `p`--`V` raster image. -/
structure MatchesSuppliedPVCycleFigure
    (setup : HeliumHeatEngineCycle) : Prop where
  verticalAxisIsPressure : setup.suppliedFigure.verticalAxisLabel = "p"
  horizontalAxisIsVolume : setup.suppliedFigure.horizontalAxisLabel = "V"
  originIsLabelledO : setup.suppliedFigure.originLabel = "O"
  stateLabels :
    setup.suppliedFigure.stateLabel .a = "a" ∧
    setup.suppliedFigure.stateLabel .b = "b" ∧
    setup.suppliedFigure.stateLabel .c = "c"
  statePositions :
    setup.suppliedFigure.statePosition .a = .lowerLeft ∧
    setup.suppliedFigure.statePosition .b = .upperLeft ∧
    setup.suppliedFigure.statePosition .c = .lowerRight
  everyArrowShown :
    ∀ leg, setup.suppliedFigure.arrowShown leg = true
  directedCycle :
    ∀ leg,
      setup.suppliedFigure.arrowStart leg = legStart leg ∧
      setup.suppliedFigure.arrowFinish leg = legFinish leg
  pathShapes :
    setup.suppliedFigure.pathShape .ab = .vertical ∧
    setup.suppliedFigure.pathShape .bc = .curvedDownwardRight ∧
    setup.suppliedFigure.pathShape .ca = .horizontal

/-! ## Governing thermodynamic laws -/

/-!
The governing laws are independent of the requested numerical efficiency:

* `P V = n R T` at every state, in coherent SI readouts;
* `U = (3/2) n R T` for monatomic helium;
* the first law `Delta U = Q - W` on every directed leg;
* zero isochoric work, logarithmic isothermal work, and `P Delta V`
  isobaric work;
* cycle work and positive-heat-input bookkeeping; and
* the definition `eta = W_net / Q_in` of heat-engine efficiency.
-/
structure SatisfiesIdealMonatomicGasCycleLaws
    (setup : HeliumHeatEngineCycle) : Prop where
  idealGasLaw :
    ∀ state,
      pressureInPascals (setup.pressure state) *
          volumeInCubicMeters (setup.volume state) =
        setup.amountOfSubstanceMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.temperature state)
  monatomicHeliumInternalEnergy :
    ∀ state,
      energyInJoules (setup.internalEnergy state) =
        (3 / 2 : ℝ) * setup.amountOfSubstanceMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.temperature state)
  firstLawOnEachLeg :
    ∀ leg,
      energyInJoules (setup.internalEnergy (legFinish leg)) -
          energyInJoules (setup.internalEnergy (legStart leg)) =
        energyInJoules (setup.heatIntoGas leg) -
          energyInJoules (setup.workByGas leg)
  isochoricAB : setup.volume .a = setup.volume .b
  isothermalBC : setup.temperature .b = setup.temperature .c
  isobaricCA : setup.pressure .c = setup.pressure .a
  isochoricABWork : energyInJoules (setup.workByGas .ab) = 0
  isothermalBCWork :
    energyInJoules (setup.workByGas .bc) =
      setup.amountOfSubstanceMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
        temperatureInKelvins (setup.temperature .b) *
        Real.log
          (volumeInCubicMeters (setup.volume .c) /
            volumeInCubicMeters (setup.volume .b))
  isobaricCAWork :
    energyInJoules (setup.workByGas .ca) =
      pressureInPascals (setup.pressure .a) *
        (volumeInCubicMeters (setup.volume .a) -
          volumeInCubicMeters (setup.volume .c))
  netWorkAccounting :
    energyInJoules setup.cycleNetWork =
      energyInJoules (setup.workByGas .ab) +
        energyInJoules (setup.workByGas .bc) +
        energyInJoules (setup.workByGas .ca)
  heatInputAccounting :
    energyInJoules setup.cycleHeatInput =
      max (energyInJoules (setup.heatIntoGas .ab)) 0 +
        max (energyInJoules (setup.heatIntoGas .bc)) 0 +
        max (energyInJoules (setup.heatIntoGas .ca)) 0
  efficiencyLaw :
    setup.thermalEfficiency =
      energyInJoules setup.cycleNetWork /
        energyInJoules setup.cycleHeatInput

/-! ## Displayed answers and formal targets -/

/-- The answer letters shown in the multiple-choice problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed efficiencies, read as percentages. -/
def answerEfficiencyPercent : AnswerChoice → ℝ
  | .A => 10
  | .B => 8.7
  | .C => 15.9
  | .D => 12.3

/-- The answer label recorded by the source dataset; it is never a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement after rounding an efficiency to the nearest tenth of a percent. -/
def EfficiencyRoundsToPercent
    (setup : HeliumHeatEngineCycle) (percentage : ℝ) : Prop :=
  round (1000 * setup.thermalEfficiency) =
    round (10 * percentage)

/-- Agreement with the percentage printed beside an answer choice. -/
def EfficiencyRoundsToChoice
    (setup : HeliumHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  EfficiencyRoundsToPercent setup (answerEfficiencyPercent choice)

/-!
For the standard monatomic ideal-gas interpretation of the depicted cycle,
the exact efficiency is

`(3 * log 3 - 2) / (3 + 3 * log 3)`.

It is about `0.205824`, hence rounds to `20.6%`.  None of the four printed
choices has that rounded percentage; in particular, the dataset's recorded
choice B (`8.7%`) is inconsistent with the stated pressures, figure, and
standard governing laws.  These conclusions occur only in this target.

Blueprint label: `thm:physics:phyx_mini_0351:target`.
-/
theorem problem_phyx_mini_0351
    (setup : HeliumHeatEngineCycle)
    (_physical : HasPhysicalHeatEngineParameters setup)
    (_scenario : MatchesHeatEngineScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedPVCycleFigure setup)
    (_laws : SatisfiesIdealMonatomicGasCycleLaws setup) :
    setup.thermalEfficiency =
        (3 * Real.log 3 - 2) / (3 + 3 * Real.log 3) ∧
      EfficiencyRoundsToPercent setup (103 / 5) ∧
      ∀ choice : AnswerChoice, ¬ EfficiencyRoundsToChoice setup choice := by
  have hvb_pos : 0 < volumeInCubicMeters (setup.volume .b) :=
    _physical.volumePositive .b
  have hlog_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htarget_den_pos : 0 < 3 + 3 * Real.log 3 := by
    positivity
  have hround_exact :
      round (1000 * ((3 * Real.log 3 - 2) / (3 + 3 * Real.log 3))) = 206 := by
    rw [round_eq]
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num only [Int.cast_ofNat]
      rw [show
          1000 * ((3 * Real.log 3 - 2) / (3 + 3 * Real.log 3)) + 1 / 2 =
            (1000 * (3 * Real.log 3 - 2) +
                (1 / 2) * (3 + 3 * Real.log 3)) /
              (3 + 3 * Real.log 3) by
            field_simp]
      apply (le_div_iff₀ htarget_den_pos).2
      nlinarith [Real.log_three_gt_d9]
    · norm_num only [Int.cast_ofNat]
      rw [show
          1000 * ((3 * Real.log 3 - 2) / (3 + 3 * Real.log 3)) + 1 / 2 =
            (1000 * (3 * Real.log 3 - 2) +
                (1 / 2) * (3 + 3 * Real.log 3)) /
              (3 + 3 * Real.log 3) by
            field_simp]
      apply (div_lt_iff₀ htarget_den_pos).2
      nlinarith [Real.log_three_lt_d9]
  have hvol_ab :
      volumeInCubicMeters (setup.volume .a) =
        volumeInCubicMeters (setup.volume .b) :=
    congrArg volumeInCubicMeters _laws.isochoricAB
  have htemp_bc :
      temperatureInKelvins (setup.temperature .b) =
        temperatureInKelvins (setup.temperature .c) :=
    congrArg temperatureInKelvins _laws.isothermalBC
  have hgas_a := _laws.idealGasLaw .a
  have hgas_b := _laws.idealGasLaw .b
  have hgas_c := _laws.idealGasLaw .c
  rw [_data.pressureAtAIsOneHundredKilopascals, hvol_ab] at hgas_a
  rw [_data.pressureAtBIsThreeHundredKilopascals] at hgas_b
  rw [_data.pressureAtCIsOneHundredKilopascals, ← htemp_bc] at hgas_c
  have hvol_cb :
      volumeInCubicMeters (setup.volume .c) =
        3 * volumeInCubicMeters (setup.volume .b) := by
    nlinarith [hgas_b, hgas_c]
  have hvolume_ratio :
      volumeInCubicMeters (setup.volume .c) /
          volumeInCubicMeters (setup.volume .b) = 3 := by
    rw [hvol_cb]
    field_simp [ne_of_gt hvb_pos]
  have hu_a := _laws.monatomicHeliumInternalEnergy .a
  have hu_b := _laws.monatomicHeliumInternalEnergy .b
  have hu_c := _laws.monatomicHeliumInternalEnergy .c
  rw [← htemp_bc] at hu_c
  have hu_a' :
      energyInJoules (setup.internalEnergy .a) =
        150000 * volumeInCubicMeters (setup.volume .b) := by
    nlinarith [hu_a, hgas_a]
  have hu_b' :
      energyInJoules (setup.internalEnergy .b) =
        450000 * volumeInCubicMeters (setup.volume .b) := by
    nlinarith [hu_b, hgas_b]
  have hu_c' :
      energyInJoules (setup.internalEnergy .c) =
        450000 * volumeInCubicMeters (setup.volume .b) := by
    nlinarith [hu_c, hgas_b]
  have hw_ab : energyInJoules (setup.workByGas .ab) = 0 :=
    _laws.isochoricABWork
  have hw_bc :
      energyInJoules (setup.workByGas .bc) =
        300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 := by
    calc
      energyInJoules (setup.workByGas .bc) =
          setup.amountOfSubstanceMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
            temperatureInKelvins (setup.temperature .b) *
            Real.log
              (volumeInCubicMeters (setup.volume .c) /
                volumeInCubicMeters (setup.volume .b)) := _laws.isothermalBCWork
      _ = 300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 := by
        rw [hvolume_ratio, ← hgas_b]
  have hw_ca_raw := _laws.isobaricCAWork
  rw [_data.pressureAtAIsOneHundredKilopascals, hvol_ab, hvol_cb] at hw_ca_raw
  have hw_ca :
      energyInJoules (setup.workByGas .ca) =
        -200000 * volumeInCubicMeters (setup.volume .b) := by
    nlinarith [hw_ca_raw]
  have hfirst_ab :
      energyInJoules (setup.internalEnergy .b) -
          energyInJoules (setup.internalEnergy .a) =
        energyInJoules (setup.heatIntoGas .ab) -
          energyInJoules (setup.workByGas .ab) := by
    simpa [legFinish, legStart] using _laws.firstLawOnEachLeg .ab
  have hfirst_bc :
      energyInJoules (setup.internalEnergy .c) -
          energyInJoules (setup.internalEnergy .b) =
        energyInJoules (setup.heatIntoGas .bc) -
          energyInJoules (setup.workByGas .bc) := by
    simpa [legFinish, legStart] using _laws.firstLawOnEachLeg .bc
  have hfirst_ca :
      energyInJoules (setup.internalEnergy .a) -
          energyInJoules (setup.internalEnergy .c) =
        energyInJoules (setup.heatIntoGas .ca) -
          energyInJoules (setup.workByGas .ca) := by
    simpa [legFinish, legStart] using _laws.firstLawOnEachLeg .ca
  have hq_ab :
      energyInJoules (setup.heatIntoGas .ab) =
        300000 * volumeInCubicMeters (setup.volume .b) := by
    nlinarith [hfirst_ab, hu_a', hu_b', hw_ab]
  have hq_bc :
      energyInJoules (setup.heatIntoGas .bc) =
        300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 := by
    linarith [hfirst_bc, hu_b', hu_c', hw_bc]
  have hq_ca :
      energyInJoules (setup.heatIntoGas .ca) =
        -500000 * volumeInCubicMeters (setup.volume .b) := by
    linarith [hfirst_ca, hu_a', hu_c', hw_ca]
  have hq_ab_nonneg :
      0 ≤ 300000 * volumeInCubicMeters (setup.volume .b) := by
    positivity
  have hq_bc_nonneg :
      0 ≤ 300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 := by
    positivity
  have hq_ca_nonpos :
      -500000 * volumeInCubicMeters (setup.volume .b) ≤ 0 := by
    nlinarith [hvb_pos]
  have hnet :
      energyInJoules setup.cycleNetWork =
        300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 -
          200000 * volumeInCubicMeters (setup.volume .b) := by
    rw [_laws.netWorkAccounting, hw_ab, hw_bc, hw_ca]
    ring
  have hqin :
      energyInJoules setup.cycleHeatInput =
        300000 * volumeInCubicMeters (setup.volume .b) +
          300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 := by
    rw [_laws.heatInputAccounting, hq_ab, hq_bc, hq_ca,
      max_eq_left hq_ab_nonneg, max_eq_left hq_bc_nonneg,
      max_eq_right hq_ca_nonpos]
    ring
  have hqin_expr_pos :
      0 < 300000 * volumeInCubicMeters (setup.volume .b) +
        300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 := by
    positivity
  have hefficiency :
      setup.thermalEfficiency =
        (3 * Real.log 3 - 2) / (3 + 3 * Real.log 3) := by
    calc
      setup.thermalEfficiency =
          energyInJoules setup.cycleNetWork /
            energyInJoules setup.cycleHeatInput := _laws.efficiencyLaw
      _ = (300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3 -
            200000 * volumeInCubicMeters (setup.volume .b)) /
          (300000 * volumeInCubicMeters (setup.volume .b) +
            300000 * volumeInCubicMeters (setup.volume .b) * Real.log 3) := by
        rw [hnet, hqin]
      _ = (3 * Real.log 3 - 2) / (3 + 3 * Real.log 3) := by
        field_simp [ne_of_gt hvb_pos, ne_of_gt hqin_expr_pos,
          ne_of_gt htarget_den_pos]
        ring
  refine ⟨hefficiency, ?_, ?_⟩
  · unfold EfficiencyRoundsToPercent
    rw [hefficiency, hround_exact]
    norm_num [round_eq]
  · intro choice
    unfold EfficiencyRoundsToChoice EfficiencyRoundsToPercent
    rw [hefficiency, hround_exact]
    cases choice <;> norm_num [answerEfficiencyPercent, round_eq]

end PhyXMiniProblems.ProblemPhyXMini0351
