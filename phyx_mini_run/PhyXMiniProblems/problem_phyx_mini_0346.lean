import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

/-!
# Heat-flow comparison for three ideal-gas processes

The same `0.300 mol` gas starts at `20.0 °C` and reaches one common final
temperature along three different paths.  The paths shown as bars `a`, `b`,
and `c` are, in an unknown order, one isobaric, one isochoric, and one
adiabatic process.  The chart reports heat transferred *into* the gas.

Absolute temperatures and heat transfers remain Physlib physical quantities.
The amount of gas and the molar thermodynamic constants are explicit scalar
readouts in mol and J/(mol K), respectively, because Physlib's unit system
does not currently provide an amount-of-substance dimension.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0346

/-! ## Units and chart labels -/

/-- Read a dimensionful energy in SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/--
Read an absolute `Temperature` in degrees Celsius, taking `Temperature.toReal`
as the absolute-kelvin readout used by the SI thermodynamic model.
-/
def temperatureInCelsius (temperature : Temperature) : ℝ :=
  temperature.toReal - 27315 / 100

/-- The three process labels printed on the horizontal axis of the chart. -/
inductive FigureProcess where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The three thermodynamic process types whose chart labels were lost. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  | adiabatic
  deriving DecidableEq, Repr

/--
The supplied bar chart.  `heatIntoGas` uses the sign convention from the
problem: positive values are heat transferred into the gas.  The remaining
fields retain the numerical scale printed on the vertical `Q (J)` axis.
-/
structure HeatFlowBarChart where
  heatIntoGas : FigureProcess → DimEnergy
  yAxisMinimumJoules : ℝ
  yAxisMaximumJoules : ℝ
  yAxisTickSpacingJoules : ℝ

/-! ## Physical setup -/

/--
The gas sample and its three runs.  A single `finalTemperature` field records
that every process ends at the same `T₂`.  The real-valued thermodynamic
constants are named SI readouts, not replacements for temperature or heat.
-/
structure IdealGasHeatExperiment where
  amountOfGasMoles : ℝ
  initialTemperature : Temperature
  finalTemperature : Temperature
  chart : HeatFlowBarChart
  processKind : FigureProcess → ProcessKind
  constantVolumeMolarHeatCapacityJoulesPerMoleKelvin : ℝ
  constantPressureMolarHeatCapacityJoulesPerMoleKelvin : ℝ
  idealGasConstantJoulesPerMoleKelvin : ℝ

/-- The common temperature change of all three runs, measured in kelvins. -/
def temperatureChangeInKelvins (setup : IdealGasHeatExperiment) : ℝ :=
  setup.finalTemperature.toReal - setup.initialTemperature.toReal

/-!
The prose setup, kept separate from both governing laws and chart readouts.
`Function.Bijective` says that labels `a`, `b`, and `c` represent exactly one
isobaric, one isochoric, and one adiabatic process without revealing which
label has which role.
-/
structure MatchesIdealGasProcessScenario
    (setup : IdealGasHeatExperiment) : Prop where
  amountOfGasIsPointThreeMoles :
    setup.amountOfGasMoles = 3 / 10
  initialTemperatureIsTwentyCelsius :
    temperatureInCelsius setup.initialTemperature = 20
  oneProcessOfEachKind :
    Function.Bijective setup.processKind

/--
Positivity assumptions for the physical ideal-gas branch, together with the
standard classroom SI readout `R = 8.31 J/(mol K)` used at the precision of
the chart and answer choices.
-/
structure HasPhysicalThermodynamicParameters
    (setup : IdealGasHeatExperiment) : Prop where
  gasAmountPositive :
    0 < setup.amountOfGasMoles
  constantVolumeMolarHeatCapacityPositive :
    0 < setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin
  constantPressureMolarHeatCapacityPositive :
    0 < setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin
  idealGasConstantPositive :
    0 < setup.idealGasConstantJoulesPerMoleKelvin
  idealGasConstantSIReadout :
    setup.idealGasConstantJoulesPerMoleKelvin = 831 / 100

/-!
The governing constant-heat-capacity ideal-gas relations.  The isochoric and
isobaric fields state `Q = n Cᵥ ΔT` and `Q = n Cₚ ΔT`; the adiabatic field
states `Q = 0`; and the final field is Mayer's ideal-gas relation
`Cₚ - Cᵥ = R`.  None specifies the value of the final temperature.
-/
structure ObeysIdealGasHeatLaws
    (setup : IdealGasHeatExperiment) : Prop where
  isochoricHeatLaw :
    ∀ process,
      setup.processKind process = .isochoric →
        energyInJoules (setup.chart.heatIntoGas process) =
          setup.amountOfGasMoles *
            setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin *
              temperatureChangeInKelvins setup
  isobaricHeatLaw :
    ∀ process,
      setup.processKind process = .isobaric →
        energyInJoules (setup.chart.heatIntoGas process) =
          setup.amountOfGasMoles *
            setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin *
              temperatureChangeInKelvins setup
  adiabaticHeatLaw :
    ∀ process,
      setup.processKind process = .adiabatic →
        energyInJoules (setup.chart.heatIntoGas process) = 0
  mayerRelation :
    setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin -
        setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin =
      setup.idealGasConstantJoulesPerMoleKelvin

/-!
Primary-image readouts.  Bars `b` and `c` meet the 30 J and 50 J grid lines.
The thin bar `a` is recorded faithfully as nonnegative and below 1 J rather
than silently treating a visually near-zero height as an exact measurement.
-/
structure MatchesHeatFlowFigure
    (setup : IdealGasHeatExperiment) : Prop where
  yAxisStartsAtZero :
    setup.chart.yAxisMinimumJoules = 0
  yAxisEndsAtSixty :
    setup.chart.yAxisMaximumJoules = 60
  yAxisTicksEveryTenJoules :
    setup.chart.yAxisTickSpacingJoules = 10
  processAHeatIsNonnegative :
    0 ≤ energyInJoules (setup.chart.heatIntoGas .a)
  processAHeatIsNearZero :
    energyInJoules (setup.chart.heatIntoGas .a) < 1
  processBHeatIsThirtyJoules :
    energyInJoules (setup.chart.heatIntoGas .b) = 30
  processCHeatIsFiftyJoules :
    energyInJoules (setup.chart.heatIntoGas .c) = 50

/-! ## Displayed answers and target -/

/-- The four multiple-choice labels in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Celsius value displayed beside each answer label. -/
def answerTemperatureCelsius : AnswerChoice → ℝ
  | .A => 28
  | .B => 20
  | .C => 10
  | .D => 25

/-- The dataset metadata records answer choice B. -/
def recordedAnswerChoice : AnswerChoice := .B

/--
A displayed answer is selected by strict proximity to the derived Celsius
readout.  This keeps the multiple-choice comparison independent of the
dataset's recorded answer label.
-/
def IsNearestAnswerChoice
    (actualTemperatureCelsius : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |actualTemperatureCelsius - answerTemperatureCelsius choice| <
        |actualTemperatureCelsius - answerTemperatureCelsius otherChoice|

/-!
The 30 J and 50 J bars must be the isochoric and isobaric runs, respectively:
the remaining near-zero bar is adiabatic, and `Cₚ > Cᵥ` fixes their order.
Subtracting their heat laws gives

`20 J = (0.300 mol) (8.31 J/(mol K)) (T₂ - T₁)`,

so the exact Celsius readout in this classroom-precision model is
`20 + 20000 / 2493 ≈ 28.0225`.  It is uniquely nearest displayed choice A.
The source's recorded choice B is retained above as metadata only.

This conclusion is not a field of the setup, scenario, physical-parameter,
governing-law, or chart-data structures.

Blueprint label: `thm:physics:phyx_mini_0346:target`.
-/
theorem finalTemperature_is_answerA
    (setup : IdealGasHeatExperiment)
    (_scenario : MatchesIdealGasProcessScenario setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : ObeysIdealGasHeatLaws setup)
    (_figure : MatchesHeatFlowFigure setup) :
    temperatureInCelsius setup.finalTemperature =
        20 + (20000 : ℝ) / 2493 ∧
      IsNearestAnswerChoice
        (temperatureInCelsius setup.finalTemperature) .A := by
  have hkind_cases (process : FigureProcess) :
      setup.processKind process = .isobaric ∨
        setup.processKind process = .isochoric ∨
          setup.processKind process = .adiabatic := by
    cases setup.processKind process <;> simp
  have hbc_kind_ne :
      setup.processKind .b ≠ setup.processKind .c := by
    intro hkind
    have hbc : FigureProcess.b = FigureProcess.c :=
      _scenario.oneProcessOfEachKind.1 hkind
    cases hbc
  have hb_not_adiabatic :
      setup.processKind .b ≠ .adiabatic := by
    intro hb
    have hzero := _laws.adiabaticHeatLaw .b hb
    rw [_figure.processBHeatIsThirtyJoules] at hzero
    norm_num at hzero
  have hc_not_adiabatic :
      setup.processKind .c ≠ .adiabatic := by
    intro hc
    have hzero := _laws.adiabaticHeatLaw .c hc
    rw [_figure.processCHeatIsFiftyJoules] at hzero
    norm_num at hzero
  have hb_isochoric :
      setup.processKind .b = .isochoric := by
    rcases hkind_cases .b with hb_isobaric | hb_isochoric | hb_adiabatic
    · have hc_isochoric : setup.processKind .c = .isochoric := by
        rcases hkind_cases .c with hc_isobaric | hc_isochoric | hc_adiabatic
        · exact False.elim (hbc_kind_ne (hb_isobaric.trans hc_isobaric.symm))
        · exact hc_isochoric
        · exact False.elim (hc_not_adiabatic hc_adiabatic)
      have hb_heat := _laws.isobaricHeatLaw .b hb_isobaric
      have hc_heat := _laws.isochoricHeatLaw .c hc_isochoric
      rw [_figure.processBHeatIsThirtyJoules,
        _scenario.amountOfGasIsPointThreeMoles] at hb_heat
      rw [_figure.processCHeatIsFiftyJoules,
        _scenario.amountOfGasIsPointThreeMoles] at hc_heat
      have hmayer := _laws.mayerRelation
      rw [_physical.idealGasConstantSIReadout] at hmayer
      have hcv_lt_cp :
          setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin <
            setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin := by
        nlinarith
      have hfactor_pos :
          0 <
            (3 / 10 : ℝ) *
              setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin :=
        mul_pos (by norm_num)
          _physical.constantPressureMolarHeatCapacityPositive
      have hproduct_pos :
          0 <
            (3 / 10 : ℝ) *
              setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin *
                temperatureChangeInKelvins setup := by
        nlinarith
      have hdelta_pos : 0 < temperatureChangeInKelvins setup := by
        rcases (mul_pos_iff.mp hproduct_pos) with hpositive | hnegative
        · exact hpositive.2
        · nlinarith [hfactor_pos, hnegative.1]
      have hscale_pos :
          0 < (3 / 10 : ℝ) * temperatureChangeInKelvins setup :=
        mul_pos (by norm_num) hdelta_pos
      have hheat_order :
          (3 / 10 : ℝ) * temperatureChangeInKelvins setup *
                setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin <
            (3 / 10 : ℝ) * temperatureChangeInKelvins setup *
                setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin :=
        mul_lt_mul_of_pos_left hcv_lt_cp hscale_pos
      nlinarith
    · exact hb_isochoric
    · exact False.elim (hb_not_adiabatic hb_adiabatic)
  have hc_isobaric :
      setup.processKind .c = .isobaric := by
    rcases hkind_cases .c with hc_isobaric | hc_isochoric | hc_adiabatic
    · exact hc_isobaric
    · exact False.elim (hbc_kind_ne (hb_isochoric.trans hc_isochoric.symm))
    · exact False.elim (hc_not_adiabatic hc_adiabatic)
  have hb_heat := _laws.isochoricHeatLaw .b hb_isochoric
  have hc_heat := _laws.isobaricHeatLaw .c hc_isobaric
  rw [_figure.processBHeatIsThirtyJoules,
    _scenario.amountOfGasIsPointThreeMoles] at hb_heat
  rw [_figure.processCHeatIsFiftyJoules,
    _scenario.amountOfGasIsPointThreeMoles] at hc_heat
  have hmayer := _laws.mayerRelation
  rw [_physical.idealGasConstantSIReadout] at hmayer
  have hheat_difference :
      (20 : ℝ) =
        (3 / 10) * (831 / 100) * temperatureChangeInKelvins setup := by
    calc
      (20 : ℝ) = 50 - 30 := by norm_num
      _ =
          (3 / 10) *
                setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin *
                temperatureChangeInKelvins setup -
            (3 / 10) *
                setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin *
                temperatureChangeInKelvins setup := by
          rw [← hc_heat, ← hb_heat]
      _ =
          (3 / 10) *
            (setup.constantPressureMolarHeatCapacityJoulesPerMoleKelvin -
              setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin) *
                temperatureChangeInKelvins setup := by ring
      _ = (3 / 10) * (831 / 100) * temperatureChangeInKelvins setup := by
          rw [hmayer]
  have hdelta :
      temperatureChangeInKelvins setup = (20000 : ℝ) / 2493 := by
    nlinarith
  have hinitial := _scenario.initialTemperatureIsTwentyCelsius
  have hfinal :
      temperatureInCelsius setup.finalTemperature =
        20 + (20000 : ℝ) / 2493 := by
    simp only [temperatureInCelsius] at hinitial ⊢
    simp only [temperatureChangeInKelvins] at hdelta
    linarith
  constructor
  · exact hfinal
  · rw [hfinal]
    intro otherChoice hother
    cases otherChoice with
    | A => exact False.elim (hother rfl)
    | B => norm_num [answerTemperatureCelsius]
    | C => norm_num [answerTemperatureCelsius]
    | D => norm_num [answerTemperatureCelsius]

end PhyXMiniProblems.ProblemPhyXMini0346
