import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/-!
# Thermal efficiency of a three-leg ideal-gas cycle

The primary figure shows the directed cycle `a → b → c → a`.  The leg
`a → b` is adiabatic, `b → c` is horizontal (isobaric), and `c → a` is
vertical (isochoric).  The figure gives

* `Vₐ = V꜀ = 0.0020 m³`,
* `Vᵦ = 0.0090 m³`, and
* `pᵦ = p꜀ = 1.5 atm`.

The gas amount is `0.250 mol` and its heat-capacity ratio is `γ = 1.40`.
Dimensionful pressure, volume, and energy objects are retained below.  Real
numbers are used only for explicitly named coherent-SI/unit readouts,
dimensionless ratios, and the displayed multiple-choice percentages.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0347

open Dimension

/-! ## Dimensionful quantities and readouts -/

/-- A physical gas volume, carrying the length-cubed dimension. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- The coherent-SI pressure readout, in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- The pressure readout as a dimensionless multiple of one standard atmosphere. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- The coherent-SI volume readout, in cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-- The coherent-SI energy readout, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- The cycle uses the underlying absolute-temperature readout in kelvin. -/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Figure labels and the thermodynamic model -/

/-- The three equilibrium states labelled in the pressure-volume diagram. -/
inductive StateLabel where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The process types explicitly specified by the text and the diagram. -/
inductive ProcessKind where
  | adiabatic
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- Pressure, volume, and absolute temperature at one equilibrium state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : GasVolume
  temperature : Temperature

/--
A directed quasistatic leg.  Heat transferred to the gas and work done by the
gas use the convention that positive values enter the first-law identity
`Q = ΔU + W`.
-/
structure ThermodynamicProcess where
  initialState : StateLabel
  finalState : StateLabel
  kind : ProcessKind
  heatTransferredToGas : DimEnergy
  workDoneByGas : DimEnergy

/--
The ideal-gas engine cycle.  The amount, gas constant, and molar heat capacity
fields are explicitly named scalar readouts in mol, J/(mol K), and J/(mol K),
respectively; `thermalEfficiency` is dimensionless.
-/
structure IdealGasHeatEngineCycle where
  amountOfGasMoles : ℝ
  heatCapacityRatio : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin : ℝ
  state : StateLabel → ThermodynamicState
  ab : ThermodynamicProcess
  bc : ThermodynamicProcess
  ca : ThermodynamicProcess
  thermalEfficiency : ℝ

/--
The first law for one leg, with the ideal-gas internal-energy change
`ΔU = n Cᵥ (T_final - T_initial)`.
-/
def ObeysFirstLaw
    (cycle : IdealGasHeatEngineCycle)
    (process : ThermodynamicProcess) : Prop :=
  energyInJoules process.heatTransferredToGas =
    cycle.amountOfGasMoles *
        cycle.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
        (temperatureInKelvin (cycle.state process.finalState).temperature -
          temperatureInKelvin (cycle.state process.initialState).temperature) +
      energyInJoules process.workDoneByGas

/-! ## Assumptions: physical branch, governing laws, and figure data -/

/-- Positivity and heat-flow conditions selecting the heat-engine branch. -/
structure HasPhysicalHeatEngineParameters
    (cycle : IdealGasHeatEngineCycle) : Prop where
  amountPositive : 0 < cycle.amountOfGasMoles
  heatCapacityRatioGreaterThanOne : 1 < cycle.heatCapacityRatio
  gasConstantPositive :
    0 < cycle.molarGasConstantJoulesPerMoleKelvin
  heatCapacityAtConstantVolumePositive :
    0 < cycle.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin
  pressurePositive :
    ∀ label : StateLabel,
      0 < pressureInPascals (cycle.state label).pressure
  volumePositive :
    ∀ label : StateLabel,
      0 < volumeInCubicMeters (cycle.state label).volume
  temperaturePositive :
    ∀ label : StateLabel,
      0 < temperatureInKelvin (cycle.state label).temperature
  heatEntersOnCA : 0 < energyInJoules cycle.ca.heatTransferredToGas
  heatLeavesOnBC : energyInJoules cycle.bc.heatTransferredToGas < 0

/--
Governing thermodynamic laws for this ideal-gas cycle.  These fields state
general physical relations; none mentions a numerical answer choice.
-/
structure SatisfiesIdealGasHeatEngineLaws
    (cycle : IdealGasHeatEngineCycle) : Prop where
  idealGasLaw :
    ∀ label : StateLabel,
      pressureInPascals (cycle.state label).pressure *
          volumeInCubicMeters (cycle.state label).volume =
        cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvin (cycle.state label).temperature
  heatCapacityRelation :
    cycle.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
        (cycle.heatCapacityRatio - 1) =
      cycle.molarGasConstantJoulesPerMoleKelvin
  firstLawAB : ObeysFirstLaw cycle cycle.ab
  firstLawBC : ObeysFirstLaw cycle cycle.bc
  firstLawCA : ObeysFirstLaw cycle cycle.ca
  adiabaticPressureVolumeRelation :
    pressureInPascals (cycle.state .a).pressure /
        pressureInPascals (cycle.state .b).pressure =
      Real.rpow
        (volumeInCubicMeters (cycle.state .b).volume /
          volumeInCubicMeters (cycle.state .a).volume)
        cycle.heatCapacityRatio
  adiabaticNoHeatAB :
    energyInJoules cycle.ab.heatTransferredToGas = 0
  isobaricPressureBC :
    (cycle.state .b).pressure = (cycle.state .c).pressure
  isobaricWorkBC :
    energyInJoules cycle.bc.workDoneByGas =
      pressureInPascals (cycle.state .b).pressure *
        (volumeInCubicMeters (cycle.state .c).volume -
          volumeInCubicMeters (cycle.state .b).volume)
  isochoricVolumeCA :
    (cycle.state .c).volume = (cycle.state .a).volume
  isochoricWorkCA :
    energyInJoules cycle.ca.workDoneByGas = 0
  thermalEfficiencyDefinition :
    cycle.thermalEfficiency =
      (energyInJoules cycle.ab.workDoneByGas +
          energyInJoules cycle.bc.workDoneByGas +
          energyInJoules cycle.ca.workDoneByGas) /
        energyInJoules cycle.ca.heatTransferredToGas

/--
The textual parameters and primary-figure readouts.  The equalities for the
three processes also record the arrow directions `a → b → c → a`.
-/
structure HasHeatEngineFigureData
    (cycle : IdealGasHeatEngineCycle) : Prop where
  amountOfGasIsQuarterMole :
    cycle.amountOfGasMoles = (1 : ℝ) / 4
  heatCapacityRatioIsOnePointFour :
    cycle.heatCapacityRatio = (7 : ℝ) / 5
  abInitial : cycle.ab.initialState = .a
  abFinal : cycle.ab.finalState = .b
  abKind : cycle.ab.kind = .adiabatic
  bcInitial : cycle.bc.initialState = .b
  bcFinal : cycle.bc.finalState = .c
  bcKind : cycle.bc.kind = .isobaric
  caInitial : cycle.ca.initialState = .c
  caFinal : cycle.ca.finalState = .a
  caKind : cycle.ca.kind = .isochoric
  volumeAInCubicMeters :
    volumeInCubicMeters (cycle.state .a).volume = (2 : ℝ) / 1000
  volumeBInCubicMeters :
    volumeInCubicMeters (cycle.state .b).volume = (9 : ℝ) / 1000
  volumeCInCubicMeters :
    volumeInCubicMeters (cycle.state .c).volume = (2 : ℝ) / 1000
  pressureBInAtmospheres :
    pressureInAtmospheres (cycle.state .b).pressure = (3 : ℝ) / 2
  pressureCInAtmospheres :
    pressureInAtmospheres (cycle.state .c).pressure = (3 : ℝ) / 2

/-! ## Previous-part result and multiple-choice target -/

/--
The pressure at `a` furnished by the adiabatic `p V^γ` relation (part (a) of
the source problem), expressed in atmospheres.  It is a derived conclusion,
not a figure-data or governing-law premise.
-/
theorem pressureAtA_from_adiabatic
    (cycle : IdealGasHeatEngineCycle)
    (_physical : HasPhysicalHeatEngineParameters cycle)
    (_laws : SatisfiesIdealGasHeatEngineLaws cycle)
    (_data : HasHeatEngineFigureData cycle) :
    pressureInAtmospheres (cycle.state .a).pressure =
      (3 : ℝ) / 2 *
        Real.rpow (((9 : ℝ) / 1000) / ((2 : ℝ) / 1000)) ((7 : ℝ) / 5) := by
  have hAdiabatic := _laws.adiabaticPressureVolumeRelation
  rw [_data.volumeBInCubicMeters, _data.volumeAInCubicMeters,
    _data.heatCapacityRatioIsOnePointFour] at hAdiabatic
  have hPressureB := _data.pressureBInAtmospheres
  have hPressureB_ne :
      pressureInPascals (cycle.state .b).pressure ≠ 0 :=
    ne_of_gt (_physical.pressurePositive .b)
  have hAtmosphere_ne :
      pressureInPascals DimPressure.standardAtmosphere ≠ 0 := by
    intro h
    norm_num [pressureInAtmospheres, h] at hPressureB
  unfold pressureInAtmospheres
  calc
    pressureInPascals (cycle.state .a).pressure /
          pressureInPascals DimPressure.standardAtmosphere =
        (pressureInPascals (cycle.state .a).pressure /
            pressureInPascals (cycle.state .b).pressure) *
          (pressureInPascals (cycle.state .b).pressure /
            pressureInPascals DimPressure.standardAtmosphere) := by
              field_simp
    _ = Real.rpow (((9 : ℝ) / 1000) / ((2 : ℝ) / 1000)) ((7 : ℝ) / 5) *
          ((3 : ℝ) / 2) := by
            rw [hAdiabatic]
            exact congrArg
              (fun x =>
                Real.rpow (((9 : ℝ) / 1000) / ((2 : ℝ) / 1000)) ((7 : ℝ) / 5) * x)
              hPressureB
    _ = (3 : ℝ) / 2 *
          Real.rpow (((9 : ℝ) / 1000) / ((2 : ℝ) / 1000)) ((7 : ℝ) / 5) := by
            ring

/-- The four efficiencies displayed in the source, represented as fractions. -/
inductive EfficiencyChoice where
  | choiceA
  | choiceB
  | choiceC
  | choiceD
  deriving DecidableEq, Repr

/-- Numerical value of a displayed efficiency choice: 30%, 31.9%, 35.9%, or 32.3%. -/
def efficiencyChoiceFraction : EfficiencyChoice → ℝ
  | .choiceA => 30 / 100
  | .choiceB => 319 / 1000
  | .choiceC => 359 / 1000
  | .choiceD => 323 / 1000

/-- A displayed choice is closest to the calculated dimensionless efficiency. -/
def IsClosestEfficiencyChoice
    (efficiency : ℝ) (answer : EfficiencyChoice) : Prop :=
  ∀ candidate : EfficiencyChoice,
    abs (efficiency - efficiencyChoiceFraction answer) ≤
      abs (efficiency - efficiencyChoiceFraction candidate)

/--
The thermal efficiency selects answer choice B, namely the displayed 31.9%.
Because the diagram data and answer options are decimal readouts, the target
states the multiple-choice comparison rather than falsely identifying the
exact `Real.rpow` result with a rounded decimal.

Blueprint label: `thm:physics:phyx_mini_0347:target`.
-/
theorem thermalEfficiency_choiceB
    (cycle : IdealGasHeatEngineCycle)
    (_physical : HasPhysicalHeatEngineParameters cycle)
    (_laws : SatisfiesIdealGasHeatEngineLaws cycle)
    (_data : HasHeatEngineFigureData cycle) :
    IsClosestEfficiencyChoice cycle.thermalEfficiency .choiceB := by
  have hHeatCapacity := _laws.heatCapacityRelation
  rw [_data.heatCapacityRatioIsOnePointFour] at hHeatCapacity
  have hGasConstant :
      cycle.molarGasConstantJoulesPerMoleKelvin =
        (2 / 5 : ℝ) *
          cycle.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin := by
    linarith

  have hIdealA := _laws.idealGasLaw .a
  have hIdealB := _laws.idealGasLaw .b
  have hIdealC := _laws.idealGasLaw .c
  rw [_data.volumeAInCubicMeters, _data.amountOfGasIsQuarterMole,
    hGasConstant] at hIdealA
  rw [_data.volumeBInCubicMeters, _data.amountOfGasIsQuarterMole,
    hGasConstant] at hIdealB
  rw [_data.volumeCInCubicMeters, _data.amountOfGasIsQuarterMole,
    hGasConstant, ← _laws.isobaricPressureBC] at hIdealC

  have hCvTa :
      cycle.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
          temperatureInKelvin (cycle.state .a).temperature =
        pressureInPascals (cycle.state .a).pressure / 50 := by
    nlinarith [hIdealA]
  have hCvTb :
      cycle.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
          temperatureInKelvin (cycle.state .b).temperature =
        9 * pressureInPascals (cycle.state .b).pressure / 100 := by
    nlinarith [hIdealB]
  have hCvTc :
      cycle.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
          temperatureInKelvin (cycle.state .c).temperature =
        pressureInPascals (cycle.state .b).pressure / 50 := by
    nlinarith [hIdealC]

  have hFirstLawAB := _laws.firstLawAB
  unfold ObeysFirstLaw at hFirstLawAB
  rw [_data.abFinal, _data.abInitial, _data.amountOfGasIsQuarterMole,
    _laws.adiabaticNoHeatAB] at hFirstLawAB
  have hWorkAB :
      energyInJoules cycle.ab.workDoneByGas =
        pressureInPascals (cycle.state .a).pressure / 200 -
          9 * pressureInPascals (cycle.state .b).pressure / 400 := by
    nlinarith [hCvTa, hCvTb]

  have hFirstLawCA := _laws.firstLawCA
  unfold ObeysFirstLaw at hFirstLawCA
  rw [_data.caFinal, _data.caInitial, _data.amountOfGasIsQuarterMole,
    _laws.isochoricWorkCA] at hFirstLawCA
  have hHeatCA :
      energyInJoules cycle.ca.heatTransferredToGas =
        (pressureInPascals (cycle.state .a).pressure -
          pressureInPascals (cycle.state .b).pressure) / 200 := by
    nlinarith [hCvTa, hCvTc]

  have hWorkBC := _laws.isobaricWorkBC
  rw [_data.volumeCInCubicMeters, _data.volumeBInCubicMeters] at hWorkBC

  have hAdiabatic := _laws.adiabaticPressureVolumeRelation
  rw [_data.volumeBInCubicMeters, _data.volumeAInCubicMeters,
    _data.heatCapacityRatioIsOnePointFour] at hAdiabatic

  have hPressureB_pos :
      0 < pressureInPascals (cycle.state .b).pressure :=
    _physical.pressurePositive .b
  have hPressureA_gt_pressureB :
      pressureInPascals (cycle.state .b).pressure <
        pressureInPascals (cycle.state .a).pressure := by
    have hRpow_gt_one :
        1 <
          Real.rpow (((9 : ℝ) / 1000) / ((2 : ℝ) / 1000))
            ((7 : ℝ) / 5) := by
      apply Real.one_lt_rpow
      · norm_num
      · norm_num
    have hPressureRatio_gt_one :
        1 <
          pressureInPascals (cycle.state .a).pressure /
            pressureInPascals (cycle.state .b).pressure := by
      rw [hAdiabatic]
      exact hRpow_gt_one
    simpa using (lt_div_iff₀ hPressureB_pos).mp hPressureRatio_gt_one
  have hHeatCA_pos :
      0 < energyInJoules cycle.ca.heatTransferredToGas := by
    exact _physical.heatEntersOnCA

  have hEfficiency :
      cycle.thermalEfficiency =
        (10 *
              (pressureInPascals (cycle.state .a).pressure /
                pressureInPascals (cycle.state .b).pressure) -
            59) /
          (10 *
            (pressureInPascals (cycle.state .a).pressure /
                pressureInPascals (cycle.state .b).pressure -
              1)) := by
    rw [_laws.thermalEfficiencyDefinition, hWorkAB, hWorkBC,
      _laws.isochoricWorkCA, hHeatCA]
    field_simp [ne_of_gt hPressureB_pos,
      ne_of_gt (sub_pos.mpr hPressureA_gt_pressureB)]; ring

  rw [hEfficiency, hAdiabatic]
  have hSimplify :
      Real.rpow (((9 : ℝ) / 1000) / ((2 : ℝ) / 1000)) ((7 : ℝ) / 5) =
        Real.rpow ((9 : ℝ) / 2) ((7 : ℝ) / 5) := by
    norm_num
  rw [hSimplify]
  have hBase : (0 : ℝ) ≤ 9 / 2 := by
    norm_num
  have hRpowFive :
      ((9 / 2 : ℝ) ^ (7 / 5 : ℝ)) ^ (5 : ℕ) =
        (9 / 2 : ℝ) ^ (7 : ℕ) := by
    rw [← Real.rpow_mul_natCast hBase ((7 : ℝ) / 5) 5]
    norm_num
  have hRpow_nonneg : 0 ≤ (9 / 2 : ℝ) ^ (7 / 5 : ℝ) :=
    Real.rpow_nonneg hBase _
  have hLower : (41 / 5 : ℝ) < (9 / 2 : ℝ) ^ (7 / 5 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 5 hRpow_nonneg
    rw [hRpowFive]
    norm_num
  have hUpper : (9 / 2 : ℝ) ^ (7 / 5 : ℝ) < (8213 / 1000 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 5
      (by norm_num : (0 : ℝ) ≤ 8213 / 1000)
    rw [hRpowFive]
    norm_num
  have hDenominator_pos :
      0 < 10 * ((9 / 2 : ℝ) ^ (7 / 5 : ℝ) - 1) := by
    nlinarith only [hLower]
  have hEtaLower :
      (319 / 1000 : ℝ) ≤
        (10 * (9 / 2 : ℝ) ^ (7 / 5 : ℝ) - 59) /
          (10 * ((9 / 2 : ℝ) ^ (7 / 5 : ℝ) - 1)) := by
    apply (le_div_iff₀ hDenominator_pos).2
    nlinarith only [hLower]
  have hEtaUpper :
      (10 * (9 / 2 : ℝ) ^ (7 / 5 : ℝ) - 59) /
          (10 * ((9 / 2 : ℝ) ^ (7 / 5 : ℝ) - 1)) ≤
        (321 / 1000 : ℝ) := by
    apply (div_le_iff₀ hDenominator_pos).2
    nlinarith only [hUpper]
  unfold IsClosestEfficiencyChoice
  intro candidate
  cases candidate with
  | choiceA =>
      norm_num [efficiencyChoiceFraction]
      rw [abs_of_nonneg (sub_nonneg.mpr hEtaLower)]
      rw [abs_of_nonneg (by linarith only [hEtaLower])]
      linarith only
  | choiceB =>
      rfl
  | choiceC =>
      norm_num [efficiencyChoiceFraction]
      rw [abs_of_nonneg (sub_nonneg.mpr hEtaLower)]
      rw [abs_of_nonpos (by linarith only [hEtaUpper])]
      linarith only [hEtaUpper]
  | choiceD =>
      norm_num [efficiencyChoiceFraction]
      rw [abs_of_nonneg (sub_nonneg.mpr hEtaLower)]
      rw [abs_of_nonpos (by linarith only [hEtaUpper])]
      linarith only [hEtaUpper]

end PhyXMiniProblems.ProblemPhyXMini0347
