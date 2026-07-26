import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0354

open Dimension

/-!
# Efficiency of a rectangular pressure--volume cycle

Four moles of argon pass around the rectangular cycle
`a -> b -> c -> d -> a`.  The vertical sides are isochoric and the horizontal
sides are isobaric.  Pressure, volume, temperature, energy, heat, and work are
represented as physical quantities; real numbers are used only for named-unit
readouts and dimensionless ratios.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Joule readout of a physical energy, heat transfer, or work. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/--
Kelvin readout of a Physlib absolute temperature stored in an explicitly
chosen zero-preserving temperature unit.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Figure labels and directed cycle -/

/-- The four black vertices labelled in the supplied pressure--volume plot. -/
inductive CycleState where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- The four directed blue sides of the plotted cycle. -/
inductive CycleLeg where
  | ab
  | bc
  | cd
  | da
  deriving DecidableEq, Fintype, Repr

/-- The thermodynamic constraint represented by a straight plot side. -/
inductive LegConstraint where
  | constantVolume
  | constantPressure
  deriving DecidableEq, Repr

/-- Text labels explicitly present in the primary image. -/
inductive DiagramLabel where
  | originO
  | pressureAxisP
  | volumeAxisV
  | stateA
  | stateB
  | stateC
  | stateD
  deriving DecidableEq, Fintype, Repr

/-- Source state of a directed cycle leg. -/
def legSource : CycleLeg → CycleState
  | .ab => .a
  | .bc => .b
  | .cd => .c
  | .da => .d

/-- Target state of a directed cycle leg. -/
def legTarget : CycleLeg → CycleState
  | .ab => .b
  | .bc => .c
  | .cd => .d
  | .da => .a

/-- Vertical sides are isochoric and horizontal sides are isobaric. -/
def displayedLegConstraint : CycleLeg → LegConstraint
  | .ab => .constantVolume
  | .bc => .constantPressure
  | .cd => .constantVolume
  | .da => .constantPressure

/-- Physical coordinates and qualitative marks in the supplied diagram. -/
structure PressureVolumeCycleFigure where
  volumeAt : CycleState → VolumeQuantity
  pressureAt : CycleState → DimPressure
  showsVertex : CycleState → Bool
  showsDirectedArrow : CycleLeg → Bool
  drawsLegStraight : CycleLeg → Bool
  legConstraint : CycleLeg → LegConstraint
  showsLabel : DiagramLabel → Bool

/--
Primary-image evidence for the four labelled vertices, directed arrows, and
equal-coordinate and ordering relations of the rectangular cycle.
-/
structure MatchesSuppliedRectangularCycle
    (figure : PressureVolumeCycleFigure) : Prop where
  everyVertexShown : ∀ state, figure.showsVertex state = true
  everyArrowShown : ∀ leg, figure.showsDirectedArrow leg = true
  everyLegStraight : ∀ leg, figure.drawsLegStraight leg = true
  everyLabelShown : ∀ label, figure.showsLabel label = true
  legConstraintsAgree :
    ∀ leg, figure.legConstraint leg = displayedLegConstraint leg
  leftSideConstantVolume :
    volumeInCubicMeters (figure.volumeAt .a) =
      volumeInCubicMeters (figure.volumeAt .b)
  topSideConstantPressure :
    pressureInPascals (figure.pressureAt .b) =
      pressureInPascals (figure.pressureAt .c)
  rightSideConstantVolume :
    volumeInCubicMeters (figure.volumeAt .c) =
      volumeInCubicMeters (figure.volumeAt .d)
  bottomSideConstantPressure :
    pressureInPascals (figure.pressureAt .d) =
      pressureInPascals (figure.pressureAt .a)
  rightVolumeIsLarger :
    volumeInCubicMeters (figure.volumeAt .a) <
      volumeInCubicMeters (figure.volumeAt .d)
  upperPressureIsLarger :
    pressureInPascals (figure.pressureAt .a) <
      pressureInPascals (figure.pressureAt .b)

/-! ## Gas sample, observables, and measurements -/

/-- Chemical species named in the experiment. -/
inductive GasSpecies where
  | argon
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state and caloric model assigned to the gas. -/
inductive GasModel where
  | idealMonatomic
  | other
  deriving DecidableEq, Repr

/--
Physical data for the engine.  The amount of substance remains abstract and
only its mole readout is real-valued.  Heat is positive into the gas, while
work is positive when done by the gas.
-/
structure ArgonHeatEngineSetup (AmountOfSubstance : Type) where
  species : GasSpecies
  gasModel : GasModel
  amountOfGas : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  figure : PressureVolumeCycleFigure
  temperatureAt : CycleState → Temperature
  temperatureStorageUnit : TemperatureUnit
  universalGasConstantJoulePerMoleKelvin : ℝ
  internalEnergyAt : CycleState → DimEnergy
  workDoneByGasOn : CycleLeg → DimEnergy
  heatTransferredIntoGasOn : CycleLeg → DimEnergy

/-- Mole readout of the physical argon sample. -/
def moleAmountOfGas
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : ℝ :=
  setup.amountInMoles setup.amountOfGas

/-- Kelvin readout at a labelled cycle state. -/
def gasTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance)
    (state : CycleState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit (setup.temperatureAt state)

/-- Joule readout of internal energy at a labelled state. -/
def internalEnergyInJoules
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance)
    (state : CycleState) : ℝ :=
  energyInJoules (setup.internalEnergyAt state)

/-- Signed joule readout of work done by the gas along one directed leg. -/
def workDoneByGasInJoules
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.workDoneByGasOn leg)

/-- Signed joule readout of heat transferred into the gas along one leg. -/
def heatTransferredIntoGasInJoules
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.heatTransferredIntoGasOn leg)

/-- Half the final reported decimal place, in kelvin. -/
def temperatureReadoutToleranceInKelvin : ℝ := 1 / 20

/-- Compatibility with a temperature reported to one decimal place. -/
def MatchesTemperatureReadout (actual stated : ℝ) : Prop :=
  |actual - stated| ≤ temperatureReadoutToleranceInKelvin

/--
Problem-prose data: an ideal monatomic four-mole argon sample and the four
measured temperature readouts.  No heat, work, or efficiency is fixed here.
-/
structure MatchesArgonSampleAndTemperatureReadouts
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : Prop where
  speciesIsArgon : setup.species = .argon
  modelIsIdealMonatomic : setup.gasModel = .idealMonatomic
  amountIsFourMoles : moleAmountOfGas setup = 4
  temperatureAtA :
    MatchesTemperatureReadout (gasTemperatureInKelvin setup .a) 250
  temperatureAtB :
    MatchesTemperatureReadout (gasTemperatureInKelvin setup .b) 300
  temperatureAtC :
    MatchesTemperatureReadout (gasTemperatureInKelvin setup .c) 380
  temperatureAtD :
    MatchesTemperatureReadout (gasTemperatureInKelvin setup .d) (3167 / 10)

/-- Positivity and nondegeneracy conditions for a physical engine cycle. -/
structure HasPhysicalCycleParameters
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : Prop where
  amountPositive : 0 < moleAmountOfGas setup
  gasConstantPositive : 0 < setup.universalGasConstantJoulePerMoleKelvin
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.figure.pressureAt state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.figure.volumeAt state)
  absoluteTemperaturePositive :
    ∀ state, 0 < gasTemperatureInKelvin setup state

/--
Thermodynamic laws used for this low-pressure monatomic ideal-gas cycle:
`p V = n R T`, `U = (3/2) n R T`, quasistatic boundary work, and the first
law `Q = ΔU + W` with the sign conventions declared above.
-/
structure SatisfiesMonatomicIdealGasCycleLaws
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : Prop where
  idealGasEquation :
    ∀ state,
      pressureInPascals (setup.figure.pressureAt state) *
          volumeInCubicMeters (setup.figure.volumeAt state) =
        moleAmountOfGas setup *
          setup.universalGasConstantJoulePerMoleKelvin *
            gasTemperatureInKelvin setup state
  monatomicInternalEnergy :
    ∀ state,
      internalEnergyInJoules setup state =
        (3 / 2 : ℝ) * moleAmountOfGas setup *
          setup.universalGasConstantJoulePerMoleKelvin *
            gasTemperatureInKelvin setup state
  quasistaticBoundaryWork :
    ∀ leg,
      workDoneByGasInJoules setup leg =
        pressureInPascals (setup.figure.pressureAt (legSource leg)) *
          (volumeInCubicMeters (setup.figure.volumeAt (legTarget leg)) -
            volumeInCubicMeters (setup.figure.volumeAt (legSource leg)))
  firstLawOnEachLeg :
    ∀ leg,
      heatTransferredIntoGasInJoules setup leg =
        internalEnergyInJoules setup (legTarget leg) -
          internalEnergyInJoules setup (legSource leg) +
            workDoneByGasInJoules setup leg

/-! ## Efficiency and displayed answer choices -/

/-- Net work done by the gas over the complete directed cycle, in joules. -/
def netCycleWorkInJoules
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, workDoneByGasInJoules setup leg

/-- Sum of the positive parts of the signed heat transfers, in joules. -/
def totalHeatInputInJoules
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, max (heatTransferredIntoGasInJoules setup leg) 0

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : ℝ :=
  netCycleWorkInJoules setup / totalHeatInputInJoules setup

/-- Thermal efficiency expressed as a percentage. -/
def thermalEfficiencyPercent
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance) : ℝ :=
  100 * thermalEfficiency setup

/-- Labels of the four printed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Percentage printed beside each answer label. -/
def displayedEfficiencyPercent : AnswerChoice → ℝ
  | .A => 10
  | .B => 25 / 4
  | .C => 59 / 10
  | .D => 123 / 10

/-- The answer label recorded by the dataset, retained as source metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- An actual scalar is within `tolerance` of a stated estimate. -/
def MatchesEstimate (actual stated tolerance : ℝ) : Prop :=
  |actual - stated| ≤ tolerance

/--
A computed percentage is compatible with a displayed choice to one tenth of
a percentage point.
-/
def IsCompatibleDisplayedEfficiencyAnswer
    (actualPercent : ℝ) (choice : AnswerChoice) : Prop :=
  MatchesEstimate actualPercent (displayedEfficiencyPercent choice) (1 / 10)

/--
The measured temperatures and the monatomic ideal-gas laws support an
efficiency near `8/165`, equivalently `160/33 %`.  The tolerances in the
conclusion account conservatively for the one-decimal-place temperature
readouts.

The dataset's recorded choice B is retained separately as metadata, but none
of the printed choices is compatible with the physically supported value.
The premises contain only physical data, diagram readouts, positivity, and
general governing laws; they contain neither the efficiency estimate nor any
answer-choice conclusion.
-/
theorem problem_phyx_mini_0354
    {AmountOfSubstance : Type}
    (setup : ArgonHeatEngineSetup AmountOfSubstance)
    (hFigure : MatchesSuppliedRectangularCycle setup.figure)
    (hReadouts : MatchesArgonSampleAndTemperatureReadouts setup)
    (hPhysical : HasPhysicalCycleParameters setup)
    (hLaws : SatisfiesMonatomicIdealGasCycleLaws setup) :
    MatchesEstimate (thermalEfficiency setup) (8 / 165) (1 / 1000) ∧
      MatchesEstimate (thermalEfficiencyPercent setup) (160 / 33) (1 / 10) ∧
      (∀ choice,
        ¬ IsCompatibleDisplayedEfficiencyAnswer
          (thermalEfficiencyPercent setup) choice) := by
  let Ta : ℝ := gasTemperatureInKelvin setup .a
  let Tb : ℝ := gasTemperatureInKelvin setup .b
  let Tc : ℝ := gasTemperatureInKelvin setup .c
  let Td : ℝ := gasTemperatureInKelvin setup .d
  let K : ℝ :=
    moleAmountOfGas setup *
      setup.universalGasConstantJoulePerMoleKelvin

  have hTa : (4999 / 20 : ℝ) ≤ Ta ∧ Ta ≤ 5001 / 20 := by
    have h := hReadouts.temperatureAtA
    change |Ta - 250| ≤ 1 / 20 at h
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hTb : (5999 / 20 : ℝ) ≤ Tb ∧ Tb ≤ 6001 / 20 := by
    have h := hReadouts.temperatureAtB
    change |Tb - 300| ≤ 1 / 20 at h
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hTc : (7599 / 20 : ℝ) ≤ Tc ∧ Tc ≤ 7601 / 20 := by
    have h := hReadouts.temperatureAtC
    change |Tc - 380| ≤ 1 / 20 at h
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hTd : (6333 / 20 : ℝ) ≤ Td ∧ Td ≤ 6335 / 20 := by
    have h := hReadouts.temperatureAtD
    change |Td - 3167 / 10| ≤ 1 / 20 at h
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]

  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos hPhysical.amountPositive hPhysical.gasConstantPositive

  have hWab : workDoneByGasInJoules setup .ab = 0 := by
    rw [hLaws.quasistaticBoundaryWork]
    simp only [legSource, legTarget]
    rw [hFigure.leftSideConstantVolume, sub_self, mul_zero]
  have hWbc :
      workDoneByGasInJoules setup .bc = K * (Tc - Tb) := by
    rw [hLaws.quasistaticBoundaryWork]
    simp only [legSource, legTarget]
    calc
      pressureInPascals (setup.figure.pressureAt .b) *
            (volumeInCubicMeters (setup.figure.volumeAt .c) -
              volumeInCubicMeters (setup.figure.volumeAt .b)) =
          pressureInPascals (setup.figure.pressureAt .c) *
              volumeInCubicMeters (setup.figure.volumeAt .c) -
            pressureInPascals (setup.figure.pressureAt .b) *
              volumeInCubicMeters (setup.figure.volumeAt .b) := by
                rw [← hFigure.topSideConstantPressure]
                ring
      _ = K * (Tc - Tb) := by
        rw [hLaws.idealGasEquation .c, hLaws.idealGasEquation .b]
        dsimp [K, Tc, Tb]
        ring
  have hWcd : workDoneByGasInJoules setup .cd = 0 := by
    rw [hLaws.quasistaticBoundaryWork]
    simp only [legSource, legTarget]
    rw [← hFigure.rightSideConstantVolume, sub_self, mul_zero]
  have hWda :
      workDoneByGasInJoules setup .da = K * (Ta - Td) := by
    rw [hLaws.quasistaticBoundaryWork]
    simp only [legSource, legTarget]
    calc
      pressureInPascals (setup.figure.pressureAt .d) *
            (volumeInCubicMeters (setup.figure.volumeAt .a) -
              volumeInCubicMeters (setup.figure.volumeAt .d)) =
          pressureInPascals (setup.figure.pressureAt .a) *
              volumeInCubicMeters (setup.figure.volumeAt .a) -
            pressureInPascals (setup.figure.pressureAt .d) *
              volumeInCubicMeters (setup.figure.volumeAt .d) := by
                rw [← hFigure.bottomSideConstantPressure]
                ring
      _ = K * (Ta - Td) := by
        rw [hLaws.idealGasEquation .a, hLaws.idealGasEquation .d]
        dsimp [K, Ta, Td]
        ring

  have hQab :
      heatTransferredIntoGasInJoules setup .ab =
        (3 / 2 : ℝ) * K * (Tb - Ta) := by
    rw [hLaws.firstLawOnEachLeg]
    simp only [legSource, legTarget]
    rw [hLaws.monatomicInternalEnergy .b,
      hLaws.monatomicInternalEnergy .a, hWab]
    dsimp [K, Ta, Tb]
    ring
  have hQbc :
      heatTransferredIntoGasInJoules setup .bc =
        (5 / 2 : ℝ) * K * (Tc - Tb) := by
    rw [hLaws.firstLawOnEachLeg]
    simp only [legSource, legTarget]
    rw [hLaws.monatomicInternalEnergy .c,
      hLaws.monatomicInternalEnergy .b, hWbc]
    ring
  have hQcd :
      heatTransferredIntoGasInJoules setup .cd =
        (3 / 2 : ℝ) * K * (Td - Tc) := by
    rw [hLaws.firstLawOnEachLeg]
    simp only [legSource, legTarget]
    rw [hLaws.monatomicInternalEnergy .d,
      hLaws.monatomicInternalEnergy .c, hWcd]
    dsimp [K, Tc, Td]
    ring
  have hQda :
      heatTransferredIntoGasInJoules setup .da =
        (5 / 2 : ℝ) * K * (Ta - Td) := by
    rw [hLaws.firstLawOnEachLeg]
    simp only [legSource, legTarget]
    rw [hLaws.monatomicInternalEnergy .a,
      hLaws.monatomicInternalEnergy .d, hWda]
    ring

  have hTbTa : 0 < Tb - Ta := by linarith [hTb.1, hTa.2]
  have hTcTb : 0 < Tc - Tb := by linarith [hTc.1, hTb.2]
  have hTdTc : Td - Tc ≤ 0 := by linarith [hTd.2, hTc.1]
  have hTaTd : Ta - Td ≤ 0 := by linarith [hTa.2, hTd.1]
  have hQabNonneg : 0 ≤ heatTransferredIntoGasInJoules setup .ab := by
    rw [hQab]
    positivity
  have hQbcNonneg : 0 ≤ heatTransferredIntoGasInJoules setup .bc := by
    rw [hQbc]
    positivity
  have hQcdNonpos : heatTransferredIntoGasInJoules setup .cd ≤ 0 := by
    rw [hQcd]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) hK.le) hTdTc
  have hQdaNonpos : heatTransferredIntoGasInJoules setup .da ≤ 0 := by
    rw [hQda]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) hK.le) hTaTd

  have sum_cycleLeg (f : CycleLeg → ℝ) :
      (∑ leg : CycleLeg, f leg) =
        f .ab + f .bc + f .cd + f .da := by
    classical
    rw [show (Finset.univ : Finset CycleLeg) = {.ab, .bc, .cd, .da} by
      ext leg
      fin_cases leg <;> simp]
    simp
    ring

  let N : ℝ := Tc - Tb + Ta - Td
  let D : ℝ :=
    (3 / 2 : ℝ) * (Tb - Ta) + (5 / 2 : ℝ) * (Tc - Tb)
  have hNet : netCycleWorkInJoules setup = K * N := by
    rw [netCycleWorkInJoules, sum_cycleLeg, hWab, hWbc, hWcd, hWda]
    dsimp [N]
    ring
  have hHeat : totalHeatInputInJoules setup = K * D := by
    rw [totalHeatInputInJoules, sum_cycleLeg,
      max_eq_left hQabNonneg, max_eq_left hQbcNonneg,
      max_eq_right hQcdNonpos, max_eq_right hQdaNonpos,
      hQab, hQbc]
    dsimp [D]
    ring

  have hNLower : (131 / 10 : ℝ) ≤ N := by
    dsimp [N]
    linarith [hTc.1, hTb.2, hTa.1, hTd.2]
  have hNUpper : N ≤ (27 / 2 : ℝ) := by
    dsimp [N]
    linarith [hTc.2, hTb.1, hTa.2, hTd.1]
  have hDLower : (1099 / 4 : ℝ) ≤ D := by
    dsimp [D]
    linarith [hTb.1, hTa.2, hTc.1, hTb.2]
  have hDUpper : D ≤ (1101 / 4 : ℝ) := by
    dsimp [D]
    linarith [hTb.2, hTa.1, hTc.2, hTb.1]
  have hDPos : 0 < D := by linarith [hDLower]

  have hEfficiency : thermalEfficiency setup = N / D := by
    rw [thermalEfficiency, hNet, hHeat]
    exact mul_div_mul_left N D hK.ne'
  have hEfficiencyLower :
      (8 / 165 : ℝ) - 1 / 1000 ≤ N / D := by
    apply (le_div_iff₀ hDPos).2
    linarith [hNLower, hDUpper]
  have hEfficiencyUpper :
      N / D ≤ (8 / 165 : ℝ) + 1 / 1000 := by
    apply (div_le_iff₀ hDPos).2
    linarith [hNUpper, hDLower]

  constructor
  · rw [MatchesEstimate, hEfficiency, abs_le]
    constructor <;> linarith [hEfficiencyLower, hEfficiencyUpper]
  constructor
  · rw [MatchesEstimate, thermalEfficiencyPercent, hEfficiency, abs_le]
    constructor <;> linarith [hEfficiencyLower, hEfficiencyUpper]
  · intro choice
    fin_cases choice <;>
      simp only [IsCompatibleDisplayedEfficiencyAnswer, MatchesEstimate,
        displayedEfficiencyPercent, thermalEfficiencyPercent, hEfficiency] <;>
      intro hChoice <;>
      have hChoiceLower := (abs_le.mp hChoice).1 <;>
      linarith [hEfficiencyUpper]

end PhyXMiniProblems.ProblemPhyXMini0354
