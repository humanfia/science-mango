import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0338

open Dimension

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Heat added along a two-leg process in a pressure-volume diagram

The primary image shows an ideal-gas process `a → b → c`.  The segment from
`a` to `b` is a straight line in the `pV` plane, while the segment from `b` to
`c` is vertical and hence isochoric.  The auxiliary caption misreads several
grid coordinates; the image itself gives

* `a = (0.010 m³, 2.0 × 10⁵ Pa)`,
* `b = (0.070 m³, 5.0 × 10⁵ Pa)`, and
* `c = (0.070 m³, 8.0 × 10⁵ Pa)`.

These readings make the work done by the gas the trapezoidal area
`21000 J`.  The first-law convention used below is `Q = ΔU + W`, where `W`
is work done by the gas.  The numerical work and requested heat are theorem
conclusions, not problem-data or governing-law fields.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical volume, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Gas, state, and primary-figure roles -/

/-- Whether the sample obeys the ideal-gas model stated in the problem. -/
inductive GasModel where
  | idealGas
  | other
  deriving DecidableEq, Repr

/-- A gas sample together with its measured amount-of-substance readout. -/
structure GasSample where
  model : GasModel
  amountInMoles : NNReal

/-- The three labeled equilibrium states in the diagram. -/
inductive StateLabel where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The two directed legs of the process `abc`. -/
inductive LegLabel where
  | ab
  | bc
  deriving DecidableEq, Repr

/-- Initial labeled state of each process leg. -/
def LegLabel.initialState : LegLabel → StateLabel
  | .ab => .a
  | .bc => .b

/-- Final labeled state of each process leg. -/
def LegLabel.finalState : LegLabel → StateLabel
  | .ab => .b
  | .bc => .c

/-- A thermodynamic state as dimensionful pressure and volume. -/
structure PVState where
  volume : VolumeQuantity
  pressure : DimPressure

/-- Physical quantity assigned to an axis of the supplied plot. -/
inductive AxisQuantity where
  | volume
  | pressure
  | other
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal axis. -/
inductive VolumeDisplayUnit where
  | cubicMeter
  | other
  deriving DecidableEq, Repr

/-- Scale printed on the vertical axis. -/
inductive PressureDisplayScale where
  | pascalsTimesTenToTheFifth
  | other
  deriving DecidableEq, Repr

/-- Geometric form of a directed leg in the pressure-volume plane. -/
inductive LegGeometry where
  | straightLine
  | verticalIsochoric
  | other
  deriving DecidableEq, Repr

/-- The labeled pressure-volume diagram supplied with the problem. -/
structure PVDiagram where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalDisplayUnit : VolumeDisplayUnit
  verticalDisplayScale : PressureDisplayScale
  state : StateLabel → PVState
  legGeometry : LegLabel → LegGeometry
  arrowTail : LegLabel → StateLabel
  arrowHead : LegLabel → StateLabel

/-! ## Physical setup, figure readouts, and governing laws -/

/-- The gas process and its energy transfers. -/
structure IdealGasProcessABC where
  gas : GasSample
  diagram : PVDiagram
  internalEnergyIncrease : DimEnergy
  heatAdded : DimEnergy
  workDoneByGas : DimEnergy
  legWorkDoneByGas : LegLabel → DimEnergy

/--
Problem data and exact grid readouts from the primary image.  The amount is
`0.450 mol`, and the specified internal-energy increase is `15000 J`.
No value of the heat added or of the pressure-volume work is assumed here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : IdealGasProcessABC) : Prop where
  gasIsIdeal : setup.gas.model = .idealGas
  amountReadout_mol : (setup.gas.amountInMoles : ℝ) = 9 / 20
  horizontalAxisIsVolume :
    setup.diagram.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.diagram.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicMeters :
    setup.diagram.horizontalDisplayUnit = .cubicMeter
  verticalAxisUsesScaledPascals :
    setup.diagram.verticalDisplayScale = .pascalsTimesTenToTheFifth
  stateA_volume_m3 :
    volumeInCubicMeters (setup.diagram.state .a).volume = 1 / 100
  stateA_pressure_pa :
    pressureInPascals (setup.diagram.state .a).pressure = 200000
  stateB_volume_m3 :
    volumeInCubicMeters (setup.diagram.state .b).volume = 7 / 100
  stateB_pressure_pa :
    pressureInPascals (setup.diagram.state .b).pressure = 500000
  stateC_volume_m3 :
    volumeInCubicMeters (setup.diagram.state .c).volume = 7 / 100
  stateC_pressure_pa :
    pressureInPascals (setup.diagram.state .c).pressure = 800000
  legAB_isStraight : setup.diagram.legGeometry .ab = .straightLine
  legBC_isVerticalIsochoric :
    setup.diagram.legGeometry .bc = .verticalIsochoric
  arrowsFollowProcessOrder :
    ∀ leg : LegLabel,
      setup.diagram.arrowTail leg = leg.initialState ∧
        setup.diagram.arrowHead leg = leg.finalState
  internalEnergyIncrease_joules :
    energyInJoules setup.internalEnergyIncrease = 15000

/-- Positivity and ordering conditions for the physical process. -/
structure HasPhysicalProcessParameters
    (setup : IdealGasProcessABC) : Prop where
  amountPositive : 0 < (setup.gas.amountInMoles : ℝ)
  volumePositive :
    ∀ state : StateLabel,
      0 < volumeInCubicMeters (setup.diagram.state state).volume
  pressurePositive :
    ∀ state : StateLabel,
      0 < pressureInPascals (setup.diagram.state state).pressure
  expansionOnAB :
    volumeInCubicMeters (setup.diagram.state .a).volume <
      volumeInCubicMeters (setup.diagram.state .b).volume
  constantVolumeOnBC :
    volumeInCubicMeters (setup.diagram.state .b).volume =
      volumeInCubicMeters (setup.diagram.state .c).volume

/--
The pressure-volume work law and the first law of thermodynamics.

For a straight leg, the integral `∫ p dV` is the average endpoint pressure
times the volume change.  A vertical isochoric leg performs zero work.
The final field uses the sign convention `Q = ΔU + W_by_gas`.
All equations are symbolic governing laws; none fixes the requested heat to a
numerical answer.
-/
structure SatisfiesThermodynamicLaws
    (setup : IdealGasProcessABC) : Prop where
  straightLegWork :
    ∀ leg : LegLabel,
      setup.diagram.legGeometry leg = .straightLine →
      energyInJoules (setup.legWorkDoneByGas leg) =
        (pressureInPascals
              (setup.diagram.state leg.initialState).pressure +
            pressureInPascals
              (setup.diagram.state leg.finalState).pressure) / 2 *
          (volumeInCubicMeters
              (setup.diagram.state leg.finalState).volume -
            volumeInCubicMeters
              (setup.diagram.state leg.initialState).volume)
  isochoricLegWork :
    ∀ leg : LegLabel,
      setup.diagram.legGeometry leg = .verticalIsochoric →
      volumeInCubicMeters
          (setup.diagram.state leg.initialState).volume =
        volumeInCubicMeters
          (setup.diagram.state leg.finalState).volume →
      energyInJoules (setup.legWorkDoneByGas leg) = 0
  totalWorkIsLegSum :
    energyInJoules setup.workDoneByGas =
      energyInJoules (setup.legWorkDoneByGas .ab) +
        energyInJoules (setup.legWorkDoneByGas .bc)
  firstLaw :
    energyInJoules setup.heatAdded =
      energyInJoules setup.internalEnergyIncrease +
        energyInJoules setup.workDoneByGas

/-! ## Derived work, answer choices, and target -/

/--
The net work read from the straight `ab` leg and the isochoric `bc` leg is
`21000 J`.  This is a derived intermediate result, not a figure readout.
-/
lemma workDoneByGas_joules_eq_21000
    (setup : IdealGasProcessABC)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalProcessParameters setup)
    (hLaws : SatisfiesThermodynamicLaws setup) :
    energyInJoules setup.workDoneByGas = 21000 := by
  have hAB :=
    hLaws.straightLegWork .ab hFigure.legAB_isStraight
  have hBC :=
    hLaws.isochoricLegWork .bc hFigure.legBC_isVerticalIsochoric
      hPhysical.constantVolumeOnBC
  norm_num [LegLabel.initialState, LegLabel.finalState,
    hFigure.stateA_pressure_pa, hFigure.stateB_pressure_pa,
    hFigure.stateA_volume_m3, hFigure.stateB_volume_m3] at hAB
  rw [hLaws.totalWorkIsLegSum, hAB, hBC]
  norm_num

/-- Labels printed beside the four candidate heat values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Heat in joules printed beside each answer label. -/
def AnswerChoice.heatInJoules : AnswerChoice → ℝ
  | .A => 340000
  | .B => 36000
  | .C => 26000
  | .D => 32000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A displayed choice agrees with the physical heat added in the process. -/
def IsCorrectDisplayedChoice
    (setup : IdealGasProcessABC) (choice : AnswerChoice) : Prop :=
  energyInJoules setup.heatAdded = choice.heatInJoules

/--
The heat that must be added during `a → b → c` is `36000 J`.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0338:target`.
-/
theorem heatAddedDuringProcessABC_joules_eq_36000
    (setup : IdealGasProcessABC)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalProcessParameters setup)
    (hLaws : SatisfiesThermodynamicLaws setup) :
    energyInJoules setup.heatAdded = 36000 := by
  rw [hLaws.firstLaw, hFigure.internalEnergyIncrease_joules,
    workDoneByGas_joules_eq_21000 setup hFigure hPhysical hLaws]
  norm_num

/-- Consequently, the recorded answer choice `B` is the correct one. -/
theorem recordedAnswerChoice_isCorrect
    (setup : IdealGasProcessABC)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalProcessParameters setup)
    (hLaws : SatisfiesThermodynamicLaws setup) :
    IsCorrectDisplayedChoice setup recordedAnswerChoice := by
  simpa [IsCorrectDisplayedChoice, recordedAnswerChoice,
    AnswerChoice.heatInJoules] using
      heatAddedDuringProcessABC_joules_eq_36000 setup hFigure hPhysical hLaws

end PhyXMiniProblems.ProblemPhyXMini0338
