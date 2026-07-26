import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/-!
# Work done in a three-leg ideal-gas cycle

The primary pressure-volume figure fixes the direction of the cycle as
`a → c → b → a`.  Its `a → c` leg is horizontal (constant pressure), its
`c → b` leg is a curved adiabatic compression, and its `b → a` leg is vertical
(constant volume).

Pressures, volumes, energies, and temperatures retain physical types.  Real
numbers below are explicitly coherent SI readouts: pascals, cubic metres,
joules, kelvin, moles, or joules per mole-kelvin.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0342

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- A physical gas volume, with dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## States, directed legs, and the pressure-volume figure -/

/-- The three labeled thermodynamic states in the supplied figure. -/
inductive CycleState where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The directed legs, in the order indicated by the arrows in the image. -/
inductive CycleLeg where
  | aToC
  | cToB
  | bToA
  deriving DecidableEq, Repr

/-- Initial state of each directed leg. -/
def CycleLeg.initialState : CycleLeg → CycleState
  | .aToC => .a
  | .cToB => .c
  | .bToA => .b

/-- Final state of each directed leg. -/
def CycleLeg.finalState : CycleLeg → CycleState
  | .aToC => .c
  | .cToB => .b
  | .bToA => .a

/-- Physical quantities that can label an axis of the supplied diagram. -/
inductive AxisQuantity where
  | pressure
  | volume
  | other
  deriving DecidableEq, Repr

/-- Labels visibly attached to the origin and the three plotted states. -/
inductive FigurePointLabel where
  | O
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- Thermodynamic classification of a process leg. -/
inductive ProcessKind where
  | constantPressure
  | adiabatic
  | constantVolume
  | other
  deriving DecidableEq, Repr

/-- Geometric appearance of a directed process in the pressure-volume plot. -/
inductive LegShape where
  | horizontal
  | curved
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Orientation of the closed loop read from the arrowheads in the image. -/
inductive CycleDirection where
  | aToCToBToA
  | reverse
  deriving DecidableEq, Repr

/-- The labeled pressure-volume diagram accompanying the exercise. -/
structure PressureVolumeFigure where
  horizontalAxis : AxisQuantity
  verticalAxis : AxisQuantity
  originLabel : FigurePointLabel
  stateLabel : CycleState → FigurePointLabel
  processKind : CycleLeg → ProcessKind
  legShape : CycleLeg → LegShape
  direction : CycleDirection

/-- Pressure, volume, and absolute temperature at one equilibrium state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : GasVolume
  temperature : Temperature

/-! ## Physical setup -/

/--
The ideal gas, its three states, and the energetic quantities assigned to the
three directed legs.  The heat sign convention is heat transferred to the
gas; the work sign convention is work done by the gas.

`amountOfGasMoles`, the two molar heat capacities, and the gas constant are
explicit scalar readouts in the units stated in their field names.
-/
structure IdealGasCycleSetup where
  amountOfGasMoles : ℝ
  molarHeatCapacityAtConstantPressureJPerMolKelvin : ℝ
  molarHeatCapacityAtConstantVolumeJPerMolKelvin : ℝ
  gasConstantJPerMolKelvin : ℝ
  temperatureDisplayUnit : TemperatureUnit
  state : CycleState → ThermodynamicState
  figure : PressureVolumeFigure
  heatTransferredToGas : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  workDoneByGas : CycleLeg → DimEnergy
  totalWorkDoneByGas : DimEnergy

/-- Positivity assumptions selecting physical ideal-gas states and constants. -/
structure HasPhysicalIdealGasCycleParameters
    (setup : IdealGasCycleSetup) : Prop where
  amountPositive : 0 < setup.amountOfGasMoles
  heatCapacityAtConstantPressurePositive :
    0 < setup.molarHeatCapacityAtConstantPressureJPerMolKelvin
  heatCapacityAtConstantVolumePositive :
    0 < setup.molarHeatCapacityAtConstantVolumeJPerMolKelvin
  gasConstantPositive : 0 < setup.gasConstantJPerMolKelvin
  temperaturePositive :
    ∀ state, 0 < (setup.state state).temperature.toReal
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.state state).pressure
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.state state).volume

/-!
## Governing laws

These assumptions are general thermodynamic relations specialized to the
three named legs.  None specifies the requested numerical cycle work.
-/

/--
Ideal-gas mechanics and the first law for the cycle, expressed in coherent SI
readouts.  The convention `Q = ΔU + W` uses `W > 0` for work done by the gas.
-/
structure SatisfiesIdealGasCycleLaws
    (setup : IdealGasCycleSetup) : Prop where
  idealGasLawAtEachState :
    ∀ state,
      pressureInPascals (setup.state state).pressure *
          volumeInCubicMeters (setup.state state).volume =
        setup.amountOfGasMoles * setup.gasConstantJPerMolKelvin *
          (setup.state state).temperature.toReal
  mayerHeatCapacityRelation :
    setup.molarHeatCapacityAtConstantPressureJPerMolKelvin =
      setup.molarHeatCapacityAtConstantVolumeJPerMolKelvin +
        setup.gasConstantJPerMolKelvin
  idealGasInternalEnergyChange :
    ∀ leg,
      energyInJoules (setup.internalEnergyChange leg) =
        setup.amountOfGasMoles *
          setup.molarHeatCapacityAtConstantVolumeJPerMolKelvin *
            ((setup.state leg.finalState).temperature.toReal -
              (setup.state leg.initialState).temperature.toReal)
  firstLawOnEachLeg :
    ∀ leg,
      energyInJoules (setup.heatTransferredToGas leg) =
        energyInJoules (setup.internalEnergyChange leg) +
          energyInJoules (setup.workDoneByGas leg)
  adiabaticLegHasNoHeatTransfer :
    energyInJoules (setup.heatTransferredToGas .cToB) = 0
  constantPressureBoundaryWork :
    energyInJoules (setup.workDoneByGas .aToC) =
      pressureInPascals (setup.state .a).pressure *
        (volumeInCubicMeters (setup.state .c).volume -
          volumeInCubicMeters (setup.state .a).volume)
  constantVolumeLegDoesNoWork :
    energyInJoules (setup.workDoneByGas .bToA) = 0
  totalWorkIsSumOfDirectedLegs :
    energyInJoules setup.totalWorkDoneByGas =
      energyInJoules (setup.workDoneByGas .aToC) +
        energyInJoules (setup.workDoneByGas .cToB) +
          energyInJoules (setup.workDoneByGas .bToA)

/-! ## Textual and primary-figure data -/

/--
The numerical givens and trustworthy readouts from the primary image.  In
particular, the arrowheads give `a → c → b → a`, while horizontal and vertical
alignment give equal pressure on `a,c` and equal volume on `b,a`.
-/
structure HasGivenIdealGasCycleData
    (setup : IdealGasCycleSetup) : Prop where
  amountIsThreeMoles : setup.amountOfGasMoles = 3
  heatCapacityAtConstantPressureIs29Point1 :
    setup.molarHeatCapacityAtConstantPressureJPerMolKelvin = 29.1
  standardGasConstantReadout : setup.gasConstantJPerMolKelvin = 8.31
  temperaturesUseKelvin :
    setup.temperatureDisplayUnit = TemperatureUnit.kelvin
  stateATemperature : (setup.state .a).temperature.toReal = 300
  stateCTemperature : (setup.state .c).temperature.toReal = 492
  stateBTemperature : (setup.state .b).temperature.toReal = 600
  horizontalAxisIsVolume : setup.figure.horizontalAxis = .volume
  verticalAxisIsPressure : setup.figure.verticalAxis = .pressure
  originIsLabeledO : setup.figure.originLabel = .O
  stateLabels :
    setup.figure.stateLabel .a = .a ∧
      setup.figure.stateLabel .b = .b ∧
        setup.figure.stateLabel .c = .c
  directedCycle : setup.figure.direction = .aToCToBToA
  processKinds :
    setup.figure.processKind .aToC = .constantPressure ∧
      setup.figure.processKind .cToB = .adiabatic ∧
        setup.figure.processKind .bToA = .constantVolume
  processShapes :
    setup.figure.legShape .aToC = .horizontal ∧
      setup.figure.legShape .cToB = .curved ∧
        setup.figure.legShape .bToA = .vertical
  constantPressureAlignment :
    (setup.state .a).pressure = (setup.state .c).pressure
  constantVolumeAlignment :
    (setup.state .b).volume = (setup.state .a).volume

/-! ## Requested result -/

/--
The joule readout of `work` rounds to `reportedJoules` at the nearest-ten-joule
precision implicit in a three-significant-figure value near two kilojoules.
-/
def RoundsToNearestTenJoules
    (work : DimEnergy) (reportedJoules : ℝ) : Prop :=
  |energyInJoules work - reportedJoules| < 5

/--
The total work done by the gas in the cycle is reported as
`-1.95 × 10³ J`, answer choice B.

Blueprint label: `thm:physics:phyx_mini_0342:target`.
-/
theorem totalWorkDoneByGas_rounds_to_negative_1Point95_kilojoules
    (setup : IdealGasCycleSetup)
    (_physical : HasPhysicalIdealGasCycleParameters setup)
    (_laws : SatisfiesIdealGasCycleLaws setup)
    (_data : HasGivenIdealGasCycleData setup) :
    RoundsToNearestTenJoules setup.totalWorkDoneByGas
      ((-1.95 : ℝ) * (10 : ℝ) ^ 3) := by
  have hIdealA := _laws.idealGasLawAtEachState .a
  have hIdealC := _laws.idealGasLawAtEachState .c
  have hPressureAC :
      pressureInPascals (setup.state .a).pressure =
        pressureInPascals (setup.state .c).pressure :=
    congrArg pressureInPascals _data.constantPressureAlignment
  have hWorkAC := _laws.constantPressureBoundaryWork
  have hMayer := _laws.mayerHeatCapacityRelation
  have hInternalCB := _laws.idealGasInternalEnergyChange .cToB
  have hFirstLawCB := _laws.firstLawOnEachLeg .cToB
  have hAdiabaticCB := _laws.adiabaticLegHasNoHeatTransfer
  have hWorkBA := _laws.constantVolumeLegDoesNoWork
  have hTotal := _laws.totalWorkIsSumOfDirectedLegs
  simp only [CycleLeg.initialState, CycleLeg.finalState] at hInternalCB
  rw [_data.amountIsThreeMoles, _data.standardGasConstantReadout,
    _data.stateATemperature] at hIdealA
  rw [_data.amountIsThreeMoles, _data.standardGasConstantReadout,
    _data.stateCTemperature] at hIdealC
  rw [← hPressureAC] at hIdealC
  rw [_data.heatCapacityAtConstantPressureIs29Point1,
    _data.standardGasConstantReadout] at hMayer
  rw [_data.amountIsThreeMoles, _data.stateCTemperature,
    _data.stateBTemperature] at hInternalCB
  have hWorkACValue :
      energyInJoules (setup.workDoneByGas .aToC) = 4786.56 := by
    nlinarith
  have hHeatCapacityAtConstantVolume :
      setup.molarHeatCapacityAtConstantVolumeJPerMolKelvin = 20.79 := by
    norm_num at hMayer ⊢
    linarith
  rw [hHeatCapacityAtConstantVolume] at hInternalCB
  have hWorkCBValue :
      energyInJoules (setup.workDoneByGas .cToB) = -6735.96 := by
    norm_num at hInternalCB
    linarith
  rw [hWorkACValue, hWorkCBValue, hWorkBA] at hTotal
  unfold RoundsToNearestTenJoules
  rw [hTotal]
  norm_num [abs_of_nonneg, abs_of_pos]

end PhyXMiniProblems.ProblemPhyXMini0342
