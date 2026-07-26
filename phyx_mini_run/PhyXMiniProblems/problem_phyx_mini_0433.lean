import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0433

open Dimension

/-!
# Thermal efficiency of a triangular monatomic-gas heat-engine cycle

The primary pressure--volume bitmap shows the clockwise cycle
`1 → 2 → 3 → 1` with states

* `1 = (0.025 m³, 400 kPa)`,
* `2 = (0.050 m³, 600 kPa)`, and
* `3 = (0.050 m³, 400 kPa)`.

Thus `1 → 2` is a rising straight-line expansion, `2 → 3` is an isochoric
pressure decrease, and `3 → 1` is an isobaric compression.  The auxiliary
caption incorrectly describes the vertical second leg as decreasing in
volume; the bitmap is the designated primary evidence.  The working sample
is `2.0 mol` of monatomic gas.

Pressure, volume, internal energy, heat, and work remain dimensionful physical
quantities.  Real numbers below are explicitly named unit readouts, the mole
readout stated in the problem, dimensionless efficiencies, or displayed
multiple-choice values.  Work is positive when done by the gas and heat is
positive when transferred into it.

Assumption/target split:

* `MatchesProblemStatement` records the heat-engine role, monatomic ideal-gas
  model, and independently stated two-mole sample;
* `MatchesPrimaryPressureVolumeFigure` records the axes, units, ticks, three
  labelled coordinates, straight segments, and displayed arrow directions;
* `UsesClosedQuasistaticCycleModel` and `HasPhysicalCycleParameters` record
  the standard modelling regime and positivity conditions;
* `SatisfiesMonatomicIdealGasCycleLaws` states the caloric relation, straight
  quasistatic boundary-work law, and first law on every leg; and
* `problem_phyx_mini_0433` concludes the exact efficiency and the unique
  nearest-thousandth answer.  No premise fixes either conclusion.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A signed physical volume carrying the dimension of length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy, used for internal energy, heat, and work. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical pressure in SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical pressure in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read signed heat, work, or internal energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Working substance, states, directed legs, and figure vocabulary -/

/-- Material model used to interpret the monatomic working gas. -/
inductive GasModel where
  | monatomicIdealGas
  deriving DecidableEq, Repr

/-- Thermodynamic role explicitly assigned to the depicted device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- Regime in which a plotted pressure--volume curve gives boundary work. -/
inductive ProcessRegime where
  | quasistaticEquilibriumPath
  | other
  deriving DecidableEq, Repr

/-- The three numerical state labels printed in the primary bitmap. -/
inductive CycleState where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The directed legs, listed in the displayed traversal order. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint of a directed cycle leg. -/
def CycleLeg.start : CycleLeg → CycleState
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final endpoint of a directed cycle leg. -/
def CycleLeg.finish : CycleLeg → CycleState
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Thermodynamic character of a displayed process leg. -/
inductive ProcessKind where
  | straightLineExpansion
  | isochoricCooling
  | isobaricCompression
  deriving DecidableEq, Repr

/-- Geometric shape of every leg drawn in the primary image. -/
inductive PathShape where
  | straightSegment
  deriving DecidableEq, Repr

/-- Orientation of a segment in the pressure--volume plane. -/
inductive SegmentOrientation where
  | risingRight
  | verticalDown
  | horizontalLeft
  deriving DecidableEq, Repr

/-- The two Cartesian axes in the supplied plot. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity represented by a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside a diagram axis. -/
inductive AxisDisplayUnit where
  | cubicMeters
  | kilopascals
  deriving DecidableEq, Repr

/-- Literal mathematical symbol printed beside a diagram axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Pressure, volume, and internal energy at one equilibrium state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  internalEnergy : EnergyQuantity

/-!
Literal scalar and qualitative content of the supplied raster.  Plotted
coordinates are named readouts in the displayed units; the corresponding
physical quantities remain in `HeatEngineCycleSetup`.
-/
structure PressureVolumeFigure where
  axisQuantity : DiagramAxis → AxisQuantity
  axisDisplayUnit : DiagramAxis → AxisDisplayUnit
  axisSymbol : DiagramAxis → AxisSymbol
  volumeTickVisible : ℝ → Bool
  pressureTickVisible : ℝ → Bool
  stateLabelVisible : CycleState → Bool
  plottedVolumeCubicMeters : CycleState → ℝ
  plottedPressureKilopascals : CycleState → ℝ
  directedLegVisible : CycleLeg → Bool
  directedEndpoints : CycleLeg → CycleState × CycleState
  pathShape : CycleLeg → PathShape
  segmentOrientation : CycleLeg → SegmentOrientation
  depictedProcessKind : CycleLeg → ProcessKind

/-!
Independent physical quantities for the working gas and its cycle.  Neither
net work, total heat input, thermal efficiency, nor an answer choice is stored
as a field.
-/
structure HeatEngineCycleSetup where
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  amountOfGasMoles : ℝ
  sameClosedSample : Bool
  processRegime : ProcessRegime
  stateAt : CycleState → ThermodynamicState
  workDoneByGasOnLeg : CycleLeg → EnergyQuantity
  heatTransferredIntoGasOnLeg : CycleLeg → EnergyQuantity
  figure : PressureVolumeFigure

/-! ## Problem statement, primary-image readouts, and physical branch -/

/-!
The prose data.  The mole count is retained even though it cancels after the
ideal-gas and monatomic caloric laws are combined into `U = 3pV/2`.
-/
structure MatchesProblemStatement (setup : HeatEngineCycleSetup) : Prop where
  gasIsMonatomicIdeal : setup.gasModel = .monatomicIdealGas
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  amountIsTwoMoles : setup.amountOfGasMoles = 2

/-!
Exact transcription of the primary bitmap: pressure is vertical in `kPa`,
volume is horizontal in `m³`, and the directed triangle has the displayed
coordinates and orientations.  No heat, work, or efficiency value occurs in
this figure-data structure.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : HeatEngineCycleSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalUnitIsCubicMeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicMeters
  verticalUnitIsKilopascals :
    setup.figure.axisDisplayUnit .vertical = .kilopascals
  horizontalSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalSymbolIsP : setup.figure.axisSymbol .vertical = .p
  displayedVolumeTicks :
    setup.figure.volumeTickVisible 0 = true ∧
      setup.figure.volumeTickVisible (1 / 40) = true ∧
      setup.figure.volumeTickVisible (1 / 20) = true
  displayedPressureTicks :
    setup.figure.pressureTickVisible 0 = true ∧
      setup.figure.pressureTickVisible 200 = true ∧
      setup.figure.pressureTickVisible 400 = true ∧
      setup.figure.pressureTickVisible 600 = true
  everyStateLabelIsVisible :
    ∀ state, setup.figure.stateLabelVisible state = true
  stateOnePlottedCoordinates :
    setup.figure.plottedVolumeCubicMeters .one = 1 / 40 ∧
      setup.figure.plottedPressureKilopascals .one = 400
  stateTwoPlottedCoordinates :
    setup.figure.plottedVolumeCubicMeters .two = 1 / 20 ∧
      setup.figure.plottedPressureKilopascals .two = 600
  stateThreePlottedCoordinates :
    setup.figure.plottedVolumeCubicMeters .three = 1 / 20 ∧
      setup.figure.plottedPressureKilopascals .three = 400
  physicalStatesAgreeWithPlottedCoordinates : ∀ state,
    volumeInCubicMeters (setup.stateAt state).volume =
        setup.figure.plottedVolumeCubicMeters state ∧
      pressureInKilopascals (setup.stateAt state).pressure =
        setup.figure.plottedPressureKilopascals state
  everyDirectedLegIsVisible :
    ∀ leg, setup.figure.directedLegVisible leg = true
  displayedDirectedEndpoints : ∀ leg,
    setup.figure.directedEndpoints leg = (leg.start, leg.finish)
  everyLegIsStraight :
    ∀ leg, setup.figure.pathShape leg = .straightSegment
  oneToTwoRisesRight :
    setup.figure.segmentOrientation .oneToTwo = .risingRight
  twoToThreePointsDown :
    setup.figure.segmentOrientation .twoToThree = .verticalDown
  threeToOnePointsLeft :
    setup.figure.segmentOrientation .threeToOne = .horizontalLeft
  firstLegIsStraightExpansion :
    setup.figure.depictedProcessKind .oneToTwo = .straightLineExpansion
  secondLegIsIsochoricCooling :
    setup.figure.depictedProcessKind .twoToThree = .isochoricCooling
  thirdLegIsIsobaricCompression :
    setup.figure.depictedProcessKind .threeToOne = .isobaricCompression

/-- Closed-sample and quasistatic idealizations implied by the engine cycle. -/
structure UsesClosedQuasistaticCycleModel
    (setup : HeatEngineCycleSetup) : Prop where
  usesSameClosedSample : setup.sameClosedSample = true
  followsQuasistaticEquilibriumPath :
    setup.processRegime = .quasistaticEquilibriumPath

/-! Positivity conditions selecting the physical thermodynamic branch. -/
structure HasPhysicalCycleParameters
    (setup : HeatEngineCycleSetup) : Prop where
  amountPositive : 0 < setup.amountOfGasMoles
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.stateAt state).volume
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.stateAt state).pressure
  totalHeatInputPositive :
    0 <
      max (energyInJoules (setup.heatTransferredIntoGasOnLeg .oneToTwo)) 0 +
      max (energyInJoules (setup.heatTransferredIntoGasOnLeg .twoToThree)) 0 +
      max (energyInJoules (setup.heatTransferredIntoGasOnLeg .threeToOne)) 0

/-! ## Governing thermodynamic laws -/

/-!
Macroscopic laws for the closed monatomic ideal-gas cycle.

* Combining `pV = nRT` with `U = (3/2)nRT` gives `U = (3/2)pV` at every
  equilibrium state.  This unit-aware form avoids Physlib's unrelated
  unitless statistical-mechanics ideal-gas theorem.
* On a straight quasistatic segment, work by the gas is average endpoint
  pressure times the signed volume change.
* With heat positive into the gas and work positive out, the first law is
  `Q = U_finish - U_start + W_by` on every leg.

These laws are uniform in states and legs and contain no figure-specific
coordinate, net-work, heat-input, efficiency, or answer value.
-/
structure SatisfiesMonatomicIdealGasCycleLaws
    (setup : HeatEngineCycleSetup) : Prop where
  monatomicInternalEnergyLaw : ∀ state,
    energyInJoules (setup.stateAt state).internalEnergy =
      (3 / 2 : ℝ) * pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume
  straightSegmentBoundaryWork :
    setup.processRegime = .quasistaticEquilibriumPath →
      ∀ leg,
        setup.figure.pathShape leg = .straightSegment →
          energyInJoules (setup.workDoneByGasOnLeg leg) =
            (pressureInPascals (setup.stateAt leg.start).pressure +
                pressureInPascals (setup.stateAt leg.finish).pressure) / 2 *
              (volumeInCubicMeters (setup.stateAt leg.finish).volume -
                volumeInCubicMeters (setup.stateAt leg.start).volume)
  firstLawOnEachLeg : ∀ leg,
    energyInJoules (setup.heatTransferredIntoGasOnLeg leg) =
      energyInJoules (setup.stateAt leg.finish).internalEnergy -
          energyInJoules (setup.stateAt leg.start).internalEnergy +
        energyInJoules (setup.workDoneByGasOnLeg leg)

/-! ## Derived cycle accounting and dimensionless efficiency -/

/-- Net work done by the gas over one traversal of the three-leg cycle. -/
def netWorkByGasInJoules (setup : HeatEngineCycleSetup) : ℝ :=
  energyInJoules (setup.workDoneByGasOnLeg .oneToTwo) +
    energyInJoules (setup.workDoneByGasOnLeg .twoToThree) +
    energyInJoules (setup.workDoneByGasOnLeg .threeToOne)

/-- The positive part of a signed heat transfer into the gas. -/
def positiveHeatInJoules (heat : EnergyQuantity) : ℝ :=
  max (energyInJoules heat) 0

/-- Total heat absorbed by the gas, excluding legs on which heat leaves it. -/
def totalHeatInputInJoules (setup : HeatEngineCycleSetup) : ℝ :=
  positiveHeatInJoules (setup.heatTransferredIntoGasOnLeg .oneToTwo) +
    positiveHeatInJoules (setup.heatTransferredIntoGasOnLeg .twoToThree) +
    positiveHeatInJoules (setup.heatTransferredIntoGasOnLeg .threeToOne)

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency (setup : HeatEngineCycleSetup) : ℝ :=
  netWorkByGasInJoules setup / totalHeatInputInJoules setup

/-!
The figure and governing laws determine the three state energies, three
signed works, and three signed heats.  In particular, only `1 → 2` absorbs
heat.  Every equality here is a derived conclusion rather than a premise.
-/
lemma cycleEnergyAccounting
    (setup : HeatEngineCycleSetup)
    (_scenario : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_model : UsesClosedQuasistaticCycleModel setup)
    (_laws : SatisfiesMonatomicIdealGasCycleLaws setup) :
    energyInJoules (setup.stateAt .one).internalEnergy = 15000 ∧
      energyInJoules (setup.stateAt .two).internalEnergy = 45000 ∧
      energyInJoules (setup.stateAt .three).internalEnergy = 30000 ∧
      energyInJoules (setup.workDoneByGasOnLeg .oneToTwo) = 12500 ∧
      energyInJoules (setup.workDoneByGasOnLeg .twoToThree) = 0 ∧
      energyInJoules (setup.workDoneByGasOnLeg .threeToOne) = -10000 ∧
      energyInJoules (setup.heatTransferredIntoGasOnLeg .oneToTwo) = 42500 ∧
      energyInJoules (setup.heatTransferredIntoGasOnLeg .twoToThree) = -15000 ∧
      energyInJoules (setup.heatTransferredIntoGasOnLeg .threeToOne) = -25000 ∧
      netWorkByGasInJoules setup = 2500 ∧
      totalHeatInputInJoules setup = 42500 := by
  have hV₁ :
      volumeInCubicMeters (setup.stateAt .one).volume = 1 / 40 := by
    calc
      volumeInCubicMeters (setup.stateAt .one).volume =
          setup.figure.plottedVolumeCubicMeters .one :=
        (_figure.physicalStatesAgreeWithPlottedCoordinates .one).1
      _ = 1 / 40 := _figure.stateOnePlottedCoordinates.1
  have hV₂ :
      volumeInCubicMeters (setup.stateAt .two).volume = 1 / 20 := by
    calc
      volumeInCubicMeters (setup.stateAt .two).volume =
          setup.figure.plottedVolumeCubicMeters .two :=
        (_figure.physicalStatesAgreeWithPlottedCoordinates .two).1
      _ = 1 / 20 := _figure.stateTwoPlottedCoordinates.1
  have hV₃ :
      volumeInCubicMeters (setup.stateAt .three).volume = 1 / 20 := by
    calc
      volumeInCubicMeters (setup.stateAt .three).volume =
          setup.figure.plottedVolumeCubicMeters .three :=
        (_figure.physicalStatesAgreeWithPlottedCoordinates .three).1
      _ = 1 / 20 := _figure.stateThreePlottedCoordinates.1
  have hP₁ :
      pressureInPascals (setup.stateAt .one).pressure = 400000 := by
    have h :
        pressureInKilopascals (setup.stateAt .one).pressure = 400 := by
      calc
        pressureInKilopascals (setup.stateAt .one).pressure =
            setup.figure.plottedPressureKilopascals .one :=
          (_figure.physicalStatesAgreeWithPlottedCoordinates .one).2
        _ = 400 := _figure.stateOnePlottedCoordinates.2
    unfold pressureInKilopascals at h
    linarith
  have hP₂ :
      pressureInPascals (setup.stateAt .two).pressure = 600000 := by
    have h :
        pressureInKilopascals (setup.stateAt .two).pressure = 600 := by
      calc
        pressureInKilopascals (setup.stateAt .two).pressure =
            setup.figure.plottedPressureKilopascals .two :=
          (_figure.physicalStatesAgreeWithPlottedCoordinates .two).2
        _ = 600 := _figure.stateTwoPlottedCoordinates.2
    unfold pressureInKilopascals at h
    linarith
  have hP₃ :
      pressureInPascals (setup.stateAt .three).pressure = 400000 := by
    have h :
        pressureInKilopascals (setup.stateAt .three).pressure = 400 := by
      calc
        pressureInKilopascals (setup.stateAt .three).pressure =
            setup.figure.plottedPressureKilopascals .three :=
          (_figure.physicalStatesAgreeWithPlottedCoordinates .three).2
        _ = 400 := _figure.stateThreePlottedCoordinates.2
    unfold pressureInKilopascals at h
    linarith
  have hU₁ :
      energyInJoules (setup.stateAt .one).internalEnergy = 15000 := by
    calc
      energyInJoules (setup.stateAt .one).internalEnergy =
          (3 / 2 : ℝ) *
            pressureInPascals (setup.stateAt .one).pressure *
            volumeInCubicMeters (setup.stateAt .one).volume :=
        _laws.monatomicInternalEnergyLaw .one
      _ = 15000 := by rw [hP₁, hV₁]; norm_num
  have hU₂ :
      energyInJoules (setup.stateAt .two).internalEnergy = 45000 := by
    calc
      energyInJoules (setup.stateAt .two).internalEnergy =
          (3 / 2 : ℝ) *
            pressureInPascals (setup.stateAt .two).pressure *
            volumeInCubicMeters (setup.stateAt .two).volume :=
        _laws.monatomicInternalEnergyLaw .two
      _ = 45000 := by rw [hP₂, hV₂]; norm_num
  have hU₃ :
      energyInJoules (setup.stateAt .three).internalEnergy = 30000 := by
    calc
      energyInJoules (setup.stateAt .three).internalEnergy =
          (3 / 2 : ℝ) *
            pressureInPascals (setup.stateAt .three).pressure *
            volumeInCubicMeters (setup.stateAt .three).volume :=
        _laws.monatomicInternalEnergyLaw .three
      _ = 30000 := by rw [hP₃, hV₃]; norm_num
  have hW₁₂ :
      energyInJoules (setup.workDoneByGasOnLeg .oneToTwo) = 12500 := by
    have h := _laws.straightSegmentBoundaryWork
      _model.followsQuasistaticEquilibriumPath .oneToTwo
      (_figure.everyLegIsStraight .oneToTwo)
    norm_num [CycleLeg.start, CycleLeg.finish, hP₁, hP₂, hV₁, hV₂] at h
    exact h
  have hW₂₃ :
      energyInJoules (setup.workDoneByGasOnLeg .twoToThree) = 0 := by
    have h := _laws.straightSegmentBoundaryWork
      _model.followsQuasistaticEquilibriumPath .twoToThree
      (_figure.everyLegIsStraight .twoToThree)
    simpa [CycleLeg.start, CycleLeg.finish, hP₂, hP₃, hV₂, hV₃] using h
  have hW₃₁ :
      energyInJoules (setup.workDoneByGasOnLeg .threeToOne) = -10000 := by
    have h := _laws.straightSegmentBoundaryWork
      _model.followsQuasistaticEquilibriumPath .threeToOne
      (_figure.everyLegIsStraight .threeToOne)
    norm_num [CycleLeg.start, CycleLeg.finish, hP₁, hP₃, hV₁, hV₃] at h
    exact h
  have hQ₁₂ :
      energyInJoules (setup.heatTransferredIntoGasOnLeg .oneToTwo) = 42500 := by
    have h := _laws.firstLawOnEachLeg .oneToTwo
    norm_num [CycleLeg.start, CycleLeg.finish, hU₁, hU₂, hW₁₂] at h
    exact h
  have hQ₂₃ :
      energyInJoules (setup.heatTransferredIntoGasOnLeg .twoToThree) = -15000 := by
    have h := _laws.firstLawOnEachLeg .twoToThree
    norm_num [CycleLeg.start, CycleLeg.finish, hU₂, hU₃, hW₂₃] at h
    exact h
  have hQ₃₁ :
      energyInJoules (setup.heatTransferredIntoGasOnLeg .threeToOne) = -25000 := by
    have h := _laws.firstLawOnEachLeg .threeToOne
    norm_num [CycleLeg.start, CycleLeg.finish, hU₁, hU₃, hW₃₁] at h
    exact h
  have hWnet : netWorkByGasInJoules setup = 2500 := by
    norm_num [netWorkByGasInJoules, hW₁₂, hW₂₃, hW₃₁]
  have hQin : totalHeatInputInJoules setup = 42500 := by
    simp [totalHeatInputInJoules, positiveHeatInJoules, hQ₁₂, hQ₂₃, hQ₃₁]
  exact
    ⟨hU₁, hU₂, hU₃, hW₁₂, hW₂₃, hW₃₁, hQ₁₂, hQ₂₃, hQ₃₁, hWnet, hQin⟩

/-! ## Displayed answer choices and main target -/

/-- Labels of the four efficiency choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless decimal value printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 6 / 25
  | .B => 83 / 1000
  | .C => 1 / 2
  | .D => 59 / 1000

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Agreement with an efficiency displayed to the nearest thousandth. -/
def MatchesDisplayedEfficiency
    (setup : HeatEngineCycleSetup) (choice : AnswerChoice) : Prop :=
  |thermalEfficiency setup - displayedEfficiency choice| < (1 / 2000 : ℝ)

/-- The specified label is the unique nearest-thousandth match. -/
def IsUniqueMatchingDisplayedEfficiency
    (setup : HeatEngineCycleSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedEfficiency setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedEfficiency setup other → other = choice

/-!
The rising leg absorbs `42500 J`, while the triangular clockwise cycle
produces `2500 J` of net work.  Hence

`η = W_net / Q_in = 2500 / 42500 = 1/17 ≈ 0.058824`,

which rounds to `0.059` and uniquely selects recorded answer D.

Blueprint label: `thm:physics:phyx_mini_0433:target`.
-/
theorem problem_phyx_mini_0433
    (setup : HeatEngineCycleSetup)
    (_scenario : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_model : UsesClosedQuasistaticCycleModel setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_laws : SatisfiesMonatomicIdealGasCycleLaws setup) :
    thermalEfficiency setup = (1 / 17 : ℝ) ∧
      IsUniqueMatchingDisplayedEfficiency setup recordedAnswerChoice := by
  obtain
    ⟨_, _, _, _, _, _, _, _, _, hWnet, hQin⟩ :=
      cycleEnergyAccounting setup _scenario _figure _model _laws
  have hEfficiency : thermalEfficiency setup = (1 / 17 : ℝ) := by
    norm_num [thermalEfficiency, hWnet, hQin]
  refine ⟨hEfficiency, ?_⟩
  constructor
  · norm_num [MatchesDisplayedEfficiency, recordedAnswerChoice,
      displayedEfficiency, hEfficiency]
  · intro other hother
    cases other with
    | A =>
        norm_num [MatchesDisplayedEfficiency, displayedEfficiency,
          hEfficiency] at hother
    | B =>
        norm_num [MatchesDisplayedEfficiency, displayedEfficiency,
          hEfficiency] at hother
    | C =>
        norm_num [MatchesDisplayedEfficiency, displayedEfficiency,
          hEfficiency] at hother
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0433
