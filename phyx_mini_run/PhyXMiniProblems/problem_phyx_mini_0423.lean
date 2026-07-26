import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0423

open Dimension

/-!
# Coefficient of performance of a refrigerator cycle

The primary figure is a pressure--volume diagram of a counterclockwise
four-leg refrigerator cycle.  Its upper and lower curves are adiabats.  With
work positive when done by the working substance, the diagram gives
`-119 J` on the upper adiabat and `78 J` on the lower adiabat.  The left
constant-volume leg rejects `105 J` of heat.

Energy, work, heat, pressure, and volume are represented by dimensionful
Physlib quantities.  Real numbers are used only for readouts in named SI units
and for the dimensionless coefficient of performance.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- Physical volume, represented as a dimensionful quantity of dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Read a physical energy as a signed number of joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a physical pressure as a signed number of pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical volume as a signed number of cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-! ## Directed cycle and figure vocabulary -/

/--
The four unlabeled corners of the supplied diagram, named by their drawn
positions.  The directed cycle is
`upperRight → upperLeft → lowerLeft → lowerRight → upperRight`.
-/
inductive CyclePoint where
  | upperLeft
  | lowerLeft
  | lowerRight
  | upperRight
  deriving DecidableEq, Repr

/-- The four directed legs of the refrigerator cycle. -/
inductive CycleLeg where
  | upperAdiabat
  | leftIsochore
  | lowerAdiabat
  | rightIsochore
  deriving DecidableEq, Repr

/-- Initial point of each directed leg. -/
def startPoint : CycleLeg → CyclePoint
  | .upperAdiabat => .upperRight
  | .leftIsochore => .upperLeft
  | .lowerAdiabat => .lowerLeft
  | .rightIsochore => .lowerRight

/-- Final point of each directed leg. -/
def endPoint : CycleLeg → CyclePoint
  | .upperAdiabat => .upperLeft
  | .leftIsochore => .lowerLeft
  | .lowerAdiabat => .lowerRight
  | .rightIsochore => .upperRight

/-- Process classifications visible in the pressure--volume diagram. -/
inductive ProcessKind where
  | adiabatic
  | isochoric
  deriving DecidableEq, Repr

/-- Physical quantity denoted by an axis label in the supplied figure. -/
inductive AxisLabel where
  | pressureP
  | volumeV
  deriving DecidableEq, Repr

/-- Direction of the purple `105 J` heat arrow relative to the working substance. -/
inductive HeatArrowDirection where
  | outOfWorkingSubstance
  | intoWorkingSubstance
  deriving DecidableEq, Repr

/-- The symbol printed beside the two signed work readouts. -/
inductive WorkLabel where
  | Ws
  deriving DecidableEq, Repr

/-- Sign conventions used for all energy readouts in the model. -/
inductive EnergySignConvention where
  | heatIntoAndWorkBySystemPositive
  deriving DecidableEq, Repr

/-- The role of the cyclic device in the question. -/
inductive DeviceKind where
  | refrigerator
  deriving DecidableEq, Repr

/-- A thermodynamic state carrying dimensionful pressure and volume. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : GasVolume

/--
Qualitative labels and arrows transcribed from the primary raster image.  The
direction of an arrow on a leg is the direction already encoded by `CycleLeg`.
-/
structure RefrigeratorPVDiagram where
  showsPoint : CyclePoint → Bool
  showsArrowOnLeg : CycleLeg → Bool
  drawnProcessKind : CycleLeg → ProcessKind
  verticalAxisLabel : AxisLabel
  horizontalAxisLabel : AxisLabel
  showsAdiabatsLabel : Bool
  showsWorkReadoutOnLeg : CycleLeg → Bool
  workReadoutLabel : WorkLabel
  shows105JHeatArrow : Bool
  heatArrowLeg : CycleLeg
  heatArrowDirection : HeatArrowDirection

/-! ## Independent setup and assumption interfaces -/

/--
Independent physical quantities for the refrigerator cycle.  `heatIntoSystem`
is positive into the working substance and `workDoneBySystem` is positive when
done by it.  `cycleWorkInput` and `coldReservoirHeatAbsorbed` are positive
energy magnitudes.  The dimensionless COP is an independent field rather than
a definition equal to the requested answer.
-/
structure RefrigeratorCycleSetup where
  figure : RefrigeratorPVDiagram
  deviceKind : DeviceKind
  signConvention : EnergySignConvention
  state : CyclePoint → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  heatIntoSystem : CycleLeg → DimEnergy
  workDoneBySystem : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  cycleWorkInput : DimEnergy
  coldReservoirHeatAbsorbed : DimEnergy
  coefficientOfPerformance : ℝ

/-- Scenario facts and branch conditions, excluding every requested numerical value. -/
structure MatchesProblemScenario (setup : RefrigeratorCycleSetup) : Prop where
  deviceIsRefrigerator : setup.deviceKind = .refrigerator
  signedReadoutConvention :
    setup.signConvention = .heatIntoAndWorkBySystemPositive
  workInputPositive : 0 < energyInJoules setup.cycleWorkInput
  coldReservoirHeatPositive :
    0 < energyInJoules setup.coldReservoirHeatAbsorbed
  coefficientOfPerformanceNonnegative :
    0 ≤ setup.coefficientOfPerformance

/-!
Numerical and qualitative evidence read from the primary image.  The purple
arrow points out of the working substance, so under the setup sign convention
its `105 J` label is recorded as a positive rejected-heat magnitude.
-/
structure MatchesPrimaryFigure (setup : RefrigeratorCycleSetup) : Prop where
  everyPointShown : ∀ point, setup.figure.showsPoint point = true
  everyArrowShown : ∀ leg, setup.figure.showsArrowOnLeg leg = true
  pressureOnVerticalAxis : setup.figure.verticalAxisLabel = .pressureP
  volumeOnHorizontalAxis : setup.figure.horizontalAxisLabel = .volumeV
  adiabatsLabelShown : setup.figure.showsAdiabatsLabel = true
  processKindsAgree : ∀ leg,
    setup.processKind leg = setup.figure.drawnProcessKind leg
  upperCurveIsAdiabatic :
    setup.figure.drawnProcessKind .upperAdiabat = .adiabatic
  leftBranchIsIsochoric :
    setup.figure.drawnProcessKind .leftIsochore = .isochoric
  lowerCurveIsAdiabatic :
    setup.figure.drawnProcessKind .lowerAdiabat = .adiabatic
  rightBranchIsIsochoric :
    setup.figure.drawnProcessKind .rightIsochore = .isochoric
  leftBranchHasConstantVolume :
    (setup.state .upperLeft).volume = (setup.state .lowerLeft).volume
  rightBranchHasConstantVolume :
    (setup.state .lowerRight).volume = (setup.state .upperRight).volume
  leftVolumeLessThanRightVolume :
    volumeInCubicMeters (setup.state .upperLeft).volume <
      volumeInCubicMeters (setup.state .upperRight).volume
  leftUpperPressureGreater :
    pressureInPascals (setup.state .lowerLeft).pressure <
      pressureInPascals (setup.state .upperLeft).pressure
  rightUpperPressureGreater :
    pressureInPascals (setup.state .lowerRight).pressure <
      pressureInPascals (setup.state .upperRight).pressure
  workSymbolIsWs : setup.figure.workReadoutLabel = .Ws
  upperWorkReadoutShown :
    setup.figure.showsWorkReadoutOnLeg .upperAdiabat = true
  lowerWorkReadoutShown :
    setup.figure.showsWorkReadoutOnLeg .lowerAdiabat = true
  upperAdiabatWorkReadout :
    energyInJoules (setup.workDoneBySystem .upperAdiabat) = -119
  lowerAdiabatWorkReadout :
    energyInJoules (setup.workDoneBySystem .lowerAdiabat) = 78
  heatArrowShown : setup.figure.shows105JHeatArrow = true
  heatArrowOnLeftIsochore : setup.figure.heatArrowLeg = .leftIsochore
  heatArrowPointsOutward :
    setup.figure.heatArrowDirection = .outOfWorkingSubstance
  rejectedHeatMagnitudeReadout :
    -energyInJoules (setup.heatIntoSystem .leftIsochore) = 105

/-!
Governing thermodynamic laws for the directed cycle, stated in coherent joule
readouts:

* `ΔU = Q - W` on each leg;
* total internal-energy change vanishes on returning to the initial state;
* adiabatic legs exchange no heat and isochoric legs do no boundary work;
* work input is the negative of net work done by the working substance;
* cold-reservoir heat is the heat entering on the right isochore;
* `COP · W_in = Q_cold`.

None of these laws fixes `W_in`, `Q_cold`, the COP, or an answer choice to the
numerical values requested in the current question.
-/
structure SatisfiesRefrigeratorCycleLaws
    (setup : RefrigeratorCycleSetup) : Prop where
  firstLaw : ∀ leg,
    energyInJoules (setup.internalEnergyChange leg) =
      energyInJoules (setup.heatIntoSystem leg) -
        energyInJoules (setup.workDoneBySystem leg)
  internalEnergyClosesOverCycle :
    energyInJoules (setup.internalEnergyChange .upperAdiabat) +
          energyInJoules (setup.internalEnergyChange .leftIsochore) +
        energyInJoules (setup.internalEnergyChange .lowerAdiabat) +
      energyInJoules (setup.internalEnergyChange .rightIsochore) = 0
  adiabaticHeatIsZero : ∀ leg,
    setup.processKind leg = .adiabatic →
      energyInJoules (setup.heatIntoSystem leg) = 0
  isochoricWorkIsZero : ∀ leg,
    setup.processKind leg = .isochoric →
      energyInJoules (setup.workDoneBySystem leg) = 0
  workInputBalance :
    energyInJoules setup.cycleWorkInput =
      -(energyInJoules (setup.workDoneBySystem .upperAdiabat) +
            energyInJoules (setup.workDoneBySystem .leftIsochore) +
          energyInJoules (setup.workDoneBySystem .lowerAdiabat) +
        energyInJoules (setup.workDoneBySystem .rightIsochore))
  coldReservoirHeatBalance :
    energyInJoules setup.coldReservoirHeatAbsorbed =
      energyInJoules (setup.heatIntoSystem .rightIsochore)
  coefficientOfPerformanceDefinition :
    setup.coefficientOfPerformance *
        energyInJoules setup.cycleWorkInput =
      energyInJoules setup.coldReservoirHeatAbsorbed

/-! ## Derived quantities and multiple-choice target -/

/-- Labels of the four answer choices displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless coefficient printed by each displayed answer choice. -/
def answerCoefficientOfPerformance : AnswerChoice → ℝ
  | .A => 29 / 10
  | .B => 61 / 100
  | .C => 64 / 25
  | .D => 8 / 5

/-- Dataset metadata records answer D; this definition is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A real value rounds to the displayed coefficient at one decimal place. -/
def RoundsToDisplayedTenth (value displayed : ℝ) : Prop :=
  |value - displayed| < 1 / 20

/-- A coefficient is strictly closer to one choice than to every other choice. -/
def IsUniqueClosestDisplayedAnswer
    (value : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |value - answerCoefficientOfPerformance choice| <
      |value - answerCoefficientOfPerformance other|

/-- The two signed adiabatic works give a work input of `41 J` per cycle. -/
theorem cycle_work_input_in_joules
    (setup : RefrigeratorCycleSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_laws : SatisfiesRefrigeratorCycleLaws setup) :
    energyInJoules setup.cycleWorkInput = 41 := by
  have hLeftKind : setup.processKind .leftIsochore = .isochoric :=
    (_figure.processKindsAgree .leftIsochore).trans
      _figure.leftBranchIsIsochoric
  have hRightKind : setup.processKind .rightIsochore = .isochoric :=
    (_figure.processKindsAgree .rightIsochore).trans
      _figure.rightBranchIsIsochoric
  have hLeftWork :
      energyInJoules (setup.workDoneBySystem .leftIsochore) = 0 :=
    _laws.isochoricWorkIsZero .leftIsochore hLeftKind
  have hRightWork :
      energyInJoules (setup.workDoneBySystem .rightIsochore) = 0 :=
    _laws.isochoricWorkIsZero .rightIsochore hRightKind
  rw [_laws.workInputBalance, _figure.upperAdiabatWorkReadout,
    hLeftWork, _figure.lowerAdiabatWorkReadout, hRightWork]
  norm_num

/-- The first law then gives `64 J` absorbed from the cold reservoir. -/
theorem cold_reservoir_heat_absorbed_in_joules
    (setup : RefrigeratorCycleSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_laws : SatisfiesRefrigeratorCycleLaws setup) :
    energyInJoules setup.coldReservoirHeatAbsorbed = 64 := by
  have hUpperKind : setup.processKind .upperAdiabat = .adiabatic :=
    (_figure.processKindsAgree .upperAdiabat).trans
      _figure.upperCurveIsAdiabatic
  have hLeftKind : setup.processKind .leftIsochore = .isochoric :=
    (_figure.processKindsAgree .leftIsochore).trans
      _figure.leftBranchIsIsochoric
  have hLowerKind : setup.processKind .lowerAdiabat = .adiabatic :=
    (_figure.processKindsAgree .lowerAdiabat).trans
      _figure.lowerCurveIsAdiabatic
  have hRightKind : setup.processKind .rightIsochore = .isochoric :=
    (_figure.processKindsAgree .rightIsochore).trans
      _figure.rightBranchIsIsochoric
  have hUpperHeat :
      energyInJoules (setup.heatIntoSystem .upperAdiabat) = 0 :=
    _laws.adiabaticHeatIsZero .upperAdiabat hUpperKind
  have hLowerHeat :
      energyInJoules (setup.heatIntoSystem .lowerAdiabat) = 0 :=
    _laws.adiabaticHeatIsZero .lowerAdiabat hLowerKind
  have hLeftWork :
      energyInJoules (setup.workDoneBySystem .leftIsochore) = 0 :=
    _laws.isochoricWorkIsZero .leftIsochore hLeftKind
  have hRightWork :
      energyInJoules (setup.workDoneBySystem .rightIsochore) = 0 :=
    _laws.isochoricWorkIsZero .rightIsochore hRightKind
  have hLeftHeat :
      energyInJoules (setup.heatIntoSystem .leftIsochore) = -105 := by
    linarith [_figure.rejectedHeatMagnitudeReadout]
  have hUpperFirstLaw := _laws.firstLaw .upperAdiabat
  have hLeftFirstLaw := _laws.firstLaw .leftIsochore
  have hLowerFirstLaw := _laws.firstLaw .lowerAdiabat
  have hRightFirstLaw := _laws.firstLaw .rightIsochore
  have hRightHeat :
      energyInJoules (setup.heatIntoSystem .rightIsochore) = 64 := by
    linarith [_laws.internalEnergyClosesOverCycle,
      _figure.upperAdiabatWorkReadout,
      _figure.lowerAdiabatWorkReadout]
  exact _laws.coldReservoirHeatBalance.trans hRightHeat

/-- The exact dimensionless refrigerator COP is `Q_cold / W_in = 64 / 41`. -/
theorem refrigerator_coefficient_of_performance_exact
    (setup : RefrigeratorCycleSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_laws : SatisfiesRefrigeratorCycleLaws setup) :
    setup.coefficientOfPerformance = (64 / 41 : ℝ) := by
  have hWork := cycle_work_input_in_joules setup _scenario _figure _laws
  have hCold :=
    cold_reservoir_heat_absorbed_in_joules setup _scenario _figure _laws
  have hCOP := _laws.coefficientOfPerformanceDefinition
  rw [hWork, hCold] at hCOP
  norm_num at hCOP ⊢
  linarith

/-!
The cycle has exact COP `64/41 ≈ 1.56`, which rounds to `1.6` and is uniquely
answer D among the displayed choices.

This formalizes blueprint label `thm:physics:phyx_mini_0423:target`.
-/
theorem refrigerator_coefficient_of_performance
    (setup : RefrigeratorCycleSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_laws : SatisfiesRefrigeratorCycleLaws setup) :
    energyInJoules setup.cycleWorkInput = 41 ∧
      energyInJoules setup.coldReservoirHeatAbsorbed = 64 ∧
      setup.coefficientOfPerformance = (64 / 41 : ℝ) ∧
      RoundsToDisplayedTenth setup.coefficientOfPerformance
        (answerCoefficientOfPerformance .D) ∧
      IsUniqueClosestDisplayedAnswer setup.coefficientOfPerformance .D := by
  have hWork := cycle_work_input_in_joules setup _scenario _figure _laws
  have hCold :=
    cold_reservoir_heat_absorbed_in_joules setup _scenario _figure _laws
  have hCOP :=
    refrigerator_coefficient_of_performance_exact
      setup _scenario _figure _laws
  refine ⟨hWork, hCold, hCOP, ?_, ?_⟩
  · rw [hCOP]
    norm_num [RoundsToDisplayedTenth, answerCoefficientOfPerformance,
      abs_of_nonpos]
  · rw [hCOP]
    intro other hOther
    cases other with
    | A =>
        norm_num [answerCoefficientOfPerformance, abs_of_nonpos,
          abs_of_nonneg]
    | B =>
        norm_num [answerCoefficientOfPerformance, abs_of_nonpos,
          abs_of_nonneg]
    | C =>
        norm_num [answerCoefficientOfPerformance, abs_of_nonpos,
          abs_of_nonneg]
    | D => exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0423
