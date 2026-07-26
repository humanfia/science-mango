import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0492

open Dimension

/-!
# Work done in a two-step ideal-gas process

The primary pressure--volume diagram shows the directed path `a → b → c`.
The gas first cools at constant volume from `2.2 atm` to `1.4 atm`, then
expands at `1.4 atm` from `5.9 L` to `9.3 L`.  At `c` its temperature has
returned to the temperature at `a`.

Pressure, volume, temperature, heat, and work retain their physical roles.
Real numbers below are only readouts in atmospheres, litres, or joules, or
displayed multiple-choice values.  Heat is positive into the gas and work is
positive when done by the gas.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical gas volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a pressure in the standard atmospheres printed on the diagram. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in the litres printed on the diagram. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read signed heat or work in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- The exact number of joules represented by one litre-atmosphere. -/
def joulesPerLiterAtmosphere : ℝ :=
  pressureInPascals DimPressure.standardAtmosphere / 1000

/-! ## Gas, process, state, and primary-figure vocabulary -/

/-- Equation-of-state model specified by the phrase “ideal gas”. -/
inductive GasModel where
  | idealGas
  deriving DecidableEq, Repr

/-- The three point labels printed in the pressure--volume diagram. -/
inductive FigurePoint where
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Repr

/-- The two directed process legs shown by red arrows. -/
inductive ProcessLeg where
  | aToB
  | bToC
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint of each directed process leg. -/
def ProcessLeg.initialPoint : ProcessLeg → FigurePoint
  | .aToB => .a
  | .bToC => .b

/-- Final endpoint of each directed process leg. -/
def ProcessLeg.finalPoint : ProcessLeg → FigurePoint
  | .aToB => .b
  | .bToC => .c

/-- Thermodynamic constraint imposed on each process leg. -/
inductive ProcessKind where
  | constantVolumeCooling
  | constantPressureExpansion
  deriving DecidableEq, Repr

/-- Geometric appearance of a process leg in the pressure--volume plane. -/
inductive SegmentGeometry where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Physical quantity assigned to one of the plot axes. -/
inductive AxisQuantity where
  | pressureP
  | volumeV
  deriving DecidableEq, Repr

/-- Unit printed beside an axis of the diagram. -/
inductive AxisUnit where
  | atmosphere
  | liter
  deriving DecidableEq, Repr

/-- The red comparison curve through `a` and `c`. -/
inductive ComparisonCurveKind where
  | equalTemperatureIdealGasCurve
  deriving DecidableEq, Repr

/-- Sign conventions used for the directed energy transfers. -/
inductive EnergySignConvention where
  | heatIntoGasAndWorkByGasPositive
  deriving DecidableEq, Repr

/-- Pressure, volume, and absolute temperature at one labeled state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Qualitative content transcribed from the primary bitmap.  Numerical state
coordinates remain in the physical states and are recorded separately by
`MatchesPrimaryPressureVolumeFigure`.
-/
structure PressureVolumeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisUnit : AxisUnit
  showsPoint : FigurePoint → Bool
  showsPointLabel : FigurePoint → Bool
  showsArrowOnLeg : ProcessLeg → Bool
  directedEndpoints : ProcessLeg → FigurePoint × FigurePoint
  segmentGeometry : ProcessLeg → SegmentGeometry
  showsDashedPressureGuide : FigurePoint → Bool
  showsDashedVolumeGuide : FigurePoint → Bool
  showsRedComparisonCurve : Bool
  comparisonCurveKind : ComparisonCurveKind
  pointLiesOnComparisonCurve : FigurePoint → Bool

/-!
Independent physical quantities for the same closed gas sample.  In
particular, `totalWorkDoneByGas` is an independent dimensionful observable;
it is not defined to be the requested numerical answer.
-/
structure TwoStepIdealGasProcess where
  gasModel : GasModel
  sameClosedGasSample : Bool
  signConvention : EnergySignConvention
  stateAt : FigurePoint → ThermodynamicState
  processKind : ProcessLeg → ProcessKind
  heatTransferredIntoGas : ProcessLeg → DimEnergy
  workDoneByGas : ProcessLeg → DimEnergy
  totalWorkDoneByGas : DimEnergy
  figure : PressureVolumeFigure

/-! ## Problem statement, figure readouts, and physical laws -/

/-!
Facts stated in the prose.  The strict negative heat readout encodes heat
flow out of the gas under the declared sign convention.  No work value or
answer choice occurs here.
-/
structure MatchesProblemStatement (setup : TwoStepIdealGasProcess) : Prop where
  gasIsIdeal : setup.gasModel = .idealGas
  processUsesOneClosedSample : setup.sameClosedGasSample = true
  signsAreHeatInAndWorkByGasPositive :
    setup.signConvention = .heatIntoGasAndWorkByGasPositive
  firstLegIsConstantVolumeCooling :
    setup.processKind .aToB = .constantVolumeCooling
  secondLegIsConstantPressureExpansion :
    setup.processKind .bToC = .constantPressureExpansion
  heatFlowsOutOnFirstLeg :
    energyInJoules (setup.heatTransferredIntoGas .aToB) < 0
  finalTemperatureReturnsToOriginal :
    (setup.stateAt .c).temperature = (setup.stateAt .a).temperature

/-!
Exact transcription of the supplied pressure--volume bitmap.  The red curve
passes through `a` and `c`; the actual process instead follows the vertical
arrow `a → b` and the horizontal arrow `b → c`.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : TwoStepIdealGasProcess) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volumeV
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressureP
  horizontalAxisUsesLiters : setup.figure.horizontalAxisUnit = .liter
  verticalAxisUsesAtmospheres :
    setup.figure.verticalAxisUnit = .atmosphere
  everyPointIsShown : ∀ point, setup.figure.showsPoint point = true
  everyPointLabelIsShown :
    ∀ point, setup.figure.showsPointLabel point = true
  everyProcessArrowIsShown :
    ∀ leg, setup.figure.showsArrowOnLeg leg = true
  arrowsHaveDirectedEndpoints : ∀ leg,
    setup.figure.directedEndpoints leg =
      (leg.initialPoint, leg.finalPoint)
  firstLegIsVertical :
    setup.figure.segmentGeometry .aToB = .vertical
  secondLegIsHorizontal :
    setup.figure.segmentGeometry .bToC = .horizontal
  pressureGuideAtAIsShown :
    setup.figure.showsDashedPressureGuide .a = true
  pressureGuideAtBIsShown :
    setup.figure.showsDashedPressureGuide .b = true
  volumeGuideAtBIsShown :
    setup.figure.showsDashedVolumeGuide .b = true
  volumeGuideAtCIsShown :
    setup.figure.showsDashedVolumeGuide .c = true
  redComparisonCurveIsShown : setup.figure.showsRedComparisonCurve = true
  redCurveRepresentsEqualTemperatureStates :
    setup.figure.comparisonCurveKind = .equalTemperatureIdealGasCurve
  pointAIsOnRedCurve : setup.figure.pointLiesOnComparisonCurve .a = true
  pointBIsNotOnRedCurve :
    setup.figure.pointLiesOnComparisonCurve .b = false
  pointCIsOnRedCurve : setup.figure.pointLiesOnComparisonCurve .c = true
  pressureAtAAtmospheres :
    pressureInAtmospheres (setup.stateAt .a).pressure = (11 : ℝ) / 5
  pressureAtBAtmospheres :
    pressureInAtmospheres (setup.stateAt .b).pressure = (7 : ℝ) / 5
  pressureAtCAtmospheres :
    pressureInAtmospheres (setup.stateAt .c).pressure = (7 : ℝ) / 5
  volumeAtALiters :
    volumeInLiters (setup.stateAt .a).volume = (59 : ℝ) / 10
  volumeAtBLiters :
    volumeInLiters (setup.stateAt .b).volume = (59 : ℝ) / 10
  volumeAtCLiters :
    volumeInLiters (setup.stateAt .c).volume = (93 : ℝ) / 10

/-- Positivity and nondegeneracy conditions for the physical process. -/
structure HasPhysicalThermodynamicParameters
    (setup : TwoStepIdealGasProcess) : Prop where
  pressurePositive : ∀ point,
    0 < pressureInAtmospheres (setup.stateAt point).pressure
  volumePositive : ∀ point,
    0 < volumeInLiters (setup.stateAt point).volume
  absoluteTemperaturePositive : ∀ point,
    0 < (setup.stateAt point).temperature.val
  secondLegExpands :
    volumeInLiters (setup.stateAt .b).volume <
      volumeInLiters (setup.stateAt .c).volume

/-!
General boundary-work laws for the two process kinds, written in the named
units of the diagram.  A constant-volume leg does no boundary work, while a
constant-pressure expansion does `P ΔV` work.  These laws contain none of the
problem's numerical coordinates or answer values.
-/
structure SatisfiesBoundaryWorkLaws
    (setup : TwoStepIdealGasProcess) : Prop where
  constantVolumeWorkIsZero : ∀ leg,
    setup.processKind leg = .constantVolumeCooling →
      energyInJoules (setup.workDoneByGas leg) = 0
  constantPressureEndpointsAgree : ∀ leg,
    setup.processKind leg = .constantPressureExpansion →
      (setup.stateAt leg.initialPoint).pressure =
        (setup.stateAt leg.finalPoint).pressure
  constantPressureBoundaryWork : ∀ leg,
    setup.processKind leg = .constantPressureExpansion →
      energyInJoules (setup.workDoneByGas leg) =
        pressureInAtmospheres
            (setup.stateAt leg.initialPoint).pressure *
          (volumeInLiters (setup.stateAt leg.finalPoint).volume -
            volumeInLiters (setup.stateAt leg.initialPoint).volume) *
          joulesPerLiterAtmosphere
  totalWorkIsSumOfLegs :
    energyInJoules setup.totalWorkDoneByGas =
      energyInJoules (setup.workDoneByGas .aToB) +
        energyInJoules (setup.workDoneByGas .bToC)

/-! ## Requested work and displayed answer -/

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Work in joules printed beside each answer label. -/
def AnswerChoice.workInJoules : AnswerChoice → ℝ
  | .A => 390
  | .B => 420
  | .C => 450
  | .D => 480

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- The answer choices report work to the nearest ten joules. -/
def RoundsToNearestTenJoules (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 5

/-!
The first leg contributes no work.  On the second leg,

`W = (1.4 atm) (9.3 L - 5.9 L) = 482.307 J`.

Thus the reported total work is `480 J`, the unique listed value within the
nearest-ten-joule window, and hence recorded answer D.

Blueprint label: `thm:physics:phyx_mini_0492:target`.
-/
theorem totalWorkDoneByGas_matches_recordedAnswerD
    (setup : TwoStepIdealGasProcess)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_workLaws : SatisfiesBoundaryWorkLaws setup) :
    energyInJoules setup.totalWorkDoneByGas = (482307 : ℝ) / 1000 ∧
      RoundsToNearestTenJoules
        (energyInJoules setup.totalWorkDoneByGas)
        recordedAnswerChoice.workInJoules ∧
      ∀ choice : AnswerChoice,
        RoundsToNearestTenJoules
            (energyInJoules setup.totalWorkDoneByGas)
            choice.workInJoules →
          choice = recordedAnswerChoice := by
  have hConversion :
      joulesPerLiterAtmosphere = (101325 : ℝ) / 1000 := by
    norm_num [joulesPerLiterAtmosphere, pressureInPascals,
      DimPressure.standardAtmosphere, DimPressure.pascal,
      CarriesDimension.toDimensionful_apply_apply]
  have hFirst :=
    _workLaws.constantVolumeWorkIsZero .aToB
      _problem.firstLegIsConstantVolumeCooling
  have hSecond :=
    _workLaws.constantPressureBoundaryWork .bToC
      _problem.secondLegIsConstantPressureExpansion
  simp only [ProcessLeg.initialPoint, ProcessLeg.finalPoint] at hSecond
  rw [_figure.pressureAtBAtmospheres, _figure.volumeAtCLiters,
    _figure.volumeAtBLiters] at hSecond
  rw [_workLaws.totalWorkIsSumOfLegs, hFirst, hSecond, hConversion]
  norm_num [RoundsToNearestTenJoules, recordedAnswerChoice,
    AnswerChoice.workInJoules, abs_of_nonneg, abs_of_neg]
  intro choice
  cases choice <;>
    norm_num [RoundsToNearestTenJoules, recordedAnswerChoice,
      AnswerChoice.workInJoules, abs_of_nonneg, abs_of_neg]

end PhyXMiniProblems.ProblemPhyXMini0492
