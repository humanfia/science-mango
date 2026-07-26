import Mathlib.Data.Real.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0422

open Dimension

/-!
# Thermal efficiency of a triangular pressure--volume heat-engine cycle

The supplied image shows a clockwise triangular cycle with vertices
`(200 cm³, 100 kPa)`, `(600 cm³, 300 kPa)`, and `(600 cm³, 100 kPa)`.
The auxiliary caption's right-hand volume of `400 cm³` is a transcription
error; the primary image shows `600 cm³`.  The image also contains outward
energy-transfer arrows labelled `180 J` and `100 J`, interpreted by the
problem as heat rejected to the cold reservoir.

Pressure, volume, work, and heat are dimensionful physical quantities.  Real
numbers below are used only as readouts in named units, dimensionless
efficiencies, coordinates, and displayed answer-choice values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a dimensionful pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in the cubic centimetres printed on the graph. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with
    length := LengthUnit.centimeters}).val : ℝ)

/-- Read dimensionful work or heat in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Cycle states, directed legs, and primary-figure labels -/

/-- The three black vertices visible in the supplied image. -/
inductive CycleState where
  | leftLow
  | rightHigh
  | rightLow
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs, in the order shown by the black arrows. -/
inductive CycleLeg where
  | rising
  | verticalDown
  | horizontalLeft
  deriving DecidableEq, Fintype, Repr

/-- Starting vertex of each directed process leg. -/
def legStart : CycleLeg → CycleState
  | .rising => .leftLow
  | .verticalDown => .rightHigh
  | .horizontalLeft => .rightLow

/-- Finishing vertex of each directed process leg. -/
def legFinish : CycleLeg → CycleState
  | .rising => .rightHigh
  | .verticalDown => .rightLow
  | .horizontalLeft => .leftLow

/-- The two axes in the pressure--volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity represented by a figure axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside a figure axis. -/
inductive AxisUnit where
  | cubicCentimeter
  | kilopascal
  deriving DecidableEq, Repr

/-- Geometric appearance of a process leg in the `p`--`V` plane. -/
inductive PVPathShape where
  | risingStraightSegment
  | verticalStraightSegment
  | horizontalStraightSegment
  deriving DecidableEq, Repr

/-- Direction on the page of a purple energy-transfer arrow. -/
inductive PageArrowDirection where
  | right
  | down
  deriving DecidableEq, Repr

/-- The two labelled rejected-heat markers in the primary image. -/
inductive RejectedHeatMarker where
  | rightward180J
  | downward100J
  deriving DecidableEq, Fintype, Repr

/-- The process leg crossed by each rejected-heat marker. -/
def markerLeg : RejectedHeatMarker → CycleLeg
  | .rightward180J => .verticalDown
  | .downward100J => .horizontalLeft

/-- A pressure--volume equilibrium state of the working system. -/
structure PressureVolumeState where
  pressure : DimPressure
  volume : VolumeQuantity

/-- The graphical content of the supplied pressure--volume image. -/
structure HeatEnginePVFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisUnit : FigureAxis → AxisUnit
  printedTicks : FigureAxis → List ℝ
  coordinateInAxisUnits : CycleState → ℝ × ℝ
  showsVertex : CycleState → Bool
  arrowEndpoints : CycleLeg → CycleState × CycleState
  showsProcessArrow : CycleLeg → Bool
  pathShape : CycleLeg → PVPathShape
  energyMarkerLeg : RejectedHeatMarker → CycleLeg
  energyMarkerDirection : RejectedHeatMarker → PageArrowDirection
  showsEnergyMarker : RejectedHeatMarker → Bool
  printedEnergyInJoules : RejectedHeatMarker → ℝ

/-! ## Physical setup and assumption-side predicates -/

/-- The kind of cyclic thermodynamic device described in the question. -/
inductive ThermodynamicDeviceKind where
  | heatEngine
  | other
  deriving DecidableEq, Repr

/-- Physical regime in which straight plotted paths determine boundary work. -/
inductive ProcessRegime where
  | quasistaticPiecewiseLinear
  | other
  deriving DecidableEq, Repr

/-- Orientation of the directed closed loop in the `p`--`V` plane. -/
inductive CycleOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Thermodynamic interpretation assigned to a labelled energy arrow. -/
inductive EnergyTransferRole where
  | heatRejectedToColdReservoir
  | other
  deriving DecidableEq, Repr

/-!
Independent physical quantities for the cycle.  Net work, absorbed heat, and
the two rejected heat transfers are genuine dimensionful observables.  None
is defined from the requested efficiency or from an answer choice.
-/
structure TriangularHeatEngineSetup where
  deviceKind : ThermodynamicDeviceKind
  processRegime : ProcessRegime
  cycleOrientation : CycleOrientation
  stateAt : CycleState → PressureVolumeState
  workDoneByGasOnLeg : CycleLeg → DimEnergy
  netWorkDoneByGas : DimEnergy
  heatRejectedToColdReservoir : RejectedHeatMarker → DimEnergy
  heatAbsorbedFromHotReservoir : DimEnergy
  energyTransferRole : RejectedHeatMarker → EnergyTransferRole
  figure : HeatEnginePVFigure

/-- Qualitative heat-engine and sign interpretations supplied by the problem. -/
structure MatchesHeatEngineScenario
    (setup : TriangularHeatEngineSetup) : Prop where
  deviceIsHeatEngine : setup.deviceKind = .heatEngine
  processIsQuasistaticPiecewiseLinear :
    setup.processRegime = .quasistaticPiecewiseLinear
  cycleRunsClockwise : setup.cycleOrientation = .clockwise
  labelledTransfersAreRejectedHeat : ∀ marker,
    setup.energyTransferRole marker = .heatRejectedToColdReservoir

/-!
Exact evidence from the primary image.  These fields include the measured
rejected-heat readouts, but no net work, absorbed heat, efficiency, or
answer-choice conclusion.
-/
structure MatchesSuppliedHeatEngineFigure
    (setup : TriangularHeatEngineSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUsesCubicCentimeters :
    setup.figure.axisUnit .horizontal = .cubicCentimeter
  verticalAxisUsesKilopascals :
    setup.figure.axisUnit .vertical = .kilopascal
  horizontalTicks :
    setup.figure.printedTicks .horizontal = [0, 200, 400, 600]
  verticalTicks :
    setup.figure.printedTicks .vertical = [0, 100, 200, 300]
  leftLowCoordinate :
    setup.figure.coordinateInAxisUnits .leftLow = (200, 100)
  rightHighCoordinate :
    setup.figure.coordinateInAxisUnits .rightHigh = (600, 300)
  rightLowCoordinate :
    setup.figure.coordinateInAxisUnits .rightLow = (600, 100)
  coordinatesRepresentPhysicalStates : ∀ state,
    setup.figure.coordinateInAxisUnits state =
      (volumeInCubicCentimeters (setup.stateAt state).volume,
        pressureInKilopascals (setup.stateAt state).pressure)
  everyVertexShown : ∀ state, setup.figure.showsVertex state = true
  processArrowsFollowCycle : ∀ leg,
    setup.figure.arrowEndpoints leg = (legStart leg, legFinish leg)
  everyProcessArrowShown : ∀ leg,
    setup.figure.showsProcessArrow leg = true
  risingLegShape :
    setup.figure.pathShape .rising = .risingStraightSegment
  verticalLegShape :
    setup.figure.pathShape .verticalDown = .verticalStraightSegment
  horizontalLegShape :
    setup.figure.pathShape .horizontalLeft = .horizontalStraightSegment
  energyMarkersAttachToDisplayedLegs : ∀ marker,
    setup.figure.energyMarkerLeg marker = markerLeg marker
  marker180PointsRight :
    setup.figure.energyMarkerDirection .rightward180J = .right
  marker100PointsDown :
    setup.figure.energyMarkerDirection .downward100J = .down
  everyEnergyMarkerShown : ∀ marker,
    setup.figure.showsEnergyMarker marker = true
  marker180Readout :
    setup.figure.printedEnergyInJoules .rightward180J = 180
  marker100Readout :
    setup.figure.printedEnergyInJoules .downward100J = 100
  printedEnergiesRepresentRejectedHeat : ∀ marker,
    setup.figure.printedEnergyInJoules marker =
      energyInJoules (setup.heatRejectedToColdReservoir marker)

/-- Positivity conditions for physical states and heat-transfer magnitudes. -/
structure HasPhysicalHeatEngineParameters
    (setup : TriangularHeatEngineSetup) : Prop where
  pressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  volumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  rejectedHeatPositive : ∀ marker,
    0 < energyInJoules (setup.heatRejectedToColdReservoir marker)
  absorbedHeatPositive :
    0 < energyInJoules setup.heatAbsorbedFromHotReservoir

/-!
Governing thermodynamic laws for this model:

* each quasistatic straight leg has signed gas work equal to its trapezoid
  area under the `p`--`V` path;
* net cycle work is the sum of the three directed-leg works;
* the cyclic first law gives absorbed heat as net work plus rejected heat.

These laws contain none of the derived numerical work, absorbed heat,
efficiency, or answer label.
-/
structure SatisfiesTriangularHeatEngineLaws
    (setup : TriangularHeatEngineSetup) : Prop where
  straightLegBoundaryWork : ∀ leg,
    setup.processRegime = .quasistaticPiecewiseLinear →
      energyInJoules (setup.workDoneByGasOnLeg leg) =
        (pressureInPascals (setup.stateAt (legStart leg)).pressure +
            pressureInPascals (setup.stateAt (legFinish leg)).pressure) / 2 *
          (volumeInCubicMeters (setup.stateAt (legFinish leg)).volume -
            volumeInCubicMeters (setup.stateAt (legStart leg)).volume)
  netWorkIsLegSum :
    energyInJoules setup.netWorkDoneByGas =
      energyInJoules (setup.workDoneByGasOnLeg .rising) +
        energyInJoules (setup.workDoneByGasOnLeg .verticalDown) +
          energyInJoules (setup.workDoneByGasOnLeg .horizontalLeft)
  cyclicFirstLaw :
    energyInJoules setup.heatAbsorbedFromHotReservoir =
      energyInJoules setup.netWorkDoneByGas +
        energyInJoules
          (setup.heatRejectedToColdReservoir .rightward180J) +
        energyInJoules
          (setup.heatRejectedToColdReservoir .downward100J)

/-! ## Efficiency and displayed answer choices -/

/-- Dimensionless thermal efficiency `W_net / Q_hot`. -/
def thermalEfficiency (setup : TriangularHeatEngineSetup) : ℝ :=
  energyInJoules setup.netWorkDoneByGas /
    energyInJoules setup.heatAbsorbedFromHotReservoir

/-- Labels of the four answers displayed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless efficiency printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 14 / 100
  | .B => 10 / 100
  | .C => 75 / 100
  | .D => 13 / 100

/-- The answer metadata recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Membership in the half-open interval that rounds to a displayed hundredth
using the usual round-half-up convention.
-/
def RoundsToDisplayedHundredth (actual displayed : ℝ) : Prop :=
  displayed - 1 / 200 ≤ actual ∧ actual < displayed + 1 / 200

/-- The computed efficiency rounds to the value beside a displayed choice. -/
def IsRoundedEfficiencyAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedHundredth actual (displayedEfficiency choice)

/-- The specified choice is the unique displayed rounding match. -/
def IsUniqueRoundedEfficiencyAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  IsRoundedEfficiencyAnswer actual choice ∧
    ∀ other, IsRoundedEfficiencyAnswer actual other → other = choice

/-! ## Derived work, heat input, and current target -/

/-!
The clockwise triangular area gives `40 J` of net work done by the gas.  This
is a derived conclusion, not figure data or a governing-law premise.
-/
lemma netCycleWorkInJoules_eq_forty
    (setup : TriangularHeatEngineSetup)
    (hScenario : MatchesHeatEngineScenario setup)
    (hFigure : MatchesSuppliedHeatEngineFigure setup)
    (hLaws : SatisfiesTriangularHeatEngineLaws setup) :
    energyInJoules setup.netWorkDoneByGas = 40 := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hLengthScale :
      UnitChoices.SI.dimScale ucm L𝓭 = (100 : NNReal) := by
    apply NNReal.eq
    norm_num [ucm, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    rfl
  have hVolumeScale :
      UnitChoices.SI.dimScale ucm (L𝓭 * L𝓭 * L𝓭) =
        (1000000 : NNReal) := by
    rw [map_mul, map_mul, hLengthScale]
    norm_num
  have volumeConversion (volume : VolumeQuantity) :
      volumeInCubicCentimeters volume =
        1000000 * volumeInCubicMeters volume := by
    change ((volume ucm).val : ℝ) =
      1000000 * ((volume UnitChoices.SI).val : ℝ)
    rw [volume.2 UnitChoices.SI ucm]
    simp only [WithDim.dim_apply, hVolumeScale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have hLeft := hFigure.leftLowCoordinate
  rw [hFigure.coordinatesRepresentPhysicalStates .leftLow] at hLeft
  have hLeftVolumeCM :
      volumeInCubicCentimeters (setup.stateAt .leftLow).volume = 200 := by
    simpa using congrArg Prod.fst hLeft
  have hLeftPressureKPa :
      pressureInKilopascals (setup.stateAt .leftLow).pressure = 100 := by
    simpa using congrArg Prod.snd hLeft
  have hHigh := hFigure.rightHighCoordinate
  rw [hFigure.coordinatesRepresentPhysicalStates .rightHigh] at hHigh
  have hHighVolumeCM :
      volumeInCubicCentimeters (setup.stateAt .rightHigh).volume = 600 := by
    simpa using congrArg Prod.fst hHigh
  have hHighPressureKPa :
      pressureInKilopascals (setup.stateAt .rightHigh).pressure = 300 := by
    simpa using congrArg Prod.snd hHigh
  have hLow := hFigure.rightLowCoordinate
  rw [hFigure.coordinatesRepresentPhysicalStates .rightLow] at hLow
  have hLowVolumeCM :
      volumeInCubicCentimeters (setup.stateAt .rightLow).volume = 600 := by
    simpa using congrArg Prod.fst hLow
  have hLowPressureKPa :
      pressureInKilopascals (setup.stateAt .rightLow).pressure = 100 := by
    simpa using congrArg Prod.snd hLow
  have hLeftPressure :
      pressureInPascals (setup.stateAt .leftLow).pressure = 100000 := by
    unfold pressureInKilopascals at hLeftPressureKPa
    linarith
  have hHighPressure :
      pressureInPascals (setup.stateAt .rightHigh).pressure = 300000 := by
    unfold pressureInKilopascals at hHighPressureKPa
    linarith
  have hLowPressure :
      pressureInPascals (setup.stateAt .rightLow).pressure = 100000 := by
    unfold pressureInKilopascals at hLowPressureKPa
    linarith
  have hLeftVolume :
      volumeInCubicMeters (setup.stateAt .leftLow).volume = 1 / 5000 := by
    rw [volumeConversion] at hLeftVolumeCM
    norm_num at hLeftVolumeCM ⊢
    linarith
  have hHighVolume :
      volumeInCubicMeters (setup.stateAt .rightHigh).volume = 3 / 5000 := by
    rw [volumeConversion] at hHighVolumeCM
    norm_num at hHighVolumeCM ⊢
    linarith
  have hLowVolume :
      volumeInCubicMeters (setup.stateAt .rightLow).volume = 3 / 5000 := by
    rw [volumeConversion] at hLowVolumeCM
    norm_num at hLowVolumeCM ⊢
    linarith
  have hRising := hLaws.straightLegBoundaryWork .rising
    hScenario.processIsQuasistaticPiecewiseLinear
  have hVertical := hLaws.straightLegBoundaryWork .verticalDown
    hScenario.processIsQuasistaticPiecewiseLinear
  have hHorizontal := hLaws.straightLegBoundaryWork .horizontalLeft
    hScenario.processIsQuasistaticPiecewiseLinear
  simp only [legStart, legFinish] at hRising hVertical hHorizontal
  norm_num [hLeftPressure, hHighPressure, hLowPressure,
    hLeftVolume, hHighVolume, hLowVolume] at hRising hVertical hHorizontal
  rw [hLaws.netWorkIsLegSum, hRising, hVertical, hHorizontal]
  norm_num

/-!
The cyclic first law combines `40 J` of work output with `180 J + 100 J` of
rejected heat, so the hot-reservoir heat is `320 J`.
-/
lemma heatAbsorbedFromHotReservoirInJoules_eq_threeHundredTwenty
    (setup : TriangularHeatEngineSetup)
    (hScenario : MatchesHeatEngineScenario setup)
    (hFigure : MatchesSuppliedHeatEngineFigure setup)
    (hLaws : SatisfiesTriangularHeatEngineLaws setup) :
    energyInJoules setup.heatAbsorbedFromHotReservoir = 320 := by
  rw [hLaws.cyclicFirstLaw,
    netCycleWorkInJoules_eq_forty setup hScenario hFigure hLaws,
    ← hFigure.printedEnergiesRepresentRejectedHeat .rightward180J,
    ← hFigure.printedEnergiesRepresentRejectedHeat .downward100J,
    hFigure.marker180Readout, hFigure.marker100Readout]
  norm_num

/-!
The exact efficiency is `40 / 320 = 1/8 = 0.125`.  With the displayed
two-decimal convention this rounds to `0.13`, uniquely selecting answer D.

Blueprint: `thm:physics:phyx_mini_0422:target`.
-/
theorem problem_phyx_mini_0422
    (setup : TriangularHeatEngineSetup)
    (hScenario : MatchesHeatEngineScenario setup)
    (hFigure : MatchesSuppliedHeatEngineFigure setup)
    (hPhysical : HasPhysicalHeatEngineParameters setup)
    (hLaws : SatisfiesTriangularHeatEngineLaws setup) :
    thermalEfficiency setup = 1 / 8 ∧
      IsUniqueRoundedEfficiencyAnswer (thermalEfficiency setup) .D := by
  have hWork := netCycleWorkInJoules_eq_forty setup hScenario hFigure hLaws
  have hHeat :=
    heatAbsorbedFromHotReservoirInJoules_eq_threeHundredTwenty
      setup hScenario hFigure hLaws
  have hEfficiency : thermalEfficiency setup = 1 / 8 := by
    unfold thermalEfficiency
    rw [hWork, hHeat]
    norm_num
  refine ⟨hEfficiency, ?_⟩
  rw [hEfficiency]
  constructor
  · norm_num [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
      displayedEfficiency]
  · intro other hOther
    cases other with
    | A =>
        norm_num [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
          displayedEfficiency] at hOther
    | B =>
        norm_num [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
          displayedEfficiency] at hOther
    | C =>
        norm_num [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
          displayedEfficiency] at hOther
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0422
