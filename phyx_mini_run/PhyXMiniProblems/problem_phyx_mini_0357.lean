import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0357

open Dimension

/-!
# Work done in a circular pressure-volume cycle

One mole of a monatomic ideal gas undergoes the clockwise, quasistatic cycle
shown in the supplied `p`-versus-`V` diagram.  The plotted circle has centre
`(2, 2)` and coordinate radii `1`, while one horizontal coordinate unit is
`10^3 cm^3` and one vertical coordinate unit is `10^6 dyne/cm^2`.

Pressure, volume, molar heat capacity, and work retain physical dimensions.
Real numbers below are explicitly SI or diagram-coordinate readouts, a mole
readout, or displayed answer values.
-/

/-! ## Dimensionful quantities and named readouts -/

/-- A signed physical volume, carrying length-cubed dimension. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy using Physlib's energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/--
Energy per absolute temperature.  It is used for molar heat capacity and the
molar gas constant; the inverse-mole role is represented by the explicitly
named mole readout because Physlib's `Dimension` has no amount-of-substance
component.
-/
abbrev MolarEnergyPerTemperatureQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Joule readout of a signed physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val / (DimEnergy.joule UnitChoices.SI).val

/-- SI readout in joules per mole-kelvin. -/
def molarEnergyPerTemperatureInSI
    (quantity : MolarEnergyPerTemperatureQuantity) : ℝ :=
  (quantity UnitChoices.SI).val

/-! ## Gas model, cycle, and primary-figure labels -/

/-- Material model explicitly specified in the problem. -/
inductive GasModel where
  | monatomicIdealGas
  deriving DecidableEq, Repr

/-- The four state labels printed on the circular loop. -/
inductive FigurePoint where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Shape of the loop drawn in the `pV` plane. -/
inductive LoopShape where
  | circle
  deriving DecidableEq, Repr

/-- Direction in which the arrows traverse the loop. -/
inductive TraversalDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Thermodynamic regime specified for the cyclic process. -/
inductive ProcessRegime where
  | quasistatic
  deriving DecidableEq, Repr

/-- Literal roles of the labels printed on the two axes. -/
inductive AxisLabel where
  | volumeV
  | pressureP
  | volumeScaleTenCubedCubicCentimeters
  | pressureScaleMillionDynesPerSquareCentimeter
  deriving DecidableEq, Repr

/-!
The independent physical quantities and figure metadata for the experiment.

The path is parameterized from `cycleStartParameter` to
`cycleEndParameter`.  `workOrientedAreaInAxisUnits` is the signed scalar
`pV`-area in the displayed coordinate units, with clockwise orientation
positive because the requested sign convention is work done by the gas.
Neither this area nor `netWorkByGas` is defined to have the requested value.
-/
structure CircularPVCycleSetup where
  gasModel : GasModel
  amountOfGasMoles : ℝ
  molarHeatCapacityAtConstantVolume : MolarEnergyPerTemperatureQuantity
  molarGasConstant : MolarEnergyPerTemperatureQuantity
  processRegime : ProcessRegime
  volumeAlongCycle : ℝ → VolumeQuantity
  pressureAlongCycle : ℝ → PressureQuantity
  cycleStartParameter : ℝ
  cycleEndParameter : ℝ
  parameterAt : FigurePoint → ℝ
  loopShape : LoopShape
  traversalDirection : TraversalDirection
  centerVolumeCoordinate : ℝ
  centerPressureCoordinate : ℝ
  volumeCoordinateRadius : ℝ
  pressureCoordinateRadius : ℝ
  volumeAxisMinimum : ℝ
  volumeAxisMaximum : ℝ
  pressureAxisMinimum : ℝ
  pressureAxisMaximum : ℝ
  volumeAxisUnitCubicCentimeters : ℝ
  pressureAxisUnitDynesPerSquareCentimeter : ℝ
  workOrientedAreaInAxisUnits : ℝ
  netWorkByGas : EnergyQuantity
  axisLabelVisible : AxisLabel → Bool
  pointLabelVisible : FigurePoint → Bool
  arrowVisibleAt : FigurePoint → Bool
  backgroundGridVisible : Bool

/-! ## Unit calibration and diagram-coordinate readouts -/

/-- Cubic metres represented by one horizontal diagram unit. -/
def cubicMetersPerVolumeAxisUnit (setup : CircularPVCycleSetup) : ℝ :=
  setup.volumeAxisUnitCubicCentimeters / 10 ^ 6

/--
Pascals represented by one vertical diagram unit, using
`1 Pa = 10 dyne/cm^2`.
-/
def pascalsPerPressureAxisUnit (setup : CircularPVCycleSetup) : ℝ :=
  setup.pressureAxisUnitDynesPerSquareCentimeter / 10

/-- Horizontal graph coordinate of the volume at parameter `t`. -/
def volumeAxisCoordinate (setup : CircularPVCycleSetup) (t : ℝ) : ℝ :=
  volumeInCubicMeters (setup.volumeAlongCycle t) /
    cubicMetersPerVolumeAxisUnit setup

/-- Vertical graph coordinate of the pressure at parameter `t`. -/
def pressureAxisCoordinate (setup : CircularPVCycleSetup) (t : ℝ) : ℝ :=
  pressureInPascals (setup.pressureAlongCycle t) /
    pascalsPerPressureAxisUnit setup

/--
Sign used for boundary work: a clockwise `pV` cycle has positive work by the
gas, while reversing the cycle reverses the work.
-/
def workOrientationSign : TraversalDirection → ℝ
  | .clockwise => 1
  | .counterclockwise => -1

/-! ## Problem data and governing laws -/

/-!
Statement data and transcription of the primary image.  In particular, the
four labels are at `A = (1,2)`, `B = (2,3)`, `C = (3,2)`, and `D = (2,1)`.
The circle-area value and net work do not occur in this structure.
-/
structure MatchesProblemStatementAndPrimaryFigure
    (setup : CircularPVCycleSetup) : Prop where
  gasIsMonatomicIdeal : setup.gasModel = .monatomicIdealGas
  amountIsOneMole : setup.amountOfGasMoles = 1
  statedMolarHeatCapacity :
    molarEnergyPerTemperatureInSI
        setup.molarHeatCapacityAtConstantVolume =
      (3 / 2 : ℝ) *
        molarEnergyPerTemperatureInSI setup.molarGasConstant
  processIsQuasistatic : setup.processRegime = .quasistatic
  loopIsCircular : setup.loopShape = .circle
  arrowsAreClockwise : setup.traversalDirection = .clockwise
  startParameter : setup.cycleStartParameter = 0
  endParameter : setup.cycleEndParameter = 2 * Real.pi
  parameterA : setup.parameterAt .A = 0
  parameterB : setup.parameterAt .B = Real.pi / 2
  parameterC : setup.parameterAt .C = Real.pi
  parameterD : setup.parameterAt .D = 3 * Real.pi / 2
  circleCenterVolume : setup.centerVolumeCoordinate = 2
  circleCenterPressure : setup.centerPressureCoordinate = 2
  circleVolumeRadius : setup.volumeCoordinateRadius = 1
  circlePressureRadius : setup.pressureCoordinateRadius = 1
  volumeAxisRange :
    setup.volumeAxisMinimum = 0 ∧ setup.volumeAxisMaximum = 4
  pressureAxisRange :
    setup.pressureAxisMinimum = 0 ∧ setup.pressureAxisMaximum = 3
  volumeAxisScale : setup.volumeAxisUnitCubicCentimeters = 10 ^ 3
  pressureAxisScale :
    setup.pressureAxisUnitDynesPerSquareCentimeter = 10 ^ 6
  pointACoordinates :
    volumeAxisCoordinate setup (setup.parameterAt .A) = 1 ∧
      pressureAxisCoordinate setup (setup.parameterAt .A) = 2
  pointBCoordinates :
    volumeAxisCoordinate setup (setup.parameterAt .B) = 2 ∧
      pressureAxisCoordinate setup (setup.parameterAt .B) = 3
  pointCCoordinates :
    volumeAxisCoordinate setup (setup.parameterAt .C) = 3 ∧
      pressureAxisCoordinate setup (setup.parameterAt .C) = 2
  pointDCoordinates :
    volumeAxisCoordinate setup (setup.parameterAt .D) = 2 ∧
      pressureAxisCoordinate setup (setup.parameterAt .D) = 1
  volumeSymbolVisible : setup.axisLabelVisible .volumeV = true
  pressureSymbolVisible : setup.axisLabelVisible .pressureP = true
  volumeUnitVisible :
    setup.axisLabelVisible .volumeScaleTenCubedCubicCentimeters = true
  pressureUnitVisible :
    setup.axisLabelVisible
        .pressureScaleMillionDynesPerSquareCentimeter = true
  allPointLabelsVisible : ∀ point, setup.pointLabelVisible point = true
  allDirectionArrowsVisible : ∀ point, setup.arrowVisibleAt point = true
  gridVisible : setup.backgroundGridVisible = true

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalParameters (setup : CircularPVCycleSetup) : Prop where
  gasAmountPositive : 0 < setup.amountOfGasMoles
  molarGasConstantPositive :
    0 < molarEnergyPerTemperatureInSI setup.molarGasConstant
  parameterIntervalNonempty :
    setup.cycleStartParameter < setup.cycleEndParameter
  volumeRadiusPositive : 0 < setup.volumeCoordinateRadius
  pressureRadiusPositive : 0 < setup.pressureCoordinateRadius
  volumeScalePositive : 0 < cubicMetersPerVolumeAxisUnit setup
  pressureScalePositive : 0 < pascalsPerPressureAxisUnit setup
  volumePositiveAlongCycle : ∀ t,
    t ∈ Set.Icc setup.cycleStartParameter setup.cycleEndParameter →
      0 < volumeInCubicMeters (setup.volumeAlongCycle t)
  pressurePositiveAlongCycle : ∀ t,
    t ∈ Set.Icc setup.cycleStartParameter setup.cycleEndParameter →
      0 < pressureInPascals (setup.pressureAlongCycle t)

/-!
The path is a differentiable closed cycle, expressing the quasistatic process
mathematically without assigning its work.
-/
structure IsClosedQuasistaticCycle (setup : CircularPVCycleSetup) : Prop where
  volumePathDifferentiable :
    Differentiable ℝ
      (fun t => volumeInCubicMeters (setup.volumeAlongCycle t))
  pressurePathDifferentiable :
    Differentiable ℝ
      (fun t => pressureInPascals (setup.pressureAlongCycle t))
  volumeCloses :
    setup.volumeAlongCycle setup.cycleStartParameter =
      setup.volumeAlongCycle setup.cycleEndParameter
  pressureCloses :
    setup.pressureAlongCycle setup.cycleStartParameter =
      setup.pressureAlongCycle setup.cycleEndParameter

/-!
Geometry of a circular loop in calibrated diagram coordinates.  The second
field is the general oriented-area formula for a circle with arbitrary
coordinate radii and either traversal direction; it contains no numerical
answer specific to this problem.
-/
structure SatisfiesCircularPVDiagramGeometry
    (setup : CircularPVCycleSetup) : Prop where
  pointsLieOnDisplayedCircle : ∀ t,
    t ∈ Set.Icc setup.cycleStartParameter setup.cycleEndParameter →
      ((volumeAxisCoordinate setup t - setup.centerVolumeCoordinate) /
          setup.volumeCoordinateRadius) ^ 2 +
        ((pressureAxisCoordinate setup t - setup.centerPressureCoordinate) /
          setup.pressureCoordinateRadius) ^ 2 = 1
  orientedAreaOfCircle :
    setup.workOrientedAreaInAxisUnits =
      workOrientationSign setup.traversalDirection * Real.pi *
        setup.volumeCoordinateRadius * setup.pressureCoordinateRadius

/-!
Quasistatic boundary-work law `W_by = ∮ p dV`.  The signed integral is
represented by `workOrientedAreaInAxisUnits`, and the two calibration factors
convert diagram area to joules.  This is a generic law and does not fix the
circle's radii, scales, or resulting work.
-/
structure SatisfiesQuasistaticBoundaryWorkLaw
    (setup : CircularPVCycleSetup) : Prop where
  boundaryWorkFromOrientedPVArea :
    energyInJoules setup.netWorkByGas =
      setup.workOrientedAreaInAxisUnits *
        pascalsPerPressureAxisUnit setup *
        cubicMetersPerVolumeAxisUnit setup

/-! ## Exact work and displayed answer -/

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Work values printed beside the four answer labels, in joules. -/
def displayedNetWorkJoules : AnswerChoice → ℝ
  | .A => 314
  | .B => 895
  | .C => 550
  | .D => 160

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- A real joule readout rounds to the displayed whole number. -/
def RoundsToNearestJoule (value displayedValue : ℝ) : Prop :=
  |value - displayedValue| < 1 / 2

/-!
The circle and unit scales give the exact joule readout `100π` of the
dimensionful net work.  This lemma is a derived conclusion, not a premise of
the model.
-/
lemma exactNetWorkFromCircularDiagram
    (setup : CircularPVCycleSetup)
    (h_data : MatchesProblemStatementAndPrimaryFigure setup)
    (h_geometry : SatisfiesCircularPVDiagramGeometry setup)
    (h_work : SatisfiesQuasistaticBoundaryWorkLaw setup) :
    energyInJoules setup.netWorkByGas = 100 * Real.pi := by
  rw [h_work.boundaryWorkFromOrientedPVArea,
    h_geometry.orientedAreaOfCircle,
    h_data.arrowsAreClockwise,
    h_data.circleVolumeRadius,
    h_data.circlePressureRadius]
  simp only [workOrientationSign, one_mul, mul_one]
  rw [show pascalsPerPressureAxisUnit setup = 100000 by
      rw [pascalsPerPressureAxisUnit, h_data.pressureAxisScale]
      norm_num,
    show cubicMetersPerVolumeAxisUnit setup = 1 / 1000 by
      rw [cubicMetersPerVolumeAxisUnit, h_data.volumeAxisScale]
      norm_num]
  ring

/-!
The exact work is `100π J`, whose nearest whole-joule display is `314 J`;
therefore the recorded choice is A.

Blueprint: `thm:physics:phyx_mini_0357:target`.
-/
theorem netWorkDoneByGasInOneCycle
    (setup : CircularPVCycleSetup)
    (h_data : MatchesProblemStatementAndPrimaryFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_cycle : IsClosedQuasistaticCycle setup)
    (h_geometry : SatisfiesCircularPVDiagramGeometry setup)
    (h_work : SatisfiesQuasistaticBoundaryWorkLaw setup) :
    energyInJoules setup.netWorkByGas = 100 * Real.pi ∧
      RoundsToNearestJoule (energyInJoules setup.netWorkByGas)
        (displayedNetWorkJoules .A) ∧
      recordedAnswerChoice = .A := by
  have h_exact : energyInJoules setup.netWorkByGas = 100 * Real.pi :=
    exactNetWorkFromCircularDiagram setup h_data h_geometry h_work
  refine ⟨h_exact, ?_, rfl⟩
  rw [h_exact]
  unfold RoundsToNearestJoule displayedNetWorkJoules
  rw [abs_lt]
  constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

end PhyXMiniProblems.ProblemPhyXMini0357
