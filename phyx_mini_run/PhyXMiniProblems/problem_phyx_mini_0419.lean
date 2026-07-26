import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0419

open Dimension

/-!
# Thermal efficiency of a rectangular pressure-volume heat-engine cycle

The primary raster shows a clockwise rectangular cycle.  Its left and right
volumes are `100 cm³` and `200 cm³`; its lower and upper pressures are
`100 kPa` and `400 kPa`.  This corrects two errors in the auxiliary caption:
the lower edge is at `100 kPa`, not `200 kPa`, and the black process arrows run
clockwise, not counterclockwise.

The two purple outward heat-transfer arrows belong to the right and bottom
legs and read `Q = -90 J` and `Q = -25 J`, respectively.  Heat is signed
positive into the working gas, while boundary work is signed positive when
done by the gas.

Pressure, volume, heat, work, and internal-energy change remain dimensionful
Physlib quantities.  Real numbers below occur only as explicitly named unit
readouts, a dimensionless efficiency, or displayed answer-choice values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A signed physical volume, carrying the dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read the same physical volume in the `cm³` unit printed on the figure. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read the same physical pressure in the `kPa` unit printed on the figure. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- The conversion `1 kPa · cm³ = 10⁻³ J`. -/
def joulesPerKilopascalCubicCentimeter : ℝ := 1 / 1000

/-! ## Cycle and figure vocabulary -/

/-- The thermodynamic role explicitly assigned to the cyclic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- The four unlabeled corner markers, named by their positions in the image. -/
inductive CycleState where
  | lowerLeft
  | upperLeft
  | upperRight
  | lowerRight
  deriving DecidableEq, Repr

/-- The four directed legs in the order shown by the black arrows. -/
inductive CycleLeg where
  | leftUp
  | topRight
  | rightDown
  | bottomLeft
  deriving DecidableEq, Repr

/-- Constant-coordinate thermodynamic character of a rectangular leg. -/
inductive ProcessKind where
  | isochoric
  | isobaric
  deriving DecidableEq, Repr

/-- Geometric appearance of a leg in the supplied `p`-`V` plot. -/
inductive PathGeometry where
  | verticalSegment
  | horizontalSegment
  deriving DecidableEq, Repr

/-- Physical quantity and unit literally printed on a diagram axis. -/
inductive AxisQuantity where
  | pressureKilopascals
  | volumeCubicCentimeters
  deriving DecidableEq, Repr

/-- Direction of a purple heat-transfer arrow, or absence of an annotation. -/
inductive HeatArrowDirection where
  | intoGas
  | outOfGas
  | notShown
  deriving DecidableEq, Repr

/-- A dimensionful equilibrium state represented by a corner of the rectangle. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity

/-!
The working system, its four states, and the signed energy transfers on each
leg.  The heat and work fields are independent physical observables; no field
assigns the requested efficiency or any answer-choice value.
-/
structure RectangularPVHeatEngineCycle where
  deviceRole : ThermodynamicDeviceRole
  stateAt : CycleState → ThermodynamicState
  workByGas : CycleLeg → DimEnergy
  heatIntoGas : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  pathStart : CycleLeg → CycleState
  pathFinish : CycleLeg → CycleState
  processKind : CycleLeg → ProcessKind
  pathGeometry : CycleLeg → PathGeometry
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  stateMarkerVisible : CycleState → Bool
  heatAnnotationVisible : CycleLeg → Bool
  heatArrowDirection : CycleLeg → HeatArrowDirection

/-! ## Problem data, primary-figure readouts, and governing laws -/

/-- The prose identifies the cyclic device as a heat engine. -/
structure MatchesProblemStatement
    (setup : RectangularPVHeatEngineCycle) : Prop where
  device_is_heat_engine : setup.deviceRole = .heatEngine

/-!
Exact transcription of the primary raster: axis units, corner coordinates,
clockwise path, and the two signed outward-heat annotations.  The raster is
used instead of the contradictory approximate auxiliary caption.
-/
structure MatchesPrimaryPVDiagram
    (setup : RectangularPVHeatEngineCycle) : Prop where
  horizontal_axis_is_volume :
    setup.horizontalAxisQuantity = .volumeCubicCentimeters
  vertical_axis_is_pressure :
    setup.verticalAxisQuantity = .pressureKilopascals
  lower_left_volume :
    volumeInCubicCentimeters (setup.stateAt .lowerLeft).volume = 100
  lower_left_pressure :
    pressureInKilopascals (setup.stateAt .lowerLeft).pressure = 100
  upper_left_volume :
    volumeInCubicCentimeters (setup.stateAt .upperLeft).volume = 100
  upper_left_pressure :
    pressureInKilopascals (setup.stateAt .upperLeft).pressure = 400
  upper_right_volume :
    volumeInCubicCentimeters (setup.stateAt .upperRight).volume = 200
  upper_right_pressure :
    pressureInKilopascals (setup.stateAt .upperRight).pressure = 400
  lower_right_volume :
    volumeInCubicCentimeters (setup.stateAt .lowerRight).volume = 200
  lower_right_pressure :
    pressureInKilopascals (setup.stateAt .lowerRight).pressure = 100
  lower_left_marker_visible : setup.stateMarkerVisible .lowerLeft = true
  upper_left_marker_visible : setup.stateMarkerVisible .upperLeft = true
  upper_right_marker_visible : setup.stateMarkerVisible .upperRight = true
  lower_right_marker_visible : setup.stateMarkerVisible .lowerRight = true
  left_starts_at_lower_left : setup.pathStart .leftUp = .lowerLeft
  left_finishes_at_upper_left : setup.pathFinish .leftUp = .upperLeft
  top_starts_at_upper_left : setup.pathStart .topRight = .upperLeft
  top_finishes_at_upper_right : setup.pathFinish .topRight = .upperRight
  right_starts_at_upper_right : setup.pathStart .rightDown = .upperRight
  right_finishes_at_lower_right : setup.pathFinish .rightDown = .lowerRight
  bottom_starts_at_lower_right : setup.pathStart .bottomLeft = .lowerRight
  bottom_finishes_at_lower_left : setup.pathFinish .bottomLeft = .lowerLeft
  left_is_vertical : setup.pathGeometry .leftUp = .verticalSegment
  top_is_horizontal : setup.pathGeometry .topRight = .horizontalSegment
  right_is_vertical : setup.pathGeometry .rightDown = .verticalSegment
  bottom_is_horizontal : setup.pathGeometry .bottomLeft = .horizontalSegment
  left_is_isochoric : setup.processKind .leftUp = .isochoric
  top_is_isobaric : setup.processKind .topRight = .isobaric
  right_is_isochoric : setup.processKind .rightDown = .isochoric
  bottom_is_isobaric : setup.processKind .bottomLeft = .isobaric
  left_heat_annotation_absent :
    setup.heatAnnotationVisible .leftUp = false
  top_heat_annotation_absent :
    setup.heatAnnotationVisible .topRight = false
  right_heat_annotation_visible :
    setup.heatAnnotationVisible .rightDown = true
  bottom_heat_annotation_visible :
    setup.heatAnnotationVisible .bottomLeft = true
  left_heat_arrow_not_shown :
    setup.heatArrowDirection .leftUp = .notShown
  top_heat_arrow_not_shown :
    setup.heatArrowDirection .topRight = .notShown
  right_heat_arrow_points_out :
    setup.heatArrowDirection .rightDown = .outOfGas
  bottom_heat_arrow_points_out :
    setup.heatArrowDirection .bottomLeft = .outOfGas
  right_leg_heat_joules :
    energyInJoules (setup.heatIntoGas .rightDown) = -90
  bottom_leg_heat_joules :
    energyInJoules (setup.heatIntoGas .bottomLeft) = -25

/-- Positivity conditions selecting genuine pressure-volume states. -/
structure HasPhysicalStateReadouts
    (setup : RectangularPVHeatEngineCycle) : Prop where
  pressure_positive :
    ∀ state, 0 < pressureInPascals (setup.stateAt state).pressure
  volume_positive :
    ∀ state, 0 < volumeInCubicMeters (setup.stateAt state).volume

/-!
The image shows the only two outward heat-transfer arrows on the right and
bottom legs.  The remaining left and top legs therefore comprise the heat
input of the depicted engine.  These sign facts identify heat-input versus
heat-rejection legs without assigning the total input or the efficiency.
-/
structure HasFigureIndicatedHeatFlowPattern
    (setup : RectangularPVHeatEngineCycle) : Prop where
  left_leg_absorbs_heat :
    0 < energyInJoules (setup.heatIntoGas .leftUp)
  top_leg_absorbs_heat :
    0 < energyInJoules (setup.heatIntoGas .topRight)
  right_leg_rejects_heat :
    energyInJoules (setup.heatIntoGas .rightDown) < 0
  bottom_leg_rejects_heat :
    energyInJoules (setup.heatIntoGas .bottomLeft) < 0

/-!
Quasi-static boundary-work laws for isobaric and isochoric legs.  The
isobaric formula is `W_by = p (V_finish - V_start)` with the diagram-unit
conversion shown explicitly; an isochoric leg does no boundary work.
-/
structure SatisfiesQuasiStaticBoundaryWorkLaw
    (setup : RectangularPVHeatEngineCycle) : Prop where
  isobaric_pressure_constant : ∀ leg,
    setup.processKind leg = .isobaric →
      pressureInKilopascals
          (setup.stateAt (setup.pathFinish leg)).pressure =
        pressureInKilopascals
          (setup.stateAt (setup.pathStart leg)).pressure
  isobaric_boundary_work : ∀ leg,
    setup.processKind leg = .isobaric →
      energyInJoules (setup.workByGas leg) =
        pressureInKilopascals
            (setup.stateAt (setup.pathStart leg)).pressure *
          (volumeInCubicCentimeters
                (setup.stateAt (setup.pathFinish leg)).volume -
            volumeInCubicCentimeters
                (setup.stateAt (setup.pathStart leg)).volume) *
          joulesPerKilopascalCubicCentimeter
  isochoric_volume_constant : ∀ leg,
    setup.processKind leg = .isochoric →
      volumeInCubicCentimeters
          (setup.stateAt (setup.pathFinish leg)).volume =
        volumeInCubicCentimeters
          (setup.stateAt (setup.pathStart leg)).volume
  isochoric_boundary_work : ∀ leg,
    setup.processKind leg = .isochoric →
      energyInJoules (setup.workByGas leg) = 0

/-!
First law on every directed leg, with `Q = ΔU + W_by`, together with the
state-function closure relation `Σ ΔU = 0` for one complete cycle.  These
are governing laws and do not assert any requested work, heat-input, or
efficiency value.
-/
structure SatisfiesFirstLawAndCycleClosure
    (setup : RectangularPVHeatEngineCycle) : Prop where
  first_law : ∀ leg,
    energyInJoules (setup.heatIntoGas leg) =
      energyInJoules (setup.internalEnergyChange leg) +
        energyInJoules (setup.workByGas leg)
  internal_energy_returns_to_initial_value :
    energyInJoules (setup.internalEnergyChange .leftUp) +
          energyInJoules (setup.internalEnergyChange .topRight) +
        energyInJoules (setup.internalEnergyChange .rightDown) +
      energyInJoules (setup.internalEnergyChange .bottomLeft) = 0

/-! ## Cycle totals, efficiency, and displayed choices -/

/-- Net work done by the gas during one clockwise traversal. -/
def netWorkByGasInJoules (setup : RectangularPVHeatEngineCycle) : ℝ :=
  energyInJoules (setup.workByGas .leftUp) +
      energyInJoules (setup.workByGas .topRight) +
    energyInJoules (setup.workByGas .rightDown) +
  energyInJoules (setup.workByGas .bottomLeft)

/-- Total heat input, obtained by summing the positive parts of all leg heats. -/
def totalHeatInputInJoules (setup : RectangularPVHeatEngineCycle) : ℝ :=
  max (energyInJoules (setup.heatIntoGas .leftUp)) 0 +
      max (energyInJoules (setup.heatIntoGas .topRight)) 0 +
    max (energyInJoules (setup.heatIntoGas .rightDown)) 0 +
  max (energyInJoules (setup.heatIntoGas .bottomLeft)) 0

/-- Dimensionless heat-engine efficiency `W_net / Q_in`. -/
def thermalEfficiency (setup : RectangularPVHeatEngineCycle) : ℝ :=
  netWorkByGasInJoules setup / totalHeatInputInJoules setup

/-- Labels of the four choices displayed beside the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless decimal value printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 79 / 100
  | .B => 42 / 100
  | .C => 21 / 100
  | .D => 33 / 100

/-- The dataset records answer label C. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a value displayed after rounding to two decimal places. -/
def RoundsToDisplayedHundredth
    (efficiency displayed : ℝ) : Prop :=
  abs (efficiency - displayed) < 1 / 200

/-!
The diagram and boundary-work law give `40 J` on the upper expansion,
`-10 J` on the lower compression, and zero work on both vertical legs, hence
`W_net = 30 J`.  The two rejected heats sum to `-115 J`; first-law closure
then forces the two heat-input legs to supply `145 J` in total.
-/
lemma cycleWorkAndHeatInputReadouts
    (setup : RectangularPVHeatEngineCycle)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_heat_flow : HasFigureIndicatedHeatFlowPattern setup)
    (h_work : SatisfiesQuasiStaticBoundaryWorkLaw setup)
    (h_first_law : SatisfiesFirstLawAndCycleClosure setup) :
    netWorkByGasInJoules setup = 30 ∧
      totalHeatInputInJoules setup = 145 := by
  have h_work_left :
      energyInJoules (setup.workByGas .leftUp) = 0 :=
    h_work.isochoric_boundary_work .leftUp h_figure.left_is_isochoric
  have h_work_right :
      energyInJoules (setup.workByGas .rightDown) = 0 :=
    h_work.isochoric_boundary_work .rightDown h_figure.right_is_isochoric
  have h_work_top :
      energyInJoules (setup.workByGas .topRight) = 40 := by
    have h :=
      h_work.isobaric_boundary_work .topRight h_figure.top_is_isobaric
    rw [h_figure.top_starts_at_upper_left,
      h_figure.top_finishes_at_upper_right,
      h_figure.upper_left_pressure,
      h_figure.upper_right_volume,
      h_figure.upper_left_volume] at h
    norm_num [joulesPerKilopascalCubicCentimeter] at h ⊢
    exact h
  have h_work_bottom :
      energyInJoules (setup.workByGas .bottomLeft) = -10 := by
    have h :=
      h_work.isobaric_boundary_work .bottomLeft h_figure.bottom_is_isobaric
    rw [h_figure.bottom_starts_at_lower_right,
      h_figure.bottom_finishes_at_lower_left,
      h_figure.lower_right_pressure,
      h_figure.lower_left_volume,
      h_figure.lower_right_volume] at h
    norm_num [joulesPerKilopascalCubicCentimeter] at h ⊢
    exact h
  have h_heat_input_sum :
      energyInJoules (setup.heatIntoGas .leftUp) +
        energyInJoules (setup.heatIntoGas .topRight) = 145 := by
    have h_first_left := h_first_law.first_law .leftUp
    have h_first_top := h_first_law.first_law .topRight
    have h_first_right := h_first_law.first_law .rightDown
    have h_first_bottom := h_first_law.first_law .bottomLeft
    linarith [h_first_law.internal_energy_returns_to_initial_value,
      h_figure.right_leg_heat_joules, h_figure.bottom_leg_heat_joules]
  constructor
  · simp [netWorkByGasInJoules, h_work_left, h_work_top, h_work_right,
      h_work_bottom]
    norm_num
  · rw [totalHeatInputInJoules,
      max_eq_left (le_of_lt h_heat_flow.left_leg_absorbs_heat),
      max_eq_left (le_of_lt h_heat_flow.top_leg_absorbs_heat),
      max_eq_right (le_of_lt h_heat_flow.right_leg_rejects_heat),
      max_eq_right (le_of_lt h_heat_flow.bottom_leg_rejects_heat)]
    norm_num
    exact h_heat_input_sum

/-!
Consequently the exact efficiency is `30 / 145 = 6 / 29`.  This lies within
one half-hundredth of `0.21`, so it selects recorded answer C.
-/
theorem thermalEfficiency_eq_answerChoiceC
    (setup : RectangularPVHeatEngineCycle)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_physical : HasPhysicalStateReadouts setup)
    (h_heat_flow : HasFigureIndicatedHeatFlowPattern setup)
    (h_work : SatisfiesQuasiStaticBoundaryWorkLaw setup)
    (h_first_law : SatisfiesFirstLawAndCycleClosure setup) :
    thermalEfficiency setup = (6 / 29 : ℝ) ∧
      RoundsToDisplayedHundredth
        (thermalEfficiency setup)
        (displayedEfficiency recordedAnswerChoice) := by
  obtain ⟨h_work_total, h_heat_input_total⟩ :=
    cycleWorkAndHeatInputReadouts setup h_figure h_heat_flow h_work h_first_law
  have h_efficiency : thermalEfficiency setup = (6 / 29 : ℝ) := by
    rw [thermalEfficiency, h_work_total, h_heat_input_total]
    norm_num
  refine ⟨h_efficiency, ?_⟩
  rw [h_efficiency]
  norm_num [RoundsToDisplayedHundredth, displayedEfficiency,
    recordedAnswerChoice, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0419
