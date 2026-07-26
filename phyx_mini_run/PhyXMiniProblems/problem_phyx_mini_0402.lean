import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0402

open Dimension

/-!
# Work done on a gas along a two-stage compression path

The primary pressure-volume image shows the directed path

`i = (300 cm³, 200 kPa) → peak = (200 cm³, 400 kPa)
  → f = (100 cm³, 200 kPa)`.

Both legs are straight.  The auxiliary caption gives approximate pixel-based
coordinates, but the plotted points lie exactly on the labelled axis ticks
listed above.  This formalization therefore uses the primary image, as the
blueprint requests.

Volume, pressure, and work are physical dimensionful quantities.  Real
numbers are used only for explicitly unit-labelled readouts, plotted
coordinates, unit-conversion factors, and the displayed answer value.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical gas volume, carrying dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical gas volume in cubic centimetres. -/
def volumeInCubicCentimeters (volume : GasVolume) : ℝ :=
  1000000 * ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical pressure in kilopascals, the figure's vertical unit. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a signed physical work or energy quantity in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- One `kPa · cm³` is `10⁻³ J`. -/
def joulesPerKilopascalCubicCentimeter : ℝ := 1 / 1000

/--
Work done on the gas along one straight segment of a `p`--`V` diagram.

The average pressure on a straight segment is the arithmetic mean of its
endpoint pressures.  The factor `initialVolume - finalVolume` implements the
work-on-the-gas sign convention, so a compression has positive work.
-/
def straightSegmentWorkOnGasInJoules
    (initialPressure finalPressure initialVolume finalVolume : ℝ) : ℝ :=
  ((initialPressure + finalPressure) / 2) *
    (initialVolume - finalVolume) *
    joulesPerKilopascalCubicCentimeter

/-! ## Process states, legs, and figure labels -/

/-- The two labelled endpoints and the unlabelled peak in the image. -/
inductive DiagramPoint where
  | initialI
  | peak
  | finalF
  deriving DecidableEq, Repr

/-- The two directed straight segments shown by arrows in the image. -/
inductive ProcessSegment where
  | initialToPeak
  | peakToFinal
  deriving DecidableEq, Repr

/-- Initial diagram point of each directed segment. -/
def ProcessSegment.initialPoint : ProcessSegment → DiagramPoint
  | .initialToPeak => .initialI
  | .peakToFinal => .peak

/-- Final diagram point of each directed segment. -/
def ProcessSegment.finalPoint : ProcessSegment → DiagramPoint
  | .initialToPeak => .peak
  | .peakToFinal => .finalF

/-- Physical quantity assigned to an axis in the supplied figure. -/
inductive AxisQuantity where
  | volumeV
  | pressureP
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal axis. -/
inductive VolumeAxisUnit where
  | cubicCentimeter
  deriving DecidableEq, Repr

/-- Unit printed on the vertical axis. -/
inductive PressureAxisUnit where
  | kilopascal
  deriving DecidableEq, Repr

/-- Geometric shape of each process leg in the `p`--`V` plane. -/
inductive SegmentShape where
  | straightLine
  deriving DecidableEq, Repr

/-- Thermodynamic role of each leg. -/
inductive ProcessKind where
  | compression
  deriving DecidableEq, Repr

/-- Qualitative pressure change along a directed leg. -/
inductive PressureTrend where
  | rising
  | falling
  deriving DecidableEq, Repr

/-- Physical pressure and volume at one point of the process. -/
structure ThermodynamicState where
  volume : GasVolume
  pressure : DimPressure

/-!
The axes, plotted coordinates, labels, segments, and arrows visible in the
primary image.  Coordinates are scalar readouts in the units stored alongside
the axes; they are not replacements for physical pressure or volume.
-/
structure PressureVolumeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : VolumeAxisUnit
  verticalAxisUnit : PressureAxisUnit
  volumeCoordinate : DiagramPoint → ℝ
  pressureCoordinate : DiagramPoint → ℝ
  pointShown : DiagramPoint → Bool
  pointLabelShown : DiagramPoint → Bool
  segmentShown : ProcessSegment → Bool
  arrowStart : ProcessSegment → DiagramPoint
  arrowEnd : ProcessSegment → DiagramPoint
  segmentShape : ProcessSegment → SegmentShape

/-!
A gas sample and its two-stage compression.  The gas carrier is abstract, while
all plotted state variables and work values retain physical dimensions.  The
segment works and total work are independent fields; no requested numerical
answer is assigned here.
-/
structure TwoStageGasCompression (GasSample : Type) where
  gas : GasSample
  stateAt : DiagramPoint → ThermodynamicState
  processKind : ProcessSegment → ProcessKind
  pressureTrend : ProcessSegment → PressureTrend
  workDoneOnGasOnSegment : ProcessSegment → DimEnergy
  workDoneOnGas : DimEnergy
  figure : PressureVolumeFigure

/-! ## Scenario and primary-figure data -/

/--
The prose classification of the two legs.  It contains no numerical work
claim.
-/
structure MatchesTwoStageCompressionScenario
    {GasSample : Type} (process : TwoStageGasCompression GasSample) : Prop where
  first_leg_is_compression :
    process.processKind .initialToPeak = .compression
  second_leg_is_compression :
    process.processKind .peakToFinal = .compression
  pressure_rises_on_first_leg :
    process.pressureTrend .initialToPeak = .rising
  pressure_falls_on_second_leg :
    process.pressureTrend .peakToFinal = .falling

/-!
Exact transcription of the primary pressure-volume raster, including the axis
roles and units, the three plotted coordinates, endpoint labels, straight
segments, and arrow directions.  The physical state readouts are explicitly
calibrated to these coordinates.
-/
structure MatchesPrimaryPressureVolumeFigure
    {GasSample : Type} (process : TwoStageGasCompression GasSample) : Prop where
  horizontal_axis_is_volume :
    process.figure.horizontalAxisQuantity = .volumeV
  vertical_axis_is_pressure :
    process.figure.verticalAxisQuantity = .pressureP
  horizontal_axis_unit_is_cubic_centimeter :
    process.figure.horizontalAxisUnit = .cubicCentimeter
  vertical_axis_unit_is_kilopascal :
    process.figure.verticalAxisUnit = .kilopascal
  state_readouts_match_figure_coordinates :
    ∀ point,
      volumeInCubicCentimeters (process.stateAt point).volume =
          process.figure.volumeCoordinate point ∧
        pressureInKilopascals (process.stateAt point).pressure =
          process.figure.pressureCoordinate point
  initial_volume_coordinate :
    process.figure.volumeCoordinate .initialI = 300
  initial_pressure_coordinate :
    process.figure.pressureCoordinate .initialI = 200
  peak_volume_coordinate :
    process.figure.volumeCoordinate .peak = 200
  peak_pressure_coordinate :
    process.figure.pressureCoordinate .peak = 400
  final_volume_coordinate :
    process.figure.volumeCoordinate .finalF = 100
  final_pressure_coordinate :
    process.figure.pressureCoordinate .finalF = 200
  initial_point_shown : process.figure.pointShown .initialI = true
  peak_point_shown : process.figure.pointShown .peak = true
  final_point_shown : process.figure.pointShown .finalF = true
  initial_label_i_shown : process.figure.pointLabelShown .initialI = true
  peak_is_unlabelled : process.figure.pointLabelShown .peak = false
  final_label_f_shown : process.figure.pointLabelShown .finalF = true
  both_segments_shown :
    ∀ segment, process.figure.segmentShown segment = true
  arrows_follow_process_order :
    ∀ segment,
      process.figure.arrowStart segment = segment.initialPoint ∧
        process.figure.arrowEnd segment = segment.finalPoint
  both_segments_are_straight :
    ∀ segment, process.figure.segmentShape segment = .straightLine

/-! ## Governing pressure-volume work law -/

/-!
For each straight leg, work on the gas is average pressure times the decrease
in volume, with the explicit `kPa · cm³` to joule conversion.  The total work
is the sum of the two independent leg works.  These laws are generic in the
state data and do not contain the requested `60 J` conclusion.
-/
structure ObeysPiecewiseLinearPressureVolumeWorkLaw
    {GasSample : Type} (process : TwoStageGasCompression GasSample) : Prop where
  segment_work_law :
    ∀ segment,
      energyInJoules (process.workDoneOnGasOnSegment segment) =
        straightSegmentWorkOnGasInJoules
          (pressureInKilopascals
            (process.stateAt segment.initialPoint).pressure)
          (pressureInKilopascals
            (process.stateAt segment.finalPoint).pressure)
          (volumeInCubicCentimeters
            (process.stateAt segment.initialPoint).volume)
          (volumeInCubicCentimeters
            (process.stateAt segment.finalPoint).volume)
  total_work_is_sum_of_segment_works :
    energyInJoules process.workDoneOnGas =
      energyInJoules
          (process.workDoneOnGasOnSegment .initialToPeak) +
        energyInJoules
          (process.workDoneOnGasOnSegment .peakToFinal)

/-! ## Requested result -/

/--
The work done on the gas along the plotted two-stage compression is `60 J`.
-/
theorem work_done_on_gas_is_sixty_joules
    {GasSample : Type}
    (process : TwoStageGasCompression GasSample)
    (h_scenario : MatchesTwoStageCompressionScenario process)
    (h_figure : MatchesPrimaryPressureVolumeFigure process)
    (h_work_law : ObeysPiecewiseLinearPressureVolumeWorkLaw process) :
    energyInJoules process.workDoneOnGas = 60 := by
  rw [h_work_law.total_work_is_sum_of_segment_works,
    h_work_law.segment_work_law .initialToPeak,
    h_work_law.segment_work_law .peakToFinal]
  simp only [ProcessSegment.initialPoint, ProcessSegment.finalPoint]
  rw [(h_figure.state_readouts_match_figure_coordinates .initialI).1,
    (h_figure.state_readouts_match_figure_coordinates .initialI).2,
    (h_figure.state_readouts_match_figure_coordinates .peak).1,
    (h_figure.state_readouts_match_figure_coordinates .peak).2,
    (h_figure.state_readouts_match_figure_coordinates .finalF).1,
    (h_figure.state_readouts_match_figure_coordinates .finalF).2,
    h_figure.initial_volume_coordinate,
    h_figure.initial_pressure_coordinate,
    h_figure.peak_volume_coordinate,
    h_figure.peak_pressure_coordinate,
    h_figure.final_volume_coordinate,
    h_figure.final_pressure_coordinate]
  norm_num [straightSegmentWorkOnGasInJoules,
    joulesPerKilopascalCubicCentimeter]

end PhyXMiniProblems.ProblemPhyXMini0402
