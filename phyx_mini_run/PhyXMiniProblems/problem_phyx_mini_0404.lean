import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0404

open Dimension

/-!
# Volume scale in an isobaric compression

The primary pressure--volume bitmap shows a horizontal process at `200 kPa`.
Its arrow runs from the tick `3V₁` on the right to the tick `V₁` on the left,
so the gas is compressed isobarically from volume `3V₁` to volume `V₁`.
The prose states that the work done on the gas is `80 J` and asks for the
reference volume `V₁` in cubic centimetres.

Pressure and work use Physlib's dimensionful quantities.  Physlib has no
named volume quantity, so volume is represented directly with its physical
dimension `L³`.  Real numbers occur only as explicitly unit-labelled
readouts and displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical gas volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Physical pressure, using Physlib's dimensional pressure quantity. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed physical energy, used here for work done on the gas. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Coherent-SI volume readout in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Volume readout in cubic centimetres, using `1 m³ = 10⁶ cm³`. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- Coherent-SI pressure readout in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Pressure readout in kilopascals, using `1 kPa = 10³ Pa`. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Coherent-SI energy readout in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Process and primary-figure vocabulary -/

/-- The three symbolic volume ticks printed under the horizontal line. -/
inductive VolumeTick where
  | V1
  | twiceV1
  | thriceV1
  deriving DecidableEq, Fintype, Repr

/-- Physical quantities assigned to the two axes of the bitmap. -/
inductive AxisQuantity where
  | volumeV
  | pressureP
  deriving DecidableEq, Repr

/-- Unit explicitly printed beside the pressure axis. -/
inductive PressureDisplayUnit where
  | kilopascal
  deriving DecidableEq, Repr

/-- Volume unit requested in the question and used in the answer choices. -/
inductive VolumeDisplayUnit where
  | cubicCentimeter
  deriving DecidableEq, Repr

/-- Energy unit used by the stated work measurement. -/
inductive EnergyDisplayUnit where
  | joule
  deriving DecidableEq, Repr

/-- Qualitative geometry of the drawn process segment. -/
inductive SegmentShape where
  | horizontal
  deriving DecidableEq, Repr

/-- Direction of the arrow in the supplied `p`-`V` diagram. -/
inductive ArrowDirection where
  | towardDecreasingVolume
  deriving DecidableEq, Repr

/-- Thermodynamic classification of the displayed process. -/
inductive ProcessKind where
  | isobaricCompression
  deriving DecidableEq, Repr

/-- Sign convention attached to the positive `80 J` datum. -/
inductive WorkSignConvention where
  | workOnGasPositive
  deriving DecidableEq, Repr

/-!
The literal axes, ticks, pressure level, segment, and arrow in the primary
bitmap.  The physical values at the volume ticks remain independent fields;
their displayed ratios are recorded separately in `MatchesPrimaryPVDiagram`.
-/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  verticalAxisUnit : PressureDisplayUnit
  horizontalAxisUnitIsPrinted : Bool
  originLabelIsPrinted : Bool
  pressure200TickIsPrinted : Bool
  volumeTickLabelIsPrinted : VolumeTick → Bool
  pressureLevel : PressureQuantity
  volumeAtTick : VolumeTick → VolumeQuantity
  segmentPressure : PressureQuantity
  segmentStart : VolumeTick
  segmentFinish : VolumeTick
  segmentShape : SegmentShape
  arrowDirection : ArrowDirection

/-!
The gas process, its measured work, and the supplied diagram.  No numerical
value of `V₁` is built into this structure.
-/
structure IsobaricGasCompressionSetup where
  figure : PressureVolumeDiagram
  processKind : ProcessKind
  workOnGas : EnergyQuantity
  workSignConvention : WorkSignConvention
  statedWorkUnit : EnergyDisplayUnit
  requestedVolumeUnit : VolumeDisplayUnit

/-! ## Problem data and primary-image readouts -/

/-!
The prose datum and the units in which the measurement and requested answer
are stated.  This predicate contains the given `80 J`, but no value of `V₁`.
-/
structure MatchesProblemStatement
    (setup : IsobaricGasCompressionSetup) : Prop where
  work_is_positive_when_done_on_gas :
    setup.workSignConvention = .workOnGasPositive
  work_unit_is_joule : setup.statedWorkUnit = .joule
  work_done_on_gas_is_80_joules : energyInJoules setup.workOnGas = 80
  requested_volume_unit_is_cubic_centimeter :
    setup.requestedVolumeUnit = .cubicCentimeter

/-!
Exact transcription of the primary bitmap: pressure is on the vertical
`kPa` axis, volume is on the horizontal axis without a printed unit, the line
is horizontal at `200 kPa`, and its arrow runs left from `3V₁` to `V₁`.
The relations at the `2V₁` and `3V₁` ticks state only the figure's symbolic
scale; they do not assign the requested numerical value to `V₁`.
-/
structure MatchesPrimaryPVDiagram
    (setup : IsobaricGasCompressionSetup) : Prop where
  horizontal_axis_is_volume :
    setup.figure.horizontalAxisQuantity = .volumeV
  vertical_axis_is_pressure :
    setup.figure.verticalAxisQuantity = .pressureP
  pressure_axis_unit_is_kilopascal :
    setup.figure.verticalAxisUnit = .kilopascal
  no_volume_unit_is_printed_on_axis :
    setup.figure.horizontalAxisUnitIsPrinted = false
  origin_label_is_printed : setup.figure.originLabelIsPrinted = true
  pressure_200_tick_is_printed :
    setup.figure.pressure200TickIsPrinted = true
  every_volume_tick_label_is_printed :
    ∀ tick, setup.figure.volumeTickLabelIsPrinted tick = true
  pressure_level_is_200_kilopascals :
    pressureInKilopascals setup.figure.pressureLevel = 200
  segment_lies_at_pressure_level :
    setup.figure.segmentPressure = setup.figure.pressureLevel
  twice_V1_tick_relation :
    volumeInCubicMeters (setup.figure.volumeAtTick .twiceV1) =
      2 * volumeInCubicMeters (setup.figure.volumeAtTick .V1)
  thrice_V1_tick_relation :
    volumeInCubicMeters (setup.figure.volumeAtTick .thriceV1) =
      3 * volumeInCubicMeters (setup.figure.volumeAtTick .V1)
  segment_starts_at_thrice_V1 :
    setup.figure.segmentStart = .thriceV1
  segment_finishes_at_V1 : setup.figure.segmentFinish = .V1
  segment_is_horizontal : setup.figure.segmentShape = .horizontal
  arrow_points_toward_decreasing_volume :
    setup.figure.arrowDirection = .towardDecreasingVolume
  process_is_isobaric_compression :
    setup.processKind = .isobaricCompression

/-! ## Physical-domain conditions and governing law -/

/-- Positivity conditions selecting a nondegenerate physical compression. -/
structure HasPhysicalCompressionParameters
    (setup : IsobaricGasCompressionSetup) : Prop where
  pressure_positive : 0 < pressureInPascals setup.figure.segmentPressure
  volume_positive :
    ∀ tick, 0 < volumeInCubicMeters (setup.figure.volumeAtTick tick)
  work_on_gas_positive : 0 < energyInJoules setup.workOnGas

/-!
The coherent-SI boundary-work relation for an isobaric compression.  With
work on the gas taken as positive, `W_on = p (V_initial - V_final)`.
This predicate is a general physical relation among pressure, two volumes,
and work; it does not contain the figure's `200 kPa`, the measured `80 J`, or
the requested value of `V₁`.
-/
def IsobaricWorkDoneOnGas
    (pressure : PressureQuantity)
    (initialVolume finalVolume : VolumeQuantity)
    (workOnGas : EnergyQuantity) : Prop :=
  energyInJoules workOnGas =
    pressureInPascals pressure *
      (volumeInCubicMeters initialVolume -
        volumeInCubicMeters finalVolume)

/-!
The displayed process obeys the general isobaric boundary-work law at its
directed endpoints.  The endpoint ticks and their numerical readouts remain
the independent responsibility of the primary-figure predicate.
-/
structure SatisfiesIsobaricBoundaryWorkLaw
    (setup : IsobaricGasCompressionSetup) : Prop where
  boundary_work_for_displayed_compression :
    setup.processKind = .isobaricCompression →
      IsobaricWorkDoneOnGas
        setup.figure.segmentPressure
        (setup.figure.volumeAtTick setup.figure.segmentStart)
        (setup.figure.volumeAtTick setup.figure.segmentFinish)
        setup.workOnGas

/-! ## Displayed choices and requested conclusion -/

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Cubic-centimetre value displayed beside each answer label. -/
def AnswerChoice.volumeInCubicCentimeters : AnswerChoice → ℝ
  | .A => 600
  | .B => 400
  | .C => 200
  | .D => 1200

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The pressure, volume ratio, and work law give
`80 J = (200 kPa) (3V₁ - V₁)`, hence `V₁ = 200 cm³`, answer C.

Blueprint label: `thm:physics:phyx_mini_0404:target`.
-/
theorem referenceVolumeV1_eq_200_cubicCentimeters
    (setup : IsobaricGasCompressionSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPVDiagram setup)
    (_physical : HasPhysicalCompressionParameters setup)
    (_workLaw : SatisfiesIsobaricBoundaryWorkLaw setup) :
    volumeInCubicCentimeters (setup.figure.volumeAtTick .V1) = 200 ∧
      volumeInCubicCentimeters (setup.figure.volumeAtTick .V1) =
        recordedAnswerChoice.volumeInCubicCentimeters := by
  have hWork :=
    _workLaw.boundary_work_for_displayed_compression
      _figure.process_is_isobaric_compression
  unfold IsobaricWorkDoneOnGas at hWork
  have hPressure :
      pressureInPascals setup.figure.segmentPressure = 200000 := by
    rw [_figure.segment_lies_at_pressure_level]
    have h := _figure.pressure_level_is_200_kilopascals
    unfold pressureInKilopascals at h
    linarith
  have hInitial :
      volumeInCubicMeters
          (setup.figure.volumeAtTick setup.figure.segmentStart) =
        3 * volumeInCubicMeters (setup.figure.volumeAtTick .V1) := by
    rw [_figure.segment_starts_at_thrice_V1]
    exact _figure.thrice_V1_tick_relation
  have hFinal :
      volumeInCubicMeters
          (setup.figure.volumeAtTick setup.figure.segmentFinish) =
        volumeInCubicMeters (setup.figure.volumeAtTick .V1) := by
    rw [_figure.segment_finishes_at_V1]
  rw [_problem.work_done_on_gas_is_80_joules, hPressure, hInitial, hFinal] at hWork
  have hV1 :
      volumeInCubicCentimeters (setup.figure.volumeAtTick .V1) = 200 := by
    unfold volumeInCubicCentimeters
    nlinarith [hWork]
  constructor
  · exact hV1
  · simpa [recordedAnswerChoice, AnswerChoice.volumeInCubicCentimeters] using hV1

end PhyXMiniProblems.ProblemPhyXMini0404
