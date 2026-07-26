import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0070

open Dimension

/-!
# Empty-tank sightline to a meter-stick mark

The tank and meter-stick dimensions, together with the bottom intersection of
the viewing ray, are physical lengths independent of a unit choice. Numerical
figure labels and the requested mark are scalar readouts in centimeters. The
viewing angle is a dimensionless radian readout measured below the horizontal,
as shown in the primary image.
-/

/-- A physical length or signed one-dimensional displacement. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a dimensionful length in a chosen length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The scalar centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The material occupying the interior of the tank. -/
inductive TankContents where
  | emptyAir
  | liquid
  deriving DecidableEq, Repr

/-- Labeled corners of the rectangular tank cross-section. -/
inductive TankCorner where
  | upperLeft
  | upperRight
  | lowerLeft
  | lowerRight
  deriving DecidableEq, Repr

/-- The placement of the meter stick in the primary figure. -/
inductive MeterStickPlacement where
  | alongBottomWithZeroAtLeftEdge
  | elsewhere
  deriving DecidableEq, Repr

/-- The reference direction used for the displayed sightline angle. -/
inductive AngleReference where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-!
The physical quantities and categorical figure labels for the empty-tank
experiment. `sightlineBottomRun` is the unknown horizontal distance from the
stick's zero mark to the point where the straight viewing ray meets the stick;
no numerical value for that requested distance is stored in the setup.
-/
structure EmptyTankMeterStickSetup where
  tankLength : LengthQuantity
  tankHeight : LengthQuantity
  meterStickLength : LengthQuantity
  sightlineBottomRun : LengthQuantity
  sightlineAngleBelowReferenceRadians : ℝ
  contents : TankContents
  grazingCorner : TankCorner
  stickPlacement : MeterStickPlacement
  angleReference : AngleReference

/-!
Problem-statement and primary-figure data. The image reads a `100 cm` tank
length, a `50 cm` tank height, a meter stick extending along the bottom from
its zero mark at the left edge, and a sightline grazing the upper-left corner
at `30°` below the horizontal. The requested bottom mark is not a readout in
this predicate.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : EmptyTankMeterStickSetup) : Prop where
  tank_length_readout :
    lengthInCentimeters setup.tankLength = 100
  tank_height_readout :
    lengthInCentimeters setup.tankHeight = 50
  meter_stick_length_readout :
    lengthInCentimeters setup.meterStickLength = 100
  tank_is_empty :
    setup.contents = .emptyAir
  sightline_grazes_upper_left :
    setup.grazingCorner = .upperLeft
  stick_zero_is_at_left_bottom_edge :
    setup.stickPlacement = .alongBottomWithZeroAtLeftEdge
  displayed_angle_is_from_horizontal :
    setup.angleReference = .horizontal
  displayed_angle_readout :
    setup.sightlineAngleBelowReferenceRadians = Real.pi / 6

/-!
Positivity, an acute viewing angle, and the condition that the ray's bottom
intersection lies on both the tank bottom and the meter stick. These are branch
and range conditions, not a numerical assignment of the requested mark.
-/
structure HasDepictedPhysicalConfiguration
    (setup : EmptyTankMeterStickSetup) : Prop where
  tank_length_positive :
    0 < lengthInCentimeters setup.tankLength
  tank_height_positive :
    0 < lengthInCentimeters setup.tankHeight
  meter_stick_length_positive :
    0 < lengthInCentimeters setup.meterStickLength
  sightline_angle_positive :
    0 < setup.sightlineAngleBelowReferenceRadians
  sightline_angle_acute :
    setup.sightlineAngleBelowReferenceRadians < Real.pi / 2
  bottom_intersection_nonnegative :
    0 ≤ lengthInCentimeters setup.sightlineBottomRun
  bottom_intersection_in_tank :
    lengthInCentimeters setup.sightlineBottomRun ≤
      lengthInCentimeters setup.tankLength
  bottom_intersection_on_stick :
    lengthInCentimeters setup.sightlineBottomRun ≤
      lengthInCentimeters setup.meterStickLength

/-!
Rectilinear propagation through the homogeneous empty tank, expressed as the
right-triangle slope relation for the sightline from the upper-left rim to its
bottom intersection. It is required in every length unit, so the relation is
unit-covariant and is not specialized to the requested centimeter answer.
-/
def ObeysStraightSightlineGeometry
    (setup : EmptyTankMeterStickSetup) : Prop :=
  setup.contents = .emptyAir →
    ∀ unit : LengthUnit,
      lengthReadout unit setup.sightlineBottomRun *
          Real.tan setup.sightlineAngleBelowReferenceRadians =
        lengthReadout unit setup.tankHeight

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The whole-centimeter meter-stick mark printed beside each answer choice. -/
def answerMarkInCentimeters : AnswerChoice → ℕ
  | .A => 24
  | .B => 56
  | .C => 87
  | .D => 99

/-- The ray intersection rounds to a specified whole-centimeter stick mark. -/
def RoundsToWholeCentimeterMark
    (bottomRun : LengthQuantity) (markInCentimeters : ℕ) : Prop :=
  |lengthInCentimeters bottomRun - (markInCentimeters : ℝ)| < 1 / 2

/-- Agreement of the observed bottom intersection with a displayed choice. -/
def MatchesAnswerChoice
    (setup : EmptyTankMeterStickSetup) (choice : AnswerChoice) : Prop :=
  RoundsToWholeCentimeterMark setup.sightlineBottomRun
    (answerMarkInCentimeters choice)

/-!
The figure readouts and the unit-covariant straight-ray law yield the exact
centimeter slope relation before any rounding to a meter-stick mark.
-/
lemma sightlineBottomRun_centimeter_relation
    (setup : EmptyTankMeterStickSetup)
    (figure : MatchesProblemAndPrimaryFigure setup)
    (straightSightline : ObeysStraightSightlineGeometry setup) :
    lengthInCentimeters setup.sightlineBottomRun *
        Real.tan (Real.pi / 6) = 50 := by
  have h :=
    straightSightline figure.tank_is_empty LengthUnit.centimeters
  change
    lengthInCentimeters setup.sightlineBottomRun *
        Real.tan setup.sightlineAngleBelowReferenceRadians =
      lengthInCentimeters setup.tankHeight at h
  rw [figure.displayed_angle_readout, figure.tank_height_readout] at h
  exact h

/-!
For the empty `100 cm` by `50 cm` tank, the straight sightline grazing the
upper-left edge at `30°` below horizontal reaches the bottom at approximately
`86.6 cm` from the zero mark. Therefore the visible whole-centimeter mark is
`87 cm`, answer choice C.

This formalizes `thm:physics:phyx_mini_0070:target`.
-/
theorem problem_phyx_mini_0070
    (setup : EmptyTankMeterStickSetup)
    (figure : MatchesProblemAndPrimaryFigure setup)
    (physical : HasDepictedPhysicalConfiguration setup)
    (straightSightline : ObeysStraightSightlineGeometry setup) :
    RoundsToWholeCentimeterMark setup.sightlineBottomRun 87 ∧
      MatchesAnswerChoice setup .C := by
  have hrelation :=
    sightlineBottomRun_centimeter_relation setup figure straightSightline
  rw [Real.tan_pi_div_six] at hrelation
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ne : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrt_pos
  have hcancel :
      lengthInCentimeters setup.sightlineBottomRun =
        (lengthInCentimeters setup.sightlineBottomRun *
            (1 / Real.sqrt 3)) * Real.sqrt 3 := by
    field_simp [hsqrt_ne]
  have hrun :
      lengthInCentimeters setup.sightlineBottomRun = 50 * Real.sqrt 3 := by
    calc
      lengthInCentimeters setup.sightlineBottomRun =
          (lengthInCentimeters setup.sightlineBottomRun *
              (1 / Real.sqrt 3)) * Real.sqrt 3 := hcancel
      _ = 50 * Real.sqrt 3 := by rw [hrelation]
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (173 / 100 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), hsqrt_sq]
  have hsqrt_upper : Real.sqrt 3 < (7 / 4 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), hsqrt_sq]
  have hrun_lower :
      (173 / 2 : ℝ) < lengthInCentimeters setup.sightlineBottomRun := by
    rw [hrun]
    nlinarith
  have hrun_upper :
      lengthInCentimeters setup.sightlineBottomRun < (175 / 2 : ℝ) := by
    rw [hrun]
    nlinarith
  have hround :
      RoundsToWholeCentimeterMark setup.sightlineBottomRun 87 := by
    rw [RoundsToWholeCentimeterMark, abs_lt]
    constructor <;> norm_num at * <;> linarith
  constructor
  · exact hround
  · simpa [MatchesAnswerChoice, answerMarkInCentimeters] using hround

end PhyXMiniProblems.ProblemPhyXMini0070
