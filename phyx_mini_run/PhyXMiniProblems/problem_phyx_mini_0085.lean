import Mathlib.Data.Fintype.BigOperators
import Physlib.Units.WithDim.Speed

/- USER: The source file did not exist when this autoformalization task began. -/

/-!
# Travel time from pistol 3 through the plastic array

This file models the nine labelled plastic regions and the normal-incidence
path from pistol 3 to the central armadillo. Lengths, elapsed times, and speeds
are dimensionful Physlib quantities. Refractive indices and angles in radians
are dimensionless real readouts.
-/

namespace PhyXMiniProblems.ProblemPhyXMini0085

noncomputable section

open Dimension
open scoped BigOperators

/-- A physical length, independent of the unit system used to read it. -/
abbrev DimLength := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical duration, independent of the unit system used to read it. -/
abbrev DimTime := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical speed, independent of the unit system used to read it. -/
abbrev DimSpeed := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- SI unit choices except that lengths are displayed in millimeters. -/
def millimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.millimeters }

/-- SI unit choices except that times are displayed in picoseconds. -/
def picosecondUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.picoseconds }

/-- The nine plastic regions labelled in the figure. -/
inductive PlasticLayer where
  | n1
  | n2
  | n3
  | n4
  | n5
  | n6
  | n7
  | n8
  | n9
  deriving DecidableEq, Fintype, Repr

/-- The four laser pistols surrounding the rectangular array. -/
inductive LaserPistol where
  | pistol1
  | pistol2
  | pistol3
  | pistol4
  deriving DecidableEq, Fintype, Repr

/-- The four sides of the rectangular plastic array. -/
inductive ArraySide where
  | top
  | right
  | bottom
  | left
  deriving DecidableEq, Fintype, Repr

/-- The three successive pieces of pistol 3's path, ordered from outside in. -/
inductive Pistol3Segment where
  | outer
  | middle
  | inner
  deriving DecidableEq, Fintype, Repr

/-- Figure-derived identification of the plastic crossed by each pistol 3 segment. -/
def Pistol3Segment.layer : Pistol3Segment → PlasticLayer
  | .outer => .n9
  | .middle => .n8
  | .inner => .n7

/--
The material and layout data of the arcade target. A thickness is a physical
length, while each refractive index is a dimensionless material readout.
-/
structure ArcadeArraySetup where
  /-- Dimensionless refractive index of each labelled plastic region. -/
  refractiveIndex : PlasticLayer → ℝ
  /-- Thickness assigned to each labelled layer by the diagram. -/
  layerThickness : PlasticLayer → DimLength
  /-- Side of the array from which each numbered pistol fires. -/
  pistolSide : LaserPistol → ArraySide

/--
Physical quantities associated with one burst from pistol 3. Separate segment
times retain the additive time-of-flight law rather than baking the answer into
the total travel time.
-/
structure Pistol3Burst where
  /-- Geometrical distance travelled within each crossed layer. -/
  segmentPathLength : Pistol3Segment → DimLength
  /-- Propagation speed within each crossed layer. -/
  segmentSpeed : Pistol3Segment → DimSpeed
  /-- Incidence angle from the interface normal, in radians. -/
  incidenceAngleRadians : Pistol3Segment → ℝ
  /-- Time spent in each crossed layer. -/
  segmentTravelTime : Pistol3Segment → DimTime
  /-- Total time spent traversing all plastic layers before reaching the target. -/
  totalTravelTime : DimTime

/-- A layer has one of the two thickness readouts stated in the problem. -/
def HasAllowedThickness (setup : ArcadeArraySetup) (layer : PlasticLayer) : Prop :=
  (setup.layerThickness layer millimeterUnitChoices).val = 2 ∨
    (setup.layerThickness layer millimeterUnitChoices).val = 4

/--
Numerical and geometrical readouts supplied by the text and figure. The bottom
ray from pistol 3 crosses `n₉`, `n₈`, and `n₇`; their normal thicknesses are
respectively `2 mm`, `2 mm`, and `4 mm`.
-/
structure ArcadeArrayFigureReadouts
    (setup : ArcadeArraySetup) (burst : Pistol3Burst) : Prop where
  pistol1_at_top : setup.pistolSide .pistol1 = .top
  pistol2_at_right : setup.pistolSide .pistol2 = .right
  pistol3_at_bottom : setup.pistolSide .pistol3 = .bottom
  pistol4_at_left : setup.pistolSide .pistol4 = .left
  all_thicknesses_are_two_or_four : ∀ layer, HasAllowedThickness setup layer
  n9_thickness : (setup.layerThickness .n9 millimeterUnitChoices).val = 2
  n8_thickness : (setup.layerThickness .n8 millimeterUnitChoices).val = 2
  n7_thickness : (setup.layerThickness .n7 millimeterUnitChoices).val = 4
  n1_index : setup.refractiveIndex .n1 = (31 : ℝ) / 20
  n2_index : setup.refractiveIndex .n2 = (17 : ℝ) / 10
  n3_index : setup.refractiveIndex .n3 = (29 : ℝ) / 20
  n4_index : setup.refractiveIndex .n4 = (8 : ℝ) / 5
  n5_index : setup.refractiveIndex .n5 = (29 : ℝ) / 20
  n6_index : setup.refractiveIndex .n6 = (161 : ℝ) / 100
  n7_index : setup.refractiveIndex .n7 = (159 : ℝ) / 100
  n8_index : setup.refractiveIndex .n8 = (17 : ℝ) / 10
  n9_index : setup.refractiveIndex .n9 = (8 : ℝ) / 5
  pistol3_is_normally_incident :
    ∀ segment, burst.incidenceAngleRadians segment = 0

/--
The geometrical-optics and constant-speed laws used for the time-of-flight
calculation. No numerical value for the total travel time occurs here.
-/
structure Pistol3TransitLaws
    (setup : ArcadeArraySetup) (burst : Pistol3Burst) : Prop where
  refractive_indices_positive : ∀ layer, 0 < setup.refractiveIndex layer
  layer_thicknesses_positive :
    ∀ layer, 0 < (setup.layerThickness layer UnitChoices.SI).val
  segment_speeds_positive :
    ∀ segment, 0 < (burst.segmentSpeed segment UnitChoices.SI).val
  segment_times_nonnegative :
    ∀ segment, 0 ≤ (burst.segmentTravelTime segment UnitChoices.SI).val
  /-- At normal incidence, the in-layer path length equals the layer thickness. -/
  normal_incidence_path_length : ∀ segment units,
    (burst.segmentPathLength segment units).val =
      (setup.layerThickness segment.layer units).val
  /-- In a medium of index `n`, the light speed is the vacuum speed divided by `n`. -/
  speed_refractive_index_law : ∀ segment units,
    (burst.segmentSpeed segment units).val *
        setup.refractiveIndex segment.layer =
      (DimSpeed.speedOfLight units).val
  /-- Distance equals constant speed times elapsed time on each path segment. -/
  uniform_speed_on_segment : ∀ segment units,
    (burst.segmentPathLength segment units).val =
      (burst.segmentSpeed segment units).val *
        (burst.segmentTravelTime segment units).val
  /-- The burst's total traversal time is the sum of its three segment times. -/
  total_time_is_sum : ∀ units,
    (burst.totalTravelTime units).val =
      ∑ segment : Pistol3Segment,
        (burst.segmentTravelTime segment units).val

/-- The four travel-time choices displayed by the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Picosecond readout printed beside each answer choice. -/
def AnswerChoice.timePicoseconds : AnswerChoice → ℝ
  | .A => 85 / 2
  | .B => 87 / 2
  | .C => 216 / 5
  | .D => 214 / 5

/--
A computed time agrees with a one-decimal-place displayed answer. The tolerance
`0.05 ps` is half a unit in the last printed decimal place.
-/
def MatchesAnswerChoice (travelTime : DimTime) (choice : AnswerChoice) : Prop :=
  |(travelTime picosecondUnitChoices).val - choice.timePicoseconds| ≤ 1 / 20

/--
For pistol 3's bottom-to-center path, the refractive-index speed law,
normal-incidence geometry, and additive transit time give answer C:
`43.2 × 10⁻¹² s`, to the precision displayed by the answer choice.

Blueprint label: `thm:physics:phyx_mini_0085:target`.
-/
theorem pistol3_travel_time_is_answer_C
    (setup : ArcadeArraySetup)
    (burst : Pistol3Burst)
    (_figure : ArcadeArrayFigureReadouts setup burst)
    (_laws : Pistol3TransitLaws setup burst) :
    MatchesAnswerChoice burst.totalTravelTime .C := by
  let units : UnitChoices :=
    { UnitChoices.SI with
      length := LengthUnit.millimeters
      time := TimeUnit.picoseconds }
  have h_n9_thickness :
      (setup.layerThickness .n9 units).val = 2 := by
    have hscale := congrArg WithDim.val
      ((setup.layerThickness .n9).2 millimeterUnitChoices units)
    rw [hscale]
    simp only [WithDim.smul_val]
    rw [_figure.n9_thickness]
    simp [units, millimeterUnitChoices, UnitChoices.dimScale]
  have h_n8_thickness :
      (setup.layerThickness .n8 units).val = 2 := by
    have hscale := congrArg WithDim.val
      ((setup.layerThickness .n8).2 millimeterUnitChoices units)
    rw [hscale]
    simp only [WithDim.smul_val]
    rw [_figure.n8_thickness]
    simp [units, millimeterUnitChoices, UnitChoices.dimScale]
  have h_n7_thickness :
      (setup.layerThickness .n7 units).val = 4 := by
    have hscale := congrArg WithDim.val
      ((setup.layerThickness .n7).2 millimeterUnitChoices units)
    rw [hscale]
    simp only [WithDim.smul_val]
    rw [_figure.n7_thickness]
    simp [units, millimeterUnitChoices, UnitChoices.dimScale]
  have h_c :
      (DimSpeed.speedOfLight units).val =
        (149896229 : ℝ) / 500000000 := by
    simp [DimSpeed.speedOfLight, units,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale, LengthUnit.millimeters,
      TimeUnit.picoseconds]
    rw [NNReal.rpow_neg_one]
    simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_mul, NNReal.coe_inv]
    change
      (10 : ℝ) ^ 3 * ((10 : ℝ) ^ 12)⁻¹ * 299792458 =
        (149896229 : ℝ) / 500000000
    norm_num
  have h_outer :
      (DimSpeed.speedOfLight units).val *
          (burst.segmentTravelTime .outer units).val =
        (16 : ℝ) / 5 := by
    calc
      (DimSpeed.speedOfLight units).val *
            (burst.segmentTravelTime .outer units).val =
          ((burst.segmentSpeed .outer units).val *
              setup.refractiveIndex .n9) *
            (burst.segmentTravelTime .outer units).val := by
              apply congrArg (fun x : ℝ =>
                x * (burst.segmentTravelTime .outer units).val)
              simpa only [Pistol3Segment.layer] using
                (_laws.speed_refractive_index_law .outer units).symm
      _ = setup.refractiveIndex .n9 *
            ((burst.segmentSpeed .outer units).val *
              (burst.segmentTravelTime .outer units).val) := by ring
      _ = setup.refractiveIndex .n9 *
            (burst.segmentPathLength .outer units).val := by
              rw [_laws.uniform_speed_on_segment .outer units]
      _ = setup.refractiveIndex .n9 *
            (setup.layerThickness .n9 units).val := by
              apply congrArg (fun x : ℝ =>
                setup.refractiveIndex .n9 * x)
              simpa only [Pistol3Segment.layer] using
                _laws.normal_incidence_path_length .outer units
      _ = (16 : ℝ) / 5 := by
              rw [_figure.n9_index, h_n9_thickness]
              norm_num
  have h_middle :
      (DimSpeed.speedOfLight units).val *
          (burst.segmentTravelTime .middle units).val =
        (17 : ℝ) / 5 := by
    calc
      (DimSpeed.speedOfLight units).val *
            (burst.segmentTravelTime .middle units).val =
          ((burst.segmentSpeed .middle units).val *
              setup.refractiveIndex .n8) *
            (burst.segmentTravelTime .middle units).val := by
              apply congrArg (fun x : ℝ =>
                x * (burst.segmentTravelTime .middle units).val)
              simpa only [Pistol3Segment.layer] using
                (_laws.speed_refractive_index_law .middle units).symm
      _ = setup.refractiveIndex .n8 *
            ((burst.segmentSpeed .middle units).val *
              (burst.segmentTravelTime .middle units).val) := by ring
      _ = setup.refractiveIndex .n8 *
            (burst.segmentPathLength .middle units).val := by
              rw [_laws.uniform_speed_on_segment .middle units]
      _ = setup.refractiveIndex .n8 *
            (setup.layerThickness .n8 units).val := by
              apply congrArg (fun x : ℝ =>
                setup.refractiveIndex .n8 * x)
              simpa only [Pistol3Segment.layer] using
                _laws.normal_incidence_path_length .middle units
      _ = (17 : ℝ) / 5 := by
              rw [_figure.n8_index, h_n8_thickness]
              norm_num
  have h_inner :
      (DimSpeed.speedOfLight units).val *
          (burst.segmentTravelTime .inner units).val =
        (159 : ℝ) / 25 := by
    calc
      (DimSpeed.speedOfLight units).val *
            (burst.segmentTravelTime .inner units).val =
          ((burst.segmentSpeed .inner units).val *
              setup.refractiveIndex .n7) *
            (burst.segmentTravelTime .inner units).val := by
              apply congrArg (fun x : ℝ =>
                x * (burst.segmentTravelTime .inner units).val)
              simpa only [Pistol3Segment.layer] using
                (_laws.speed_refractive_index_law .inner units).symm
      _ = setup.refractiveIndex .n7 *
            ((burst.segmentSpeed .inner units).val *
              (burst.segmentTravelTime .inner units).val) := by ring
      _ = setup.refractiveIndex .n7 *
            (burst.segmentPathLength .inner units).val := by
              rw [_laws.uniform_speed_on_segment .inner units]
      _ = setup.refractiveIndex .n7 *
            (setup.layerThickness .n7 units).val := by
              apply congrArg (fun x : ℝ =>
                setup.refractiveIndex .n7 * x)
              simpa only [Pistol3Segment.layer] using
                _laws.normal_incidence_path_length .inner units
      _ = (159 : ℝ) / 25 := by
              rw [_figure.n7_index, h_n7_thickness]
              norm_num
  have h_total_is_three_terms :
      (burst.totalTravelTime units).val =
        (burst.segmentTravelTime .outer units).val +
          (burst.segmentTravelTime .middle units).val +
            (burst.segmentTravelTime .inner units).val := by
    classical
    have h_univ :
        (Finset.univ : Finset Pistol3Segment) =
          {.outer, .middle, .inner} := by
      ext segment
      fin_cases segment <;> simp
    rw [_laws.total_time_is_sum units, h_univ]
    simp
    ring
  have h_total_optical_length :
      (DimSpeed.speedOfLight units).val *
          (burst.totalTravelTime units).val =
        (324 : ℝ) / 25 := by
    rw [h_total_is_three_terms]
    calc
      (DimSpeed.speedOfLight units).val *
            ((burst.segmentTravelTime .outer units).val +
              (burst.segmentTravelTime .middle units).val +
                (burst.segmentTravelTime .inner units).val) =
          (DimSpeed.speedOfLight units).val *
              (burst.segmentTravelTime .outer units).val +
            (DimSpeed.speedOfLight units).val *
              (burst.segmentTravelTime .middle units).val +
            (DimSpeed.speedOfLight units).val *
              (burst.segmentTravelTime .inner units).val := by ring
      _ = (324 : ℝ) / 25 := by
            rw [h_outer, h_middle, h_inner]
            norm_num
  have h_total_time_units :
      (burst.totalTravelTime picosecondUnitChoices).val =
        (burst.totalTravelTime units).val := by
    have hscale := congrArg WithDim.val
      ((burst.totalTravelTime).2 units picosecondUnitChoices)
    simpa [units, picosecondUnitChoices, UnitChoices.dimScale] using hscale
  rw [MatchesAnswerChoice, h_total_time_units]
  change
    |(burst.totalTravelTime units).val - (216 : ℝ) / 5| ≤
      (1 : ℝ) / 20
  rw [abs_le]
  rw [h_c] at h_total_optical_length
  constructor <;> nlinarith [h_total_optical_length]

end

end PhyXMiniProblems.ProblemPhyXMini0085
