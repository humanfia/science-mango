import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0676

open Dimension

/-!
# Measuring the width of a straight river by triangulation

A surveyor begins at the point on the near bank directly opposite a tree,
walks a baseline of length `d` along that bank, and sights the tree from the
baseline endpoint. The baseline, river-width crossing, and sight line form a
right triangle. Lengths are dimensionful physical quantities whose scalar SI
readouts are used in the trigonometric relation; the sight angle is a radian
readout.
-/

/-- A physical length, independent of the unit system used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The three labeled points in the river-survey construction. -/
inductive SurveyPoint where
  | tree
  | baselineStart
  | sightingStation
  deriving DecidableEq, Repr

/-- The two sides of the river shown in the primary figure. -/
inductive RiverBankSide where
  | near
  | opposite
  deriving DecidableEq, Repr

/--
The physical quantities and the smallest relational geometry interface needed
to retain the scenario and primary-figure labels.

`baselineDistanceD` is the walked bank distance labeled `d`, `riverWidth` is
the perpendicular distance between the straight banks, and
`sightAngleThetaRadians` is the angle labeled `θ` at the sighting station.
The relational fields distinguish the figure's baseline and sight line from
mere numerical lengths.
-/
structure RiverSurveySetup where
  baselineDistanceD : LengthQuantity
  riverWidth : LengthQuantity
  sightAngleThetaRadians : ℝ
  bankOf : SurveyPoint → RiverBankSide
  directlyAcross : SurveyPoint → SurveyPoint → Prop
  joinedByBaseline : SurveyPoint → SurveyPoint → Prop
  joinedBySightLine : SurveyPoint → SurveyPoint → Prop
  banksAreStraightAndParallel : Prop
  treeToStartCrossingIsPerpendicularToBanks : Prop
  thetaIsAngleAtStationBetweenBaselineAndSightLine : Prop

/--
The categorical and incidence information read from the primary diagram and
the statement that the surveyor starts directly opposite the tree. No metric
value of the river width occurs here.
-/
structure MatchesPrimaryRiverSurveyFigure
    (setup : RiverSurveySetup) : Prop where
  tree_on_opposite_bank : setup.bankOf .tree = .opposite
  baseline_start_on_near_bank : setup.bankOf .baselineStart = .near
  sighting_station_on_near_bank : setup.bankOf .sightingStation = .near
  start_directly_opposite_tree :
    setup.directlyAcross .baselineStart .tree
  baseline_joins_start_to_station :
    setup.joinedByBaseline .baselineStart .sightingStation
  sight_line_joins_station_to_tree :
    setup.joinedBySightLine .sightingStation .tree
  straight_parallel_banks : setup.banksAreStraightAndParallel
  width_crossing_is_perpendicular :
    setup.treeToStartCrossingIsPerpendicularToBanks
  theta_has_depicted_vertex_and_rays :
    setup.thetaIsAngleAtStationBetweenBaselineAndSightLine

/-- Positive physical lengths and the acute branch of the depicted angle. -/
structure HasPhysicalRiverSurveyConfiguration
    (setup : RiverSurveySetup) : Prop where
  baseline_distance_positive : 0 < lengthInMeters setup.baselineDistanceD
  river_width_positive : 0 < lengthInMeters setup.riverWidth
  sight_angle_acute :
    setup.sightAngleThetaRadians ∈ Set.Ioo 0 (Real.pi / 2)

/--
The two calibrated measurements stated in the problem: a `100 m` baseline and
a `35°` sight angle. The angle equality explicitly converts degrees to the
radian readout used by `Real.tan`.
-/
structure MatchesProblemMeasurements
    (setup : RiverSurveySetup) : Prop where
  baseline_is_100_metres : lengthInMeters setup.baselineDistanceD = 100
  sight_angle_is_35_degrees :
    setup.sightAngleThetaRadians = (35 : ℝ) * Real.pi / 180

/--
The governing right-triangle relation `tan θ = width / d`, written without a
division by the positive baseline length. This is the generic triangulation
law, not the requested numerical conclusion.
-/
def SatisfiesRightTriangleTangentLaw
    (setup : RiverSurveySetup) : Prop :=
  lengthInMeters setup.riverWidth =
    lengthInMeters setup.baselineDistanceD *
      Real.tan setup.sightAngleThetaRadians

/-- Labels of the four multiple-choice answers in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The river-width readout, in metres, printed beside each answer choice. -/
def answerWidthMeters : AnswerChoice → ℝ
  | .A => 24
  | .B => 35
  | .C => 70
  | .D => 65

/-- A physical width rounds to a displayed answer at one decimal place. -/
def MatchesAnswerToNearestTenth
    (width : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters width - answerWidthMeters choice| < (1 : ℝ) / 20

/-- A choice is strictly closer to a metre readout than every other choice. -/
def IsUniqueClosestAnswer
    (widthMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |widthMeters - answerWidthMeters choice| <
      |widthMeters - answerWidthMeters other|

/--
For the `100 m` baseline and `35°` sight angle in the straight-river figure,
right-triangle triangulation gives a width that rounds to `70.0 m`, and hence
the unique closest listed answer is choice C.

This formalizes `thm:physics:phyx_mini_0676:target`.
-/
theorem riverWidth_is_70_metres_answer_C
    (setup : RiverSurveySetup)
    (_figure : MatchesPrimaryRiverSurveyFigure setup)
    (_physical : HasPhysicalRiverSurveyConfiguration setup)
    (_measurements : MatchesProblemMeasurements setup)
    (_tangentLaw : SatisfiesRightTriangleTangentLaw setup) :
    MatchesAnswerToNearestTenth setup.riverWidth .C ∧
      IsUniqueClosestAnswer (lengthInMeters setup.riverWidth) .C := by
  have hwidth :
      lengthInMeters setup.riverWidth =
        100 * Real.tan (7 * Real.pi / 36) := by
    rw [SatisfiesRightTriangleTangentLaw,
      _measurements.baseline_is_100_metres,
      _measurements.sight_angle_is_35_degrees] at _tangentLaw
    convert _tangentLaw using 1
    ring_nf
  have htan_bounds :
      (1399 / 2000 : ℝ) < Real.tan (7 * Real.pi / 36) ∧
        Real.tan (7 * Real.pi / 36) < (1401 / 2000 : ℝ) := by
    let x : ℝ := 7 * Real.pi / 36
    let t : ℝ := Real.tan x
    let q : ℝ := Real.sqrt 3
    change (1399 / 2000 : ℝ) < t ∧ t < (1401 / 2000 : ℝ)
    have hxmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [x]
      constructor <;> nlinarith only [Real.pi_pos]
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hxlt : x < Real.pi / 2 := hxmem.2
    have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxmem
    have hcosne : Real.cos x ≠ 0 := ne_of_gt hcospos
    have htan_cos : t * Real.cos x = Real.sin x := by
      dsimp [t]
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have hq_sq : q ^ 2 = (3 : ℝ) := by
      dsimp [q]
      exact Real.sq_sqrt (by norm_num)
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      positivity
    have hq_lower : (1732 / 1000 : ℝ) < q := by
      nlinarith only [hq_sq, hq_nonneg]
    have hq_upper : q < (1733 / 1000 : ℝ) := by
      nlinarith only [hq_sq, hq_nonneg]
    have htrig :
        Real.sin (3 * x) + (2 + q) * Real.cos (3 * x) = 0 := by
      dsimp [x, q]
      rw [show 3 * (7 * Real.pi / 36) =
          Real.pi / 3 + Real.pi / 4 by ring,
        Real.sin_add, Real.cos_add, Real.sin_pi_div_three,
        Real.cos_pi_div_three, Real.sin_pi_div_four,
        Real.cos_pi_div_four]
      calc
        Real.sqrt 3 / 2 * (Real.sqrt 2 / 2) +
              1 / 2 * (Real.sqrt 2 / 2) +
              (2 + Real.sqrt 3) *
                (1 / 2 * (Real.sqrt 2 / 2) -
                  Real.sqrt 3 / 2 * (Real.sqrt 2 / 2)) =
            (3 - Real.sqrt 3 ^ 2) * Real.sqrt 2 / 4 := by
              ring
        _ = 0 := by
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
          ring
    rw [Real.sin_three_mul, Real.cos_three_mul, ← htan_cos] at htrig
    have hH :
        3 * t - 4 * t ^ 3 * Real.cos x ^ 2 +
            (2 + q) * (4 * Real.cos x ^ 2 - 3) = 0 := by
      apply (mul_left_cancel₀ hcosne)
      calc
        Real.cos x *
              (3 * t - 4 * t ^ 3 * Real.cos x ^ 2 +
                (2 + q) * (4 * Real.cos x ^ 2 - 3)) =
            3 * (t * Real.cos x) - 4 * (t * Real.cos x) ^ 3 +
              (2 + q) * (4 * Real.cos x ^ 3 - 3 * Real.cos x) := by
                ring
        _ = 0 := htrig
        _ = Real.cos x * 0 := by ring
    have hunit : Real.cos x ^ 2 * (1 + t ^ 2) = 1 := by
      have hsincos := Real.sin_sq_add_cos_sq x
      rw [← htan_cos] at hsincos
      calc
        Real.cos x ^ 2 * (1 + t ^ 2) =
            (t * Real.cos x) ^ 2 + Real.cos x ^ 2 := by ring
        _ = 1 := hsincos
    have hid :
        (3 * t - 4 * t ^ 3 * Real.cos x ^ 2 +
            (2 + q) * (4 * Real.cos x ^ 2 - 3)) +
          (t ^ 3 + 3 * (2 + q) * t ^ 2 - 3 * t - (2 + q)) *
            Real.cos x ^ 2 = 0 := by
      calc
        _ = 3 * (t - (2 + q)) *
            (1 - Real.cos x ^ 2 * (1 + t ^ 2)) := by ring
        _ = 0 := by
          rw [hunit]
          ring
    have hPc :
        (t ^ 3 + 3 * (2 + q) * t ^ 2 - 3 * t - (2 + q)) *
            Real.cos x ^ 2 = 0 := by
      linarith only [hH, hid]
    have hP :
        t ^ 3 + 3 * (2 + q) * t ^ 2 - 3 * t - (2 + q) = 0 := by
      rcases mul_eq_zero.mp hPc with hp | hc
      · exact hp
      · exact (pow_ne_zero 2 hcosne hc).elim
    have hx_six : Real.pi / 6 < x := by
      dsimp [x]
      nlinarith only [Real.pi_pos]
    have htan_six_lt : Real.tan (Real.pi / 6) < t := by
      dsimp [t]
      exact Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
        (by positivity) hxlt hx_six
    have hq_pos : 0 < q := lt_trans (by norm_num) hq_lower
    have hq_lt_two : q < 2 := by
      linarith only [hq_upper]
    have hhalf_lt_tan_six :
        (1 / 2 : ℝ) < Real.tan (Real.pi / 6) := by
      rw [Real.tan_pi_div_six]
      rw [lt_div_iff₀ (by
        dsimp [q] at hq_pos ⊢
        exact hq_pos)]
      dsimp [q] at hq_lt_two ⊢
      nlinarith only [hq_lt_two]
    have ht_lower_coarse : (1 / 2 : ℝ) < t :=
      hhalf_lt_tan_six.trans htan_six_lt
    have ha_coeff :
        0 < 3 * (1399 / 2000 : ℝ) ^ 2 - 1 := by
      norm_num
    have hpa :
        (1399 / 2000 : ℝ) ^ 3 +
            3 * (2 + q) * (1399 / 2000 : ℝ) ^ 2 -
            3 * (1399 / 2000 : ℝ) - (2 + q) < 0 := by
      calc
        _ < (1399 / 2000 : ℝ) ^ 3 +
              3 * (2 + (1733 / 1000 : ℝ)) *
                (1399 / 2000 : ℝ) ^ 2 -
              3 * (1399 / 2000 : ℝ) -
                (2 + (1733 / 1000 : ℝ)) := by
            nlinarith only [hq_upper, ha_coeff]
        _ < 0 := by norm_num
    have hb_coeff :
        0 < 3 * (1401 / 2000 : ℝ) ^ 2 - 1 := by
      norm_num
    have hpb :
        0 < (1401 / 2000 : ℝ) ^ 3 +
            3 * (2 + q) * (1401 / 2000 : ℝ) ^ 2 -
            3 * (1401 / 2000 : ℝ) - (2 + q) := by
      calc
        0 < (1401 / 2000 : ℝ) ^ 3 +
              3 * (2 + (1732 / 1000 : ℝ)) *
                (1401 / 2000 : ℝ) ^ 2 -
              3 * (1401 / 2000 : ℝ) -
                (2 + (1732 / 1000 : ℝ)) := by norm_num
        _ < _ := by
          nlinarith only [hq_lower, hb_coeff]
    constructor
    · by_contra hnot
      have htle : t ≤ (1399 / 2000 : ℝ) := le_of_not_gt hnot
      have hsum : 1 < t + (1399 / 2000 : ℝ) := by
        nlinarith only [ht_lower_coarse]
      have hA : 3 < 2 + q := by
        linarith only [hq_lower]
      have hmul :
          3 < (2 + q) * (t + (1399 / 2000 : ℝ)) := by
        have h1 :
            0 < ((2 + q) - 3) * (t + (1399 / 2000 : ℝ)) :=
          mul_pos (by linarith only [hA]) (by linarith only [hsum])
        have h2 :
            0 < 3 * ((t + (1399 / 2000 : ℝ)) - 1) :=
          mul_pos (by norm_num) (by linarith only [hsum])
        nlinarith only [h1, h2]
      have htail :
          0 <
            3 * (2 + q) * (t + (1399 / 2000 : ℝ)) - 3 := by
        nlinarith only [hmul]
      have hBpos :
          0 < t ^ 2 + t * (1399 / 2000 : ℝ) +
              (1399 / 2000 : ℝ) ^ 2 +
              3 * (2 + q) * (t + (1399 / 2000 : ℝ)) - 3 := by
        have htt : 0 ≤ t ^ 2 := sq_nonneg t
        have hta : 0 < t * (1399 / 2000 : ℝ) :=
          mul_pos (by linarith only [ht_lower_coarse])
            (by norm_num)
        have haa : 0 ≤ (1399 / 2000 : ℝ) ^ 2 :=
          sq_nonneg _
        nlinarith only [htt, hta, haa, htail]
      have hfactor :
          (t ^ 3 + 3 * (2 + q) * t ^ 2 - 3 * t - (2 + q)) -
              ((1399 / 2000 : ℝ) ^ 3 +
                3 * (2 + q) * (1399 / 2000 : ℝ) ^ 2 -
                3 * (1399 / 2000 : ℝ) - (2 + q)) =
            (t - (1399 / 2000 : ℝ)) *
              (t ^ 2 + t * (1399 / 2000 : ℝ) +
                (1399 / 2000 : ℝ) ^ 2 +
                3 * (2 + q) * (t + (1399 / 2000 : ℝ)) - 3) := by
        ring
      have hnonpos :
          (t - (1399 / 2000 : ℝ)) *
              (t ^ 2 + t * (1399 / 2000 : ℝ) +
                (1399 / 2000 : ℝ) ^ 2 +
                3 * (2 + q) * (t + (1399 / 2000 : ℝ)) - 3) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htle) hBpos.le
      nlinarith only [hP, hpa, hfactor, hnonpos]
    · by_contra hnot
      have hbt : (1401 / 2000 : ℝ) ≤ t := le_of_not_gt hnot
      have hsum : 1 < t + (1401 / 2000 : ℝ) := by
        nlinarith only [ht_lower_coarse]
      have hA : 3 < 2 + q := by
        linarith only [hq_lower]
      have hmul :
          3 < (2 + q) * (t + (1401 / 2000 : ℝ)) := by
        have h1 :
            0 < ((2 + q) - 3) * (t + (1401 / 2000 : ℝ)) :=
          mul_pos (by linarith only [hA]) (by linarith only [hsum])
        have h2 :
            0 < 3 * ((t + (1401 / 2000 : ℝ)) - 1) :=
          mul_pos (by norm_num) (by linarith only [hsum])
        nlinarith only [h1, h2]
      have htail :
          0 <
            3 * (2 + q) * (t + (1401 / 2000 : ℝ)) - 3 := by
        nlinarith only [hmul]
      have hBpos :
          0 < t ^ 2 + t * (1401 / 2000 : ℝ) +
              (1401 / 2000 : ℝ) ^ 2 +
              3 * (2 + q) * (t + (1401 / 2000 : ℝ)) - 3 := by
        have htt : 0 ≤ t ^ 2 := sq_nonneg t
        have hta : 0 < t * (1401 / 2000 : ℝ) :=
          mul_pos (by linarith only [ht_lower_coarse])
            (by norm_num)
        have hbb : 0 ≤ (1401 / 2000 : ℝ) ^ 2 :=
          sq_nonneg _
        nlinarith only [htt, hta, hbb, htail]
      have hfactor :
          (t ^ 3 + 3 * (2 + q) * t ^ 2 - 3 * t - (2 + q)) -
              ((1401 / 2000 : ℝ) ^ 3 +
                3 * (2 + q) * (1401 / 2000 : ℝ) ^ 2 -
                3 * (1401 / 2000 : ℝ) - (2 + q)) =
            (t - (1401 / 2000 : ℝ)) *
              (t ^ 2 + t * (1401 / 2000 : ℝ) +
                (1401 / 2000 : ℝ) ^ 2 +
                3 * (2 + q) * (t + (1401 / 2000 : ℝ)) - 3) := by
        ring
      have hnonneg :
          0 ≤ (t - (1401 / 2000 : ℝ)) *
              (t ^ 2 + t * (1401 / 2000 : ℝ) +
                (1401 / 2000 : ℝ) ^ 2 +
                3 * (2 + q) * (t + (1401 / 2000 : ℝ)) - 3) :=
        mul_nonneg (sub_nonneg.mpr hbt) hBpos.le
      nlinarith only [hP, hpb, hfactor, hnonneg]
  have hwidth_lower :
      (1399 / 20 : ℝ) < lengthInMeters setup.riverWidth := by
    rw [hwidth]
    nlinarith only [htan_bounds.1]
  have hwidth_upper :
      lengthInMeters setup.riverWidth < (1401 / 20 : ℝ) := by
    rw [hwidth]
    nlinarith only [htan_bounds.2]
  have hround :
      |lengthInMeters setup.riverWidth - 70| < (1 : ℝ) / 20 := by
    rw [abs_lt]
    constructor <;> nlinarith only [hwidth_lower, hwidth_upper]
  constructor
  · exact hround
  · unfold IsUniqueClosestAnswer
    intro other hne
    cases other with
    | A =>
        have hfar :
            (1 : ℝ) / 20 <
              |lengthInMeters setup.riverWidth - answerWidthMeters .A| := by
          simp only [answerWidthMeters]
          rw [abs_of_pos (by nlinarith only [hwidth_lower])]
          nlinarith only [hwidth_lower]
        exact hround.trans hfar
    | B =>
        have hfar :
            (1 : ℝ) / 20 <
              |lengthInMeters setup.riverWidth - answerWidthMeters .B| := by
          simp only [answerWidthMeters]
          rw [abs_of_pos (by nlinarith only [hwidth_lower])]
          nlinarith only [hwidth_lower]
        exact hround.trans hfar
    | C =>
        exact (hne rfl).elim
    | D =>
        have hfar :
            (1 : ℝ) / 20 <
              |lengthInMeters setup.riverWidth - answerWidthMeters .D| := by
          simp only [answerWidthMeters]
          rw [abs_of_pos (by nlinarith only [hwidth_lower])]
          nlinarith only [hwidth_lower]
        exact hround.trans hfar

end PhyXMiniProblems.ProblemPhyXMini0676
