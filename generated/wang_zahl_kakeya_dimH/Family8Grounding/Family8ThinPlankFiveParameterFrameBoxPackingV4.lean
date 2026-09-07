import Family8Grounding.Family8ThinPlankFiveParameterPackingV2
import Submission.Kakeya.ConvexFactoring.CertifiedInducedThickeningLower
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8ThinPlankFiveParameterFrameBoxPackingV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8ThinPlankEssentialDistinctPackingV4
open Family8ThinPlankFiveParameterPackingV2

noncomputable section

/-!
# Actual FrameBox inputs for the five-parameter thin-plank packing kernel

The five scalar bounds used by the finite code are derived here from literal
containment of each tube carrier in one oriented frame box.  The only
orientation premise retained is that all axes use the forward long direction.
-/

/-- The sharp half-sum version of the elementary FrameBox radius estimate. -/
theorem frameBox_dist_center_le_half_sum_side
    (B : FrameBox) {y : Space} (hy : y ∈ B.carrier) :
    dist y B.center ≤ ((∑ i, B.side i : NNReal) : Real) / 2 := by
  have hrepr :
      ∑ i, ⟪B.frame i, y - B.center⟫_Real • B.frame i = y - B.center :=
    B.frame.sum_repr' (y - B.center)
  have hcoord (i : Fin 3) :
      |⟪B.frame i, y - B.center⟫_Real| ≤ (B.side i : Real) / 2 := by
    simpa [inner_sub_right] using
      B.centeredCoordinate_abs_le_halfSide hy i
  rw [dist_eq_norm, ← hrepr]
  calc
    ‖∑ i, ⟪B.frame i, y - B.center⟫_Real • B.frame i‖ ≤
        ∑ i, ‖⟪B.frame i, y - B.center⟫_Real • B.frame i‖ :=
      norm_sum_le _ _
    _ = ∑ i, |⟪B.frame i, y - B.center⟫_Real| := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [norm_smul, B.frame.norm_eq_one]
    _ ≤ ∑ i, (B.side i : Real) / 2 :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = ((∑ i, B.side i : NNReal) : Real) / 2 := by
      simp only [Finset.sum_div, NNReal.coe_sum]

/-- Orthogonal projection onto a unit tube axis cannot increase norm. -/
theorem norm_tubePointTransverse_le_norm_midpoint_sub
    {delta : NNReal} (x : Space) (T : Tube delta) :
    ‖tubePointTransverse x T‖ ≤ ‖tubeAxisMidpoint T - x‖ := by
  have hdecomp :
      tubeAxisMidpoint T - x =
        tubePointLongitudinal x T • T.axis.direction +
          tubePointTransverse x T := by
    rw [tubeAxisMidpoint_eq_point_decomposition x T]
    abel
  have horth :
      ⟪tubePointLongitudinal x T • T.axis.direction,
        tubePointTransverse x T⟫_Real = 0 := by
    rw [real_inner_smul_left,
      direction_inner_tubePointTransverse_eq_zero x T, mul_zero]
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [← hdecomp] at hpyth
  nlinarith [sq_nonneg ‖tubePointLongitudinal x T • T.axis.direction‖,
    norm_nonneg (tubePointTransverse x T),
    norm_nonneg (tubeAxisMidpoint T - x)]

/-- Endpoint containment bounds a direction coordinate by the corresponding
full side length. -/
theorem abs_inner_direction_le_frameBox_side
    {delta : NNReal} (B : FrameBox) (T : Tube delta)
    (hTB : T.carrier ⊆ B.carrier) (i : Fin 3) :
    |⟪B.frame i, T.axis.direction⟫_Real| ≤ (B.side i : Real) := by
  have hbase :
      T.axis.base ∈ B.carrier :=
    hTB (T.axis_subset_carrier T.axis.base_mem_carrier)
  have hend :
      T.axis.endpoint ∈ B.carrier :=
    hTB (T.axis_subset_carrier T.axis.endpoint_mem_carrier)
  have hb := B.centeredCoordinate_abs_le_halfSide hbase i
  have he := B.centeredCoordinate_abs_le_halfSide hend i
  have htriangle :
      |⟪B.frame i, T.axis.endpoint⟫_Real -
          ⟪B.frame i, T.axis.base⟫_Real| ≤
        |⟪B.frame i, T.axis.endpoint⟫_Real -
            ⟪B.frame i, B.center⟫_Real| +
          |⟪B.frame i, T.axis.base⟫_Real -
            ⟪B.frame i, B.center⟫_Real| := by
    calc
      |⟪B.frame i, T.axis.endpoint⟫_Real -
          ⟪B.frame i, T.axis.base⟫_Real| ≤
        |⟪B.frame i, T.axis.endpoint⟫_Real -
            ⟪B.frame i, B.center⟫_Real| +
          |⟪B.frame i, B.center⟫_Real -
            ⟪B.frame i, T.axis.base⟫_Real| := abs_sub_le _ _ _
      _ = |⟪B.frame i, T.axis.endpoint⟫_Real -
            ⟪B.frame i, B.center⟫_Real| +
          |⟪B.frame i, T.axis.base⟫_Real -
            ⟪B.frame i, B.center⟫_Real| := by
        rw [abs_sub_comm
          (⟪B.frame i, B.center⟫_Real)
          (⟪B.frame i, T.axis.base⟫_Real)]
  calc
    |⟪B.frame i, T.axis.direction⟫_Real| =
        |⟪B.frame i, T.axis.endpoint⟫_Real -
          ⟪B.frame i, T.axis.base⟫_Real| := by
      simp only [UnitSegment.endpoint, inner_add_right]
      ring_nf
    _ ≤ |⟪B.frame i, T.axis.endpoint⟫_Real -
            ⟪B.frame i, B.center⟫_Real| +
          |⟪B.frame i, T.axis.base⟫_Real -
            ⟪B.frame i, B.center⟫_Real| := htriangle
    _ ≤ (B.side i : Real) / 2 + (B.side i : Real) / 2 :=
      add_le_add he hb
    _ = (B.side i : Real) := by ring

/-- Midpoint and direction bounds yield the transverse-position coordinate
with no independent long-axis position hypothesis. -/
theorem abs_inner_tubePointTransverse_le_five_halves_side
    {delta : NNReal} (B : FrameBox) (T : Tube delta)
    (hTB : T.carrier ⊆ B.carrier)
    (hlong : |tubePointLongitudinal B.center T| ≤ 2)
    (i : Fin 3) :
    |⟪B.frame i, tubePointTransverse B.center T⟫_Real| ≤
      (5 : Real) / 2 * (B.side i : Real) := by
  have hmidTube : tubeAxisMidpoint T ∈ T.carrier := by
    apply T.axis_subset_carrier
    exact T.axis.mem_carrier_of_mem_Icc (by norm_num)
  have hmid := B.centeredCoordinate_abs_le_halfSide (hTB hmidTube) i
  have hdir := abs_inner_direction_le_frameBox_side B T hTB i
  rw [tubePointTransverse, inner_sub_right, real_inner_smul_right]
  calc
    |⟪B.frame i, tubeAxisMidpoint T - B.center⟫_Real -
        tubePointLongitudinal B.center T *
          ⟪B.frame i, T.axis.direction⟫_Real| ≤
      |⟪B.frame i, tubeAxisMidpoint T - B.center⟫_Real| +
        |tubePointLongitudinal B.center T *
          ⟪B.frame i, T.axis.direction⟫_Real| := abs_sub _ _
    _ ≤ (B.side i : Real) / 2 +
        2 * (B.side i : Real) := by
      gcongr
      · simpa [inner_sub_right] using hmid
      · rw [abs_mul]
        exact mul_le_mul hlong hdir (abs_nonneg _) (by norm_num)
    _ = (5 : Real) / 2 * (B.side i : Real) := by ring

/-- Literal FrameBox containment discharges every scalar input of the
five-parameter packing kernel.  The factor three in the wide code is a fixed
rounding margin for the five-halves projection bound. -/
theorem card_le_thinPlankFivePackingNatCap_of_frameBox
    {delta : NNReal} {parameter : Type} [Fintype parameter]
    [DecidableEq parameter]
    (B : FrameBox) (tube : parameter → Tube delta) (R : Real)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (_hR : 0 ≤ R)
    (hsum : (∑ i, B.side i : NNReal) ≤ 4)
    (hside0 : (B.side 0 : Real) ≤ (delta : Real))
    (hside1 : (B.side 1 : Real) ≤ R * (delta : Real))
    (hcontain : ∀ p, (tube p).carrier ⊆ B.carrier)
    (hforward : ∀ p,
      (1 : Real) / 2 ≤ ⟪B.frame 2, (tube p).axis.direction⟫_Real)
    (hpairwise : Set.Pairwise (Set.univ : Set parameter) fun p q =>
      EssentiallyDistinct (tube p) (tube q)) :
    Fintype.card parameter ≤ thinPlankFivePackingNatCap (3 * R) := by
  have hsumReal : ((∑ i, B.side i : NNReal) : Real) ≤ 4 := by
    exact_mod_cast hsum
  have hlong (p : parameter) :
      |tubePointLongitudinal B.center (tube p)| ≤ 2 := by
    have hmidTube : tubeAxisMidpoint (tube p) ∈ (tube p).carrier := by
      apply (tube p).axis_subset_carrier
      exact (tube p).axis.mem_carrier_of_mem_Icc (by norm_num)
    have hdist :=
      frameBox_dist_center_le_half_sum_side B ((hcontain p) hmidTube)
    have hnorm :
        ‖tubeAxisMidpoint (tube p) - B.center‖ ≤ 2 := by
      rw [dist_eq_norm] at hdist
      exact hdist.trans (by nlinarith)
    have hinner :=
      abs_real_inner_le_norm (tube p).axis.direction
        (tubeAxisMidpoint (tube p) - B.center)
    rw [(tube p).axis.norm_direction, one_mul] at hinner
    exact hinner.trans hnorm
  have htransverse (p : parameter) :
      ‖tubePointTransverse B.center (tube p)‖ ≤ 2 := by
    have hmidTube : tubeAxisMidpoint (tube p) ∈ (tube p).carrier := by
      apply (tube p).axis_subset_carrier
      exact (tube p).axis.mem_carrier_of_mem_Icc (by norm_num)
    have hdist :=
      frameBox_dist_center_le_half_sum_side B ((hcontain p) hmidTube)
    have hnorm :
        ‖tubeAxisMidpoint (tube p) - B.center‖ ≤ 2 := by
      rw [dist_eq_norm] at hdist
      exact hdist.trans (by nlinarith)
    exact
      (norm_tubePointTransverse_le_norm_midpoint_sub B.center (tube p)).trans
        hnorm
  have hfixed (p : parameter) (j : Fin 3) :
      |thinPlankFiveFixedCoordinates B.frame B.center (tube p) j| ≤
        thinPlankPackingFixedBound := by
    have hdir0 :=
      abs_inner_direction_le_frameBox_side B (tube p) (hcontain p) 0
    have htrans0 :=
      abs_inner_tubePointTransverse_le_five_halves_side
        B (tube p) (hcontain p) (hlong p) 0
    have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
    fin_cases j
    · change |tubePointLongitudinal B.center (tube p)| ≤
          thinPlankPackingFixedBound
      simpa [thinPlankPackingFixedBound] using
        (hlong p).trans (by norm_num)
    · change
        |⟪B.frame 0, tubePointTransverse B.center (tube p)⟫_Real /
          (delta : Real)| ≤ thinPlankPackingFixedBound
      rw [abs_div]
      have hnum :
          |⟪B.frame 0, tubePointTransverse B.center (tube p)⟫_Real| ≤
            (5 : Real) / 2 * (delta : Real) := by
        exact htrans0.trans
          (mul_le_mul_of_nonneg_left hside0 (by norm_num))
      rw [abs_of_pos hdeltaReal]
      unfold thinPlankPackingFixedBound
      apply (div_le_iff₀ hdeltaReal).2
      nlinarith
    · change
        |⟪B.frame 0, (tube p).axis.direction⟫_Real /
          (delta : Real)| ≤ thinPlankPackingFixedBound
      rw [abs_div]
      have hnum :
          |⟪B.frame 0, (tube p).axis.direction⟫_Real| ≤
            (delta : Real) := hdir0.trans hside0
      rw [abs_of_pos hdeltaReal]
      unfold thinPlankPackingFixedBound
      apply (div_le_iff₀ hdeltaReal).2
      nlinarith
  have hwide (p : parameter) (j : Fin 2) :
      |thinPlankFiveWideCoordinates B.frame B.center (tube p) j| ≤
        3 * R := by
    have hdir1 :=
      abs_inner_direction_le_frameBox_side B (tube p) (hcontain p) 1
    have htrans1 :=
      abs_inner_tubePointTransverse_le_five_halves_side
        B (tube p) (hcontain p) (hlong p) 1
    have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
    fin_cases j
    · change
        |⟪B.frame 1, tubePointTransverse B.center (tube p)⟫_Real /
          (delta : Real)| ≤ 3 * R
      rw [abs_div]
      have hnum :
          |⟪B.frame 1, tubePointTransverse B.center (tube p)⟫_Real| ≤
            (5 : Real) / 2 * (R * (delta : Real)) := by
        exact htrans1.trans
          (mul_le_mul_of_nonneg_left hside1 (by norm_num))
      rw [abs_of_pos hdeltaReal]
      apply (div_le_iff₀ hdeltaReal).2
      nlinarith
    · change
        |⟪B.frame 1, (tube p).axis.direction⟫_Real /
          (delta : Real)| ≤ 3 * R
      rw [abs_div]
      have hnum :
          |⟪B.frame 1, (tube p).axis.direction⟫_Real| ≤
            R * (delta : Real) := hdir1.trans hside1
      rw [abs_of_pos hdeltaReal]
      apply (div_le_iff₀ hdeltaReal).2
      nlinarith
  exact card_le_thinPlankFivePackingNatCap B.frame B.center tube (3 * R)
    hdeltaPos hdeltaSmall hlong hforward htransverse hfixed hwide hpairwise

#print axioms frameBox_dist_center_le_half_sum_side
#print axioms norm_tubePointTransverse_le_norm_midpoint_sub
#print axioms abs_inner_direction_le_frameBox_side
#print axioms abs_inner_tubePointTransverse_le_five_halves_side
#print axioms card_le_thinPlankFivePackingNatCap_of_frameBox

end
end Family8ThinPlankFiveParameterFrameBoxPackingV4
