import Family8Grounding.Family8PaperConflictDirectionCoherenceV1
import Family8Grounding.Family8PaperConflictProjectionStabilityV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8PaperConflictAnisotropicBoundsV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8CommonPointTubePackingV1
open Family8PaperConflictDirectionCoherenceV1
open Family8PaperConflictProjectionStabilityV2
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

def PaperConflict {delta : NNReal} (T U : Tube delta) : Prop :=
  T.carrier ⊆ twoFoldTubeCarrier U ∨
    U.carrier ⊆ twoFoldTubeCarrier T

theorem paperConflict_symm {delta : NNReal} :
    Std.Symm (@PaperConflict delta) := by
  constructor
  intro T U h
  exact h.elim Or.inr Or.inl

theorem dist_midpoint_le_half_add_radius
    {delta : NNReal} (T : Tube delta) {x : Space} (hx : x ∈ T.carrier) :
    dist x (tubeAxisMidpoint T) ≤ (2 : Real)⁻¹ + (delta : Real) := by
  obtain ⟨t, ht, hxt⟩ := exists_axis_parameter_dist_le_of_mem T hx
  let q : Space := T.axis.base + t • T.axis.direction
  have hqmid : dist q (tubeAxisMidpoint T) ≤ (2 : Real)⁻¹ := by
    rw [dist_eq_norm]
    have hvec : q - tubeAxisMidpoint T =
        (t - (2 : Real)⁻¹) • T.axis.direction := by
      simp only [q, tubeAxisMidpoint]
      module
    rw [hvec, norm_smul, T.axis.norm_direction, mul_one,
      Real.norm_eq_abs, abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  calc
    dist x (tubeAxisMidpoint T) ≤ dist x q + dist q (tubeAxisMidpoint T) :=
      dist_triangle _ _ _
    _ ≤ (delta : Real) + (2 : Real)⁻¹ := add_le_add hxt hqmid
    _ = (2 : Real)⁻¹ + (delta : Real) := add_comm _ _

theorem dist_point_midpoint_le_two_of_mem_twoFold
    {delta : NNReal} (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (T : Tube delta) {x : Space} (hx : x ∈ twoFoldTubeCarrier T) :
    dist x (tubeAxisMidpoint T) ≤ 2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hcenter : tubeCenter T = tubeAxisMidpoint T := rfl
  have hycenter := dist_midpoint_le_half_add_radius T hy
  rw [← hcenter] at hycenter ⊢
  rw [dist_eq_norm]
  have hvec :
      (tubeCenter T + (2 : Real) • (y - tubeCenter T)) - tubeCenter T =
        (2 : Real) • (y - tubeCenter T) := by module
  calc
    ‖(tubeCenter T + (2 : Real) • (y - tubeCenter T)) - tubeCenter T‖ =
        ‖(2 : Real) • (y - tubeCenter T)‖ := congrArg norm hvec
    _ = 2 * ‖y - tubeCenter T‖ := by
      rw [norm_smul, Real.norm_ofNat]
    _ = 2 * dist y (tubeCenter T) := by rfl
    _ ≤ 2 * ((2 : Real)⁻¹ + (delta : Real)) := by gcongr
    _ ≤ 2 := by
      have hdeltaReal : (delta : Real) ≤ (1 : Real) / 100 := by
        exact_mod_cast hdeltaSmall
      nlinarith

theorem dist_midpoint_le_two_of_paperConflict
    {delta : NNReal} (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    {T U : Tube delta} (hconflict : PaperConflict T U) :
    dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) ≤ 2 := by
  rcases hconflict with hTU | hUT
  · have hmidT : tubeAxisMidpoint T ∈ T.carrier := by
      change tubeCenter T ∈ T.carrier
      exact tubeCenter_mem_carrier T
    exact dist_point_midpoint_le_two_of_mem_twoFold hdeltaSmall U (hTU hmidT)
  · have hmidU : tubeAxisMidpoint U ∈ U.carrier := by
      change tubeCenter U ∈ U.carrier
      exact tubeCenter_mem_carrier U
    simpa only [dist_comm] using
      dist_point_midpoint_le_two_of_mem_twoFold hdeltaSmall T (hUT hmidU)

theorem transverseResidual_neg_argument (u d : Space) :
    transverseResidual u (-d) = -transverseResidual u d := by
  simp only [transverseResidual, inner_neg_right, neg_smul]
  module

theorem norm_transverseResidual_midpoint_le_four_mul_of_mem_twoFold
    {delta : NNReal} (T : Tube delta) {x : Space}
    (hx : x ∈ twoFoldTubeCarrier T) :
    ‖transverseResidual T.axis.direction (x - tubeAxisMidpoint T)‖ ≤
      4 * (delta : Real) := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hcenter : tubeCenter T = tubeAxisMidpoint T := rfl
  have htrans := norm_tubePointTransverse_le_two_mul T hy
  have hvec :
      (tubeCenter T + (2 : Real) • (y - tubeCenter T)) - tubeCenter T =
        (2 : Real) • (y - tubeCenter T) := by module
  have heq :
      transverseResidual T.axis.direction
          ((tubeCenter T + (2 : Real) • (y - tubeCenter T)) -
            tubeAxisMidpoint T) =
        (-2 : Real) • tubePointTransverse y T := by
    simp only [transverseResidual, tubePointTransverse, tubePointLongitudinal]
    rw [← hcenter, hvec, inner_smul_right]
    have hsub : tubeCenter T - y = -(y - tubeCenter T) := by module
    rw [hsub, inner_neg_right]
    module
  rw [heq]
  calc
    ‖(-2 : Real) • tubePointTransverse y T‖ =
        2 * ‖tubePointTransverse y T‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ 2 * (2 * (delta : Real)) := by gcongr
    _ = 4 * (delta : Real) := by ring

theorem norm_tubePointTransverse_anchor_le_thirtySix_mul
    {delta : NNReal} (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    {T U : Tube delta} (hconflict : PaperConflict T U) :
    ‖tubePointTransverse (tubeAxisMidpoint T) U‖ ≤
      36 * (delta : Real) := by
  let d : Space := tubeAxisMidpoint U - tubeAxisMidpoint T
  have hd : ‖d‖ ≤ 2 := by
    simpa only [d, dist_eq_norm, norm_sub_rev] using
      dist_midpoint_le_two_of_paperConflict hdeltaSmall hconflict
  have hdirection :=
    unorientedDirectionClose_eight_mul_of_paperConflict hconflict
  rw [tubePointTransverse_eq_transverseResidual]
  change ‖transverseResidual U.axis.direction d‖ ≤ _
  rcases hconflict with hTU | hUT
  · have hmidT : tubeAxisMidpoint T ∈ T.carrier := by
      change tubeCenter T ∈ T.carrier
      exact tubeCenter_mem_carrier T
    have hdirect :
        ‖transverseResidual U.axis.direction
            (tubeAxisMidpoint T - tubeAxisMidpoint U)‖ ≤
          4 * (delta : Real) :=
      norm_transverseResidual_midpoint_le_four_mul_of_mem_twoFold U
        (hTU hmidT)
    have hdneg :
        d = -(tubeAxisMidpoint T - tubeAxisMidpoint U) := by
      dsimp only [d]
      module
    rw [hdneg, transverseResidual_neg_argument, norm_neg]
    exact hdirect.trans (by gcongr; norm_num)
  · have hmidU : tubeAxisMidpoint U ∈ U.carrier := by
      change tubeCenter U ∈ U.carrier
      exact tubeCenter_mem_carrier U
    have hanchor :
        ‖transverseResidual T.axis.direction d‖ ≤
          4 * (delta : Real) :=
      norm_transverseResidual_midpoint_le_four_mul_of_mem_twoFold T
        (hUT hmidU)
    have hprojection :
        ‖transverseResidual U.axis.direction d -
            transverseResidual T.axis.direction d‖ ≤
          32 * (delta : Real) := by
      rcases hdirection with hforward | hreverse
      · calc
          ‖transverseResidual U.axis.direction d -
              transverseResidual T.axis.direction d‖ ≤
              2 * ‖d‖ * ‖U.axis.direction - T.axis.direction‖ :=
            norm_transverseResidual_sub_le
              U.axis.norm_direction T.axis.norm_direction
          _ ≤ 2 * 2 * (8 * (delta : Real)) := by
            gcongr
            simpa only [norm_sub_rev] using hforward
          _ = 32 * (delta : Real) := by ring
      · calc
          ‖transverseResidual U.axis.direction d -
              transverseResidual T.axis.direction d‖ ≤
              2 * ‖d‖ * ‖U.axis.direction + T.axis.direction‖ :=
            norm_transverseResidual_sub_le_of_neg
              U.axis.norm_direction T.axis.norm_direction
          _ ≤ 2 * 2 * (8 * (delta : Real)) := by
            gcongr
            simpa only [add_comm] using hreverse
          _ = 32 * (delta : Real) := by ring
    calc
      ‖transverseResidual U.axis.direction d‖ ≤
          ‖transverseResidual U.axis.direction d -
              transverseResidual T.axis.direction d‖ +
            ‖transverseResidual T.axis.direction d‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le
            (transverseResidual U.axis.direction d -
              transverseResidual T.axis.direction d)
            (transverseResidual T.axis.direction d)
      _ ≤ 32 * (delta : Real) + 4 * (delta : Real) :=
        add_le_add hprojection hanchor
      _ = 36 * (delta : Real) := by ring

theorem abs_tubePointLongitudinal_anchor_le_two
    {delta : NNReal} (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    {T U : Tube delta} (hconflict : PaperConflict T U) :
    |tubePointLongitudinal (tubeAxisMidpoint T) U| ≤ 2 := by
  have hd := dist_midpoint_le_two_of_paperConflict hdeltaSmall hconflict
  have hinner := abs_real_inner_le_norm U.axis.direction
    (tubeAxisMidpoint U - tubeAxisMidpoint T)
  rw [U.axis.norm_direction, one_mul] at hinner
  exact hinner.trans (by simpa only [dist_eq_norm, norm_sub_rev] using hd)

#print axioms dist_midpoint_le_two_of_paperConflict
#print axioms transverseResidual_neg_argument
#print axioms norm_transverseResidual_midpoint_le_four_mul_of_mem_twoFold
#print axioms norm_tubePointTransverse_anchor_le_thirtySix_mul
#print axioms abs_tubePointLongitudinal_anchor_le_two

end

end Family8PaperConflictAnisotropicBoundsV4
