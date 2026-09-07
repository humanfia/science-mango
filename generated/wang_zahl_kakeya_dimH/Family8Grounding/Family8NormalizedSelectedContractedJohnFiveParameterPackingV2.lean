import Family8Grounding.Family8StickyFiberContractedJohnNormalizedFreshClosedLossV1
import Family8Grounding.Family8ContractedJohnProxyFiveParameterPackingV2
import Family8Grounding.Family8ThinPlankFiveParameterMidpointDirectionPackingV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8NormalizedSelectedContractedJohnFiveParameterPackingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnProxyFiveParameterPackingV2
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8ThinPlankEssentialDistinctPackingV4
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterMidpointDirectionPackingV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Five-parameter cap on the actual normalized fresh selection

This successor fixes only binder inference and scalar normalization in the
failed V1 draft.  The selected datum is exactly the datum whose admissibility
is supplied by the fresh closed-loss producer.
-/

theorem tubeAxisMidpoint_eighthNormalizedTube
    {r : NNReal} (T : Tube r) :
    Family8CommonPointTubePackingV1.tubeAxisMidpoint
        (eighthNormalizedTube T) =
      eighthDilationPoint
        (Family8CommonPointTubePackingV1.tubeAxisMidpoint T) := by
  unfold Family8CommonPointTubePackingV1.tubeAxisMidpoint
    eighthNormalizedTube eighthNormalizedAxis eighthDilationPoint
    Family8FiniteRandomRigidMotionB2NormalizationCoreV1.tubeAxisMidpoint
  simp only
  module

theorem eighthNormalizedTube_direction
    {r : NNReal} (T : Tube r) :
    (eighthNormalizedTube T).axis.direction = T.axis.direction :=
  rfl

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A fresh selected subtype of the canonical normalized proxy family has the
five-parameter cap from raw affine-center/vector coordinate bounds. -/
theorem normalizedSelectedProxy_card_le_fiveParameterCap
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber k.1})
    (hselectedAdmissible :
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k))
        selected).IsAdmissible)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (R : Real) (hR : 0 ≤ R)
    (ell : {i // i ∈ S.fiber k.1} → Real)
    (hellNorm : ∀ i,
      ell i ≤ ‖affineImageAxisVector
        (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
        (fine.tubes i.1)‖)
    (hcenter0 : ∀ i : {i // i ∈ S.fiber k.1},
      |⟪frame 0,
        affineImageAxisCenter
          (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
          (fine.tubes i.1)⟫_Real| ≤
        (contractedJohnProxyRadius delta rho : Real) / 2)
    (hcenter1 : ∀ i : {i // i ∈ S.fiber k.1},
      |⟪frame 1,
        affineImageAxisCenter
          (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
          (fine.tubes i.1)⟫_Real| ≤
        (R * (contractedJohnProxyRadius delta rho : Real)) / 2)
    (hvector0 : ∀ i,
      |⟪frame 0,
        affineImageAxisVector
          (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
          (fine.tubes i.1)⟫_Real| ≤
        ell i * ((contractedJohnProxyRadius delta rho : Real) / 8))
    (hvector1 : ∀ i,
      |⟪frame 1,
        affineImageAxisVector
          (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
          (fine.tubes i.1)⟫_Real| ≤
        ell i * (R * ((contractedJohnProxyRadius delta rho : Real) / 8)))
    (hnormalizedSmall :
      contractedJohnProxyRadius delta rho / 8 ≤ (1 / 100 : NNReal))
    (hthin :
      ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real) ^ 2 +
        (R * ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real)) ^ 2 ≤
          (3 : Real) / 4) :
    selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
  let selectedD := restrictActualTubeDatum (eighthNormalizedDatum D) selected
  let tube : {i // i ∈ selected} →
      Tube (contractedJohnProxyRadius delta rho / 8) :=
    fun i => selectedD.family.tubes i
  have hscalePos : 0 < contractedJohnProxyRadius delta rho / 8 := by
    exact div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hmidNorm (i : {i // i ∈ selected}) :
      ‖Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) -
        (0 : Space)‖ ≤ 2 := by
    have hmidCarrier :
        Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) ∈
          (tube i).carrier := by
      apply (tube i).axis_subset_carrier
      unfold Family8CommonPointTubePackingV1.tubeAxisMidpoint
      exact (tube i).axis.mem_carrier_of_mem_Icc (by norm_num)
    have hball := hselectedAdmissible.contained_in_unit_ball i hmidCarrier
    rw [Metric.mem_closedBall, dist_zero_right] at hball
    simpa only [sub_zero] using hball.trans (by norm_num)
  have htubeEq (i : {i // i ∈ selected}) :
      tube i = eighthNormalizedTube
        (contractedJohnProxyTube (S.coarse.tubes k.1) hrho
          (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
            S hrho hrhoOne k)
          (fine.tubes i.1.1)) := by
    rfl
  have hmid0 (i : {i // i ∈ selected}) :
      |⟪frame 0,
        Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) -
          (0 : Space)⟫_Real| ≤
        ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real) / 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube, sub_zero]
    rw [tubeAxisMidpoint_contractedJohnProxyTube]
    simp only [eighthDilationPoint, real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    calc
      (1 / 8 : Real) *
          |⟪frame 0,
            affineImageAxisCenter
              (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
              (fine.tubes i.1.1)⟫_Real| ≤
          (1 / 8 : Real) *
            ((contractedJohnProxyRadius delta rho : Real) / 2) :=
        mul_le_mul_of_nonneg_left (hcenter0 i.1) (by norm_num)
      _ = ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real) / 2 := by
        push_cast
        ring
  have hmid1 (i : {i // i ∈ selected}) :
      |⟪frame 1,
        Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) -
          (0 : Space)⟫_Real| ≤
        (R * ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real)) / 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube, sub_zero]
    rw [tubeAxisMidpoint_contractedJohnProxyTube]
    simp only [eighthDilationPoint, real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    calc
      (1 / 8 : Real) *
          |⟪frame 1,
            affineImageAxisCenter
              (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
              (fine.tubes i.1.1)⟫_Real| ≤
          (1 / 8 : Real) *
            ((R * (contractedJohnProxyRadius delta rho : Real)) / 2) :=
        mul_le_mul_of_nonneg_left (hcenter1 i.1) (by norm_num)
      _ = (R * ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real)) / 2 := by
        push_cast
        ring
  have hdir0 (i : {i // i ∈ selected}) :
      |⟪frame 0, (tube i).axis.direction⟫_Real| ≤
        ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real) := by
    rw [htubeEq i, eighthNormalizedTube_direction]
    change |⟪frame 0,
      affineImageAxisDirection
        (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
        (fine.tubes i.1.1)⟫_Real| ≤ _
    apply abs_inner_affineImageAxisDirection_le_of_lower_length
      _ _ _ (ell i.1)
        ((contractedJohnProxyRadius delta rho : Real) / 8)
        (hellNorm i.1) (by positivity) (hvector0 i.1)
  have hdir1 (i : {i // i ∈ selected}) :
      |⟪frame 1, (tube i).axis.direction⟫_Real| ≤
        R * ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real) := by
    rw [htubeEq i, eighthNormalizedTube_direction]
    change |⟪frame 1,
      affineImageAxisDirection
        (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
        (fine.tubes i.1.1)⟫_Real| ≤ _
    apply abs_inner_affineImageAxisDirection_le_of_lower_length
      _ _ _ (ell i.1)
        (R * ((contractedJohnProxyRadius delta rho : Real) / 8))
        (hellNorm i.1) (mul_nonneg hR (by positivity)) (hvector1 i.1)
  have hpairwise :
      Set.Pairwise (Set.univ : Set {i // i ∈ selected}) fun i j =>
        EssentiallyDistinct (tube i) (tube j) := by
    exact hselectedAdmissible.pairwise_essentiallyDistinct
  have hcap :=
    card_le_thinPlankFivePackingNatCap_of_midpoint_direction_bounds
      frame 0 tube R hscalePos hnormalizedSmall hR hmidNorm hmid0 hmid1
        hdir0 hdir1 hthin hpairwise
  simpa only [Fintype.card_coe] using hcap

#print axioms tubeAxisMidpoint_eighthNormalizedTube
#print axioms eighthNormalizedTube_direction
#print axioms normalizedSelectedProxy_card_le_fiveParameterCap

end
end Family8NormalizedSelectedContractedJohnFiveParameterPackingV2
