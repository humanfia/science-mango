import Family8Grounding.Family8ParentwiseBadParentFactorReplacementV1
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Family8Grounding.Family8StickyUniformCountLossV2
import Mathlib.Tactic

/-!
# Honest product data for one parentwise bad-factor replacement

For a general `StickyScaleCover`, the active fine cardinality is the sum of
the fibre cardinalities.  It is not the product of the active-parent count
and the cardinality of one prescribed fibre.  Under the literal
`C`-uniformity field from Definition 2.12, the latter product is comparable
to the source count in both directions.

This file combines that comparison with the genuine fresh retention loss of
`Family8ParentwiseBadParentFactorReplacementV1`.  It also records the actual
scale of the eighth-normalized contracted-John child.  The scale product is
`(3 / 64) * delta`, not `delta`; no exact-cardinality uniformity and no
`branchingLoss = 1` hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentFactorProductV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8ParentwiseBadParentFactorReplacementV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyUniformCountLossV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The exact radius of the actual fresh child datum.  The fresh restriction
does not change the radius of the eighth-normalized contracted-John proxy. -/
def badParentFreshChildRadius (delta rho : NNReal) : NNReal :=
  contractedJohnProxyRadius delta rho / 8

/-- The literal loss used to retain the prescribed bad fibre after the
normalized fresh selection. -/
def badParentFreshRetentionLoss
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower : ENNReal) : ENNReal :=
  stickyFiberContractedJohnSourceClosedLoss
    (selectedFiberLowCFCardEnvelope S q selected lower
      (selectedParentLowCFFreshLoss S hrho hrhoOne q lower))

/-- The reverse of the existing selected-fibre count comparison.  It is a
direct consequence of the exact partition sum and the symmetric quantified
`C`-uniformity predicate. -/
theorem activeFine_card_le_uniformity_mul_activeCoarse_card_mul_fiber_card
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (huniform : IsCUniform S C)
    (q : {q // q ∈ S.activeCoarse}) :
    (S.activeFine.card : ENNReal) <=
      C *
        ((S.activeCoarse.card * (S.fiber q.1).card : Nat) : ENNReal) := by
  have hpartitionNat := activeFine_card_eq_sum_fiber_card S
  have hpartitionENN :
      (S.activeFine.card : ENNReal) =
        ∑ k ∈ S.activeCoarse, ((S.fiber k).card : ENNReal) := by
    exact_mod_cast hpartitionNat
  rw [hpartitionENN]
  calc
    (∑ k ∈ S.activeCoarse, ((S.fiber k).card : ENNReal)) <=
        ∑ _k ∈ S.activeCoarse,
          C * ((S.fiber q.1).card : ENNReal) := by
      exact Finset.sum_le_sum fun k hk =>
        huniform k hk q.1 q.2
    _ = (S.activeCoarse.card : ENNReal) *
        (C * ((S.fiber q.1).card : ENNReal)) := by simp
    _ = C *
        ((S.activeCoarse.card * (S.fiber q.1).card : Nat) : ENNReal) := by
      rw [Nat.cast_mul]
      ac_rfl

/-- The actual child radius is the official relative scale times the fixed
coefficient forced by the contracted-John proxy and eighth normalization. -/
theorem badParentFreshChildRadius_eq_fixed_mul_ratio
    (hrho : 0 < rho) :
    badParentFreshChildRadius delta rho =
      (3 / 64 : NNReal) * (delta / rho) := by
  exact contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrho

/-- Exact scale product for the actual coarse datum and actual fresh child.
The fixed coefficient is exposed rather than absorbed silently. -/
theorem rho_mul_badParentFreshChildRadius_eq
    (hrho : 0 < rho) :
    rho * badParentFreshChildRadius delta rho =
      (3 / 64 : NNReal) * delta := by
  rw [badParentFreshChildRadius_eq_fixed_mul_ratio hrho]
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  have hrhoReal : (rho : Real) ≠ 0 := by
    exact_mod_cast hrho.ne'
  field_simp [hrhoReal]

/-- Honest product certificate for the two actual datum index types.

`coarse_mul_child_le` and `source_le_loss_mul_coarse_mul_child` are the two
directions of the paper's approximate count product.  The exact statement
available without uniformity is retained separately as `exact_partition_sum`.
-/
structure BadParentFreshFactorProductCertificate
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower C : ENNReal) : Prop where
  coarse_index_card :
    Fintype.card {k // k ∈ S.activeCoarse} = S.activeCoarse.card
  child_index_card :
    Fintype.card {i // i ∈ selected} = selected.card
  exact_partition_sum :
    S.activeFine.card =
      ∑ k ∈ S.activeCoarse, (S.fiber k).card
  fibre_card_retention :
    (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) <=
      badParentFreshRetentionLoss S hrho hrhoOne q selected lower *
        (selected.card : ENNReal)
  coarse_mul_child_le :
    ((S.activeCoarse.card * selected.card : Nat) : ENNReal) <=
      C * (S.activeFine.card : ENNReal)
  source_le_loss_mul_coarse_mul_child :
    (S.activeFine.card : ENNReal) <=
      (C * badParentFreshRetentionLoss
          S hrho hrhoOne q selected lower) *
        ((S.activeCoarse.card * selected.card : Nat) : ENNReal)
  child_radius_eq :
    badParentFreshChildRadius delta rho =
      (3 / 64 : NNReal) * (delta / rho)
  scale_product_eq :
    rho * badParentFreshChildRadius delta rho =
      (3 / 64 : NNReal) * delta

/-- Build the product certificate from literal `C`-uniformity and the
literal fresh-fibre cardinality retention. -/
theorem badParentFreshFactorProductCertificate_of_uniformity
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower C : ENNReal) (huniform : IsCUniform S C)
    (hretained :
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) <=
        badParentFreshRetentionLoss S hrho hrhoOne q selected lower *
          (selected.card : ENNReal)) :
    BadParentFreshFactorProductCertificate
      S hrho hrhoOne q selected lower C := by
  let L := badParentFreshRetentionLoss S hrho hrhoOne q selected lower
  have hselectedNat : selected.card <= (S.fiber q.1).card := by
    calc
      selected.card <= Fintype.card {i // i ∈ S.fiber q.1} :=
        Finset.card_le_univ selected
      _ = (S.fiber q.1).card := Fintype.card_coe _
  have hselectedProductNat :
      S.activeCoarse.card * selected.card <=
        S.activeCoarse.card * (S.fiber q.1).card :=
    Nat.mul_le_mul_left S.activeCoarse.card hselectedNat
  have hselectedProduct :
      ((S.activeCoarse.card * selected.card : Nat) : ENNReal) <=
        ((S.activeCoarse.card * (S.fiber q.1).card : Nat) : ENNReal) := by
    exact_mod_cast hselectedProductNat
  have hcoarseChild :
      ((S.activeCoarse.card * selected.card : Nat) : ENNReal) <=
        C * (S.activeFine.card : ENNReal) :=
    hselectedProduct.trans
      (activeCoarse_card_mul_fiber_card_le_uniformity_mul_activeFine_card
        S huniform q.1 q.2)
  have hsourceFiber :
      (S.activeFine.card : ENNReal) <=
        C *
          ((S.activeCoarse.card * (S.fiber q.1).card : Nat) : ENNReal) :=
    activeFine_card_le_uniformity_mul_activeCoarse_card_mul_fiber_card
      S huniform q
  have hfiberRetained :
      ((S.fiber q.1).card : ENNReal) <=
        L * (selected.card : ENNReal) := by
    simpa only [L, Fintype.card_coe] using hretained
  have hsourceChild :
      (S.activeFine.card : ENNReal) <=
        (C * L) *
          ((S.activeCoarse.card * selected.card : Nat) : ENNReal) := by
    calc
      (S.activeFine.card : ENNReal) <=
          C *
            ((S.activeCoarse.card * (S.fiber q.1).card : Nat) : ENNReal) :=
        hsourceFiber
      _ = C * (S.activeCoarse.card : ENNReal) *
          ((S.fiber q.1).card : ENNReal) := by
        rw [Nat.cast_mul]
        ac_rfl
      _ <= C * (S.activeCoarse.card : ENNReal) *
          (L * (selected.card : ENNReal)) :=
        by
          simpa [mul_comm] using
            (mul_le_mul_left hfiberRetained
              (C * (S.activeCoarse.card : ENNReal)))
      _ = (C * L) *
          ((S.activeCoarse.card * selected.card : Nat) : ENNReal) := by
        rw [Nat.cast_mul]
        ac_rfl
  refine
    { coarse_index_card := Fintype.card_coe _
      child_index_card := Fintype.card_coe _
      exact_partition_sum := activeFine_card_eq_sum_fiber_card S
      fibre_card_retention := hretained
      coarse_mul_child_le := hcoarseChild
      source_le_loss_mul_coarse_mul_child := ?_
      child_radius_eq := badParentFreshChildRadius_eq_fixed_mul_ratio hrho
      scale_product_eq := rho_mul_badParentFreshChildRadius_eq hrho }
  simpa only [L] using hsourceChild

/-- Callback-free producer combining the existing literal bad-parent fresh
replacement with honest two-sided count and scale product data. -/
theorem exists_badParent_freshFactorReplacement_with_product
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower C : ENNReal} (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt S q < lower)
    (huniform : IsCUniform S C) :
    exists selected : Finset {i // i ∈ S.fiber q.1},
      selected.Nonempty /\
      (badParentFreshSuccessorDatum
        S Y hrho hrhoOne q selected).IsAdmissible /\
      selectedParentLowCFFreshLoss S hrho hrhoOne q lower ≠ ∞ /\
      IsFrostmanIn
        (lower *
          (16 * selectedParentLowCFFreshLoss S hrho hrhoOne q lower))
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q) /\
      (badParentRescaledFibreDatum
        S Y hrho hrhoOne q).shading.shadingMass <=
        badParentFreshRetentionLoss S hrho hrhoOne q selected lower *
          (badParentFreshSuccessorDatum
            S Y hrho hrhoOne q selected).shading.shadingMass /\
      BadParentFreshFactorProductCertificate
        S hrho hrhoOne q selected lower C := by
  obtain ⟨selected, hselected, hadmissible, hfreshTop,
      hFrostman, hcard, hmass⟩ :=
    exists_badParent_freshFactorReplacement
      S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho q
        hlowerTop hbad
  refine ⟨selected, hselected, hadmissible, hfreshTop,
    hFrostman, ?_, ?_⟩
  · simpa only [badParentFreshRetentionLoss] using hmass
  · apply badParentFreshFactorProductCertificate_of_uniformity
      S hrho hrhoOne q selected lower C huniform
    simpa only [badParentFreshRetentionLoss] using hcard

#print axioms
  activeFine_card_le_uniformity_mul_activeCoarse_card_mul_fiber_card
#print axioms badParentFreshChildRadius_eq_fixed_mul_ratio
#print axioms rho_mul_badParentFreshChildRadius_eq
#print axioms badParentFreshFactorProductCertificate_of_uniformity
#print axioms exists_badParent_freshFactorReplacement_with_product

end
end Family8ParentwiseBadParentFactorProductV1
