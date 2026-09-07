import Family8Grounding.Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5
import Family8Grounding.Family8DoubledParentConflictIncidenceDegreeV3
import Family8Grounding.Family8DoubledCarrierPaperElongatedBodyV1
import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8DoubledCarrierPaperElongatedBodyV1
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5

attribute [local instance]
  Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5.instFintypeScaleCoverActiveOwner
  Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5.instDecidableEqScaleCoverActiveOwner

noncomputable section

/-!
# A genuine Katz--Tao cap for doubled fibres of the active-owner cover

The full central dilation `2A` fits in the honest length-six elongated frame
body.  Source Katz--Tao mass control and the lower volume of every fine tube
therefore give an explicit `O(A * (rho / delta)^2)` cap for every doubled
fibre.  No total-coarse-card or exact-graph budget is used.
-/

/-- Restriction to the deduplicated active-owner subtype inherits the source
Katz--Tao estimate exactly. -/
theorem isKatzTao_activeOwnerFine
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index]
    (D : ActualTubeDatum delta index)
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) D.family.tubes weight)
    (S : StickyScaleCover D.family rho) {A : ENNReal}
    (hKT : IsKatzTao A D.family.bodyFamily) :
    IsKatzTao A (activeOwnerFine C S).bodyFamily := by
  intro K
  let selected : Finset index := C.sourceOwnerImage S.activeFine
  have hsub := hKT.on selected K
  have hmass := restrictActualTubeDatum_containedMass D selected K
  change containedMass
      (restrictActualTubeDatum D selected).family.bodyFamily K ≤
    A * volume (K : Set Space)
  rw [hmass]
  exact hsub

/-- Katz--Tao mass control on one literal doubled fibre.  The right-hand
side is the exact volume of the elongated parent test. -/
theorem doubledFiber_card_mul_halfSq_le_katzTao_elongated
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) (hrho : rho ≤ 1)
    {A : ENNReal} (hKT : IsKatzTao A fine.bodyFamily)
    (k : Fin S.coarseCard) :
    ((doubledFiber S k).card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) ≤
      A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2) := by
  classical
  obtain ⟨frame, hframe⟩ := (S.coarse.tubes k).exists_alignedFrame
  let K : ConvexBody Space :=
    paperElongatedBody (S.coarse.tubes k) frame
  have hcontained : doubledFiber S k ⊆
      containedIndices fine.bodyFamily K := by
    intro i hi
    rw [mem_containedIndices]
    exact ((mem_doubledFiber S i k).mp hi).2.trans
      (twoFoldTubeCarrier_subset_paperElongatedBody
        (S.coarse.tubes k) frame hframe hrho)
  have hlower :
      ((doubledFiber S k).card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) ≤
        containedMass fine.bodyFamily K := by
    calc
      ((doubledFiber S k).card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) =
          ∑ _i ∈ doubledFiber S k,
            ((delta : ENNReal) ^ 2 / 2) := by
              simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ doubledFiber S k,
          volume (fine.tubes i).carrier := by
        apply Finset.sum_le_sum
        intro i _hi
        exact (fine.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
      _ ≤ ∑ i ∈ containedIndices fine.bodyFamily K,
          volume (fine.tubes i).carrier := by
        exact Finset.sum_le_sum_of_subset hcontained
      _ = containedMass fine.bodyFamily K := by
        rfl
  calc
    ((doubledFiber S k).card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) ≤
        containedMass fine.bodyFamily K := hlower
    _ ≤ A * volume (K : Set Space) := hKT K
    _ = A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2) := by
      rw [volume_paperElongatedBody]

/-- Explicit natural ceiling of the preceding geometric incidence ratio. -/
def katzTaoDoubledFiberNatCap
    (delta rho : NNReal) (A : ENNReal) : Nat :=
  Nat.ceil
    ((A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2) /
      ((delta : ENNReal) ^ 2 / 2)).toReal)

/-- Natural-cardinality form consumed by the doubled-parent incidence
double-counting API. -/
theorem doubledFiber_card_le_katzTaoDoubledFiberNatCap
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : rho ≤ 1) {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A fine.bodyFamily)
    (k : Fin S.coarseCard) :
    (doubledFiber S k).card ≤
      katzTaoDoubledFiberNatCap delta rho A := by
  let floor : ENNReal := (delta : ENNReal) ^ 2 / 2
  let total : ENNReal :=
    A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2)
  have hfloor0 : floor ≠ 0 := by
    dsimp only [floor]
    exact ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdeltaPos.ne'), by norm_num⟩
  have hfloorTop : floor ≠ ∞ := by
    dsimp only [floor]
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  have htotalTop : total ≠ ∞ := by
    dsimp only [total]
    apply ENNReal.mul_ne_top hAfinite
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hquotientTop : total / floor ≠ ∞ :=
    ENNReal.div_ne_top htotalTop hfloor0
  have hcross := doubledFiber_card_mul_halfSq_le_katzTao_elongated
    S hdeltaHalf hrho hKT k
  have hquotient : ((doubledFiber S k).card : ENNReal) ≤
      total / floor := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hfloor0) (Or.inl hfloorTop)).2
    simpa only [total, floor] using hcross
  have hreal : ((doubledFiber S k).card : Real) ≤
      (total / floor).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top
      hquotientTop).2 hquotient
    simpa using h
  have hceil : ((doubledFiber S k).card : Real) ≤
      (Nat.ceil ((total / floor).toReal) : Real) :=
    hreal.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- Direct specialization to the canonical deduplicated active-owner cover.
Every produced parent has the genuine Katz--Tao doubled-fibre cap, with no
degree callback and no total-coarse-card bound. -/
theorem exists_activeOwner_stickyScaleCover_with_katzTao_doubledFiberCap
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index]
    (D : ActualTubeDatum delta index)
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) D.family.tubes weight)
    (S : StickyScaleCover D.family rho)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho)
    (hrhoOne : rho ≤ 1) (hfiveRhoOne : 5 * rho ≤ 1)
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A D.family.bodyFamily) :
    ∃ T : StickyScaleCover (activeOwnerFine C S) (5 * rho),
      T.coarseCard ≤ S.coarseCard *
          Family8PaperConflictOwnerParentFrameFiniteCodeV8.parentFrameCodeCount rho ∧
      ∀ k, k ∈ T.activeCoarse →
        (doubledFiber T k).card ≤
          katzTaoDoubledFiberNatCap delta (5 * rho) A := by
  obtain ⟨T, hT⟩ := exists_activeOwner_stickyScaleCover C S hdeltaSmall
    hdeltaRho hrhoPos hrhoOne
  refine ⟨T, hT, ?_⟩
  intro k _hk
  have hsmallToHalf : (1 / 100 : NNReal) ≤ (2 : NNReal)⁻¹ := by
    rw [← NNReal.coe_le_coe]
    norm_num [NNReal.coe_div, NNReal.coe_inv]
  apply doubledFiber_card_le_katzTaoDoubledFiberNatCap
    T hdeltaPos (hdeltaSmall.trans hsmallToHalf) hfiveRhoOne hAfinite
  exact isKatzTao_activeOwnerFine D C S hKT

#print axioms isKatzTao_activeOwnerFine
#print axioms doubledFiber_card_mul_halfSq_le_katzTao_elongated
#print axioms doubledFiber_card_le_katzTaoDoubledFiberNatCap
#print axioms exists_activeOwner_stickyScaleCover_with_katzTao_doubledFiberCap

end
end Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
