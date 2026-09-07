import Family8Grounding.Family8IncidentParentElongatedContainmentV3
import Family8Grounding.Family8DoubledParentsAssignedFineInjectionV3
import Family8Grounding.Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictIncidenceDegreeV3.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentsAssignedFineInjectionV3.ScaleCover
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8IncidentParentElongatedContainmentV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5
open FamilyStickyAtEveryScaleCoreV1

attribute [local instance]
  Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5.instFintypeScaleCoverActiveOwner
  Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5.instDecidableEqScaleCoverActiveOwner

noncomputable section

/-!
# Exact Katz--Tao incidence degree for the active-owner cover

For one fixed fine tube, choose one assigned fine tube from each active parent
whose doubled carrier contains it.  The parent map makes this choice
injective.  The incident-parent geometry places every chosen tube in one
honest elongated convex test of volume `240000 rho^2`, so source Katz--Tao
mass control gives the missing cross-parent incidence cap.  Combining it with
the doubled-fibre cap yields the exact `1 + N*M` conflict-degree estimate.
-/

/-- Explicit natural ceiling for the cross-parent incidence cap. -/
def katzTaoDoubledParentsNatCap
    (delta rho : NNReal) (A : ENNReal) : Nat :=
  Nat.ceil
    ((A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2) /
      ((delta : ENNReal) ^ 2 / 2)).toReal)

/-- Katz--Tao mass control on the genuine active-parent incidence set of one
fine tube. -/
theorem doubledParentsContainingFine_card_mul_halfSq_le_katzTao_elongated
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : rho ≤ (1 / 16 : NNReal))
    {A : ENNReal} (hKT : IsKatzTao A fine.bodyFamily)
    (i : index) :
    ((doubledParentsContainingFine S i).card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) ≤
      A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2) := by
  classical
  obtain ⟨frame, hframe⟩ := (fine.tubes i).exists_alignedFrame
  let K : ConvexBody Space :=
    paperElongatedBody ((fine.tubes i).changeRadius rho) frame
  have hassignedContained : ∀ k : IncidentParent S i,
      (fine.tubes (incidentAssignedFine S i k)).carrier ⊆
        (K : Set Space) := by
    intro k
    have hactive := incidentAssignedFine_mem_activeFine S i k
    have hsource := S.carrier_subset (incidentAssignedFine S i k) hactive
    rw [incidentAssignedFine_parent] at hsource
    have hkData :=
      (mem_doubledParentsContainingFine S i k.1).mp k.2
    exact hsource.trans
      (parent_carrier_subset_fine_paperElongatedBody
        (fine.tubes i) (S.coarse.tubes k.1) frame hframe hrho hkData.2)
  have hcardNat :=
    doubledParentsContainingFine_card_le_containedIndices
      S i K hassignedContained
  have hcardENN :
      ((doubledParentsContainingFine S i).card : ENNReal) ≤
        ((containedIndices fine.bodyFamily K).card : ENNReal) := by
    exact_mod_cast hcardNat
  have hlower :
      ((containedIndices fine.bodyFamily K).card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) ≤
        containedMass fine.bodyFamily K := by
    calc
      ((containedIndices fine.bodyFamily K).card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) =
          ∑ _j ∈ containedIndices fine.bodyFamily K,
            ((delta : ENNReal) ^ 2 / 2) := by
              simp [nsmul_eq_mul]
      _ ≤ ∑ j ∈ containedIndices fine.bodyFamily K,
          volume (fine.tubes j).carrier := by
        apply Finset.sum_le_sum
        intro j _hj
        exact (fine.tubes j).half_sq_le_volume_of_le_half hdeltaHalf
      _ = containedMass fine.bodyFamily K := by rfl
  calc
    ((doubledParentsContainingFine S i).card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) ≤
        ((containedIndices fine.bodyFamily K).card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) := by
      gcongr
    _ ≤ containedMass fine.bodyFamily K := hlower
    _ ≤ A * volume (K : Set Space) := hKT K
    _ = A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2) := by
      rw [volume_paperElongatedBody]

/-- Natural-cardinality version of the genuine cross-parent incidence cap. -/
theorem doubledParentsContainingFine_card_le_katzTaoDoubledParentsNatCap
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : rho ≤ (1 / 16 : NNReal))
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A fine.bodyFamily) (i : index) :
    (doubledParentsContainingFine S i).card ≤
      katzTaoDoubledParentsNatCap delta rho A := by
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
  have hcross :=
    doubledParentsContainingFine_card_mul_halfSq_le_katzTao_elongated
      S hdeltaHalf hrho hKT i
  have hquotient :
      ((doubledParentsContainingFine S i).card : ENNReal) ≤
        total / floor := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hfloor0) (Or.inl hfloorTop)).2
    simpa only [total, floor] using hcross
  have hreal : ((doubledParentsContainingFine S i).card : Real) ≤
      (total / floor).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top
      hquotientTop).2 hquotient
    simpa using h
  have hceil : ((doubledParentsContainingFine S i).card : Real) ≤
      (Nat.ceil ((total / floor).toReal) : Real) :=
    hreal.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- Both Katz--Tao incidence caps give a callback-free exact conflict degree
for any sticky cover in the normalized radius range. -/
theorem closedDoubledParentConflictDegreeBound_katzTao
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : rho ≤ (1 / 16 : NNReal))
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A fine.bodyFamily) :
    ClosedDoubledParentConflictDegreeBound S
      ((1 + katzTaoDoubledFiberNatCap delta rho A *
        katzTaoDoubledParentsNatCap delta rho A : Nat) : ENNReal) := by
  have hrhoOne : rho ≤ 1 := by
    exact hrho.trans (by
      rw [← NNReal.coe_le_coe]
      norm_num [NNReal.coe_div])
  apply closedDoubledParentConflictDegreeBound_of_incidence S
    (katzTaoDoubledFiberNatCap delta rho A)
    (katzTaoDoubledParentsNatCap delta rho A)
  · intro k _hk
    exact doubledFiber_card_le_katzTaoDoubledFiberNatCap
      S hdeltaPos hdeltaHalf hrhoOne hAfinite hKT k
  · intro i _hi
    exact doubledParentsContainingFine_card_le_katzTaoDoubledParentsNatCap
      S hdeltaPos hdeltaHalf hrho hAfinite hKT i

/-- Canonical specialization: the deduplicated active-owner cover now has an
explicit exact conflict degree from source Katz--Tao mass control, with no
degree callback and no total-coarse-card estimate used as degree. -/
theorem exists_activeOwner_stickyScaleCover_with_katzTao_exactConflictDegree
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index]
    (D : ActualTubeDatum delta index)
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) D.family.tubes weight)
    (S : StickyScaleCover D.family rho)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho)
    (hrhoOne : rho ≤ 1) (hfiveRho : 5 * rho ≤ (1 / 16 : NNReal))
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A D.family.bodyFamily) :
    ∃ T : StickyScaleCover (activeOwnerFine C S) (5 * rho),
      T.coarseCard ≤ S.coarseCard *
          Family8PaperConflictOwnerParentFrameFiniteCodeV8.parentFrameCodeCount rho ∧
      ClosedDoubledParentConflictDegreeBound T
        ((1 + katzTaoDoubledFiberNatCap delta (5 * rho) A *
          katzTaoDoubledParentsNatCap delta (5 * rho) A : Nat) : ENNReal) := by
  obtain ⟨T, hT⟩ := exists_activeOwner_stickyScaleCover C S hdeltaSmall
    hdeltaRho hrhoPos hrhoOne
  refine ⟨T, hT, ?_⟩
  have hsmallToHalf : (1 / 100 : NNReal) ≤ (2 : NNReal)⁻¹ := by
    rw [← NNReal.coe_le_coe]
    norm_num [NNReal.coe_div, NNReal.coe_inv]
  apply closedDoubledParentConflictDegreeBound_katzTao
    T hdeltaPos (hdeltaSmall.trans hsmallToHalf) hfiveRho hAfinite
  exact isKatzTao_activeOwnerFine D C S hKT

#print axioms doubledParentsContainingFine_card_mul_halfSq_le_katzTao_elongated
#print axioms doubledParentsContainingFine_card_le_katzTaoDoubledParentsNatCap
#print axioms closedDoubledParentConflictDegreeBound_katzTao
#print axioms exists_activeOwner_stickyScaleCover_with_katzTao_exactConflictDegree

end
end Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
