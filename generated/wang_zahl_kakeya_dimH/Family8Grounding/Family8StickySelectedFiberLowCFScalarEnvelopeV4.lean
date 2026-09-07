import Family8Grounding.Family8StickySelectedFiberLocalFrostmanKatzTaoV1
import Family8Grounding.Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
import Mathlib.Tactic

/-!
# Scalar envelope for the retained-parent low-CF branch

The local Frostman constant carries the exact ambient family-volume density.
This file proves that constant finite and bounds it by the literal retained
cardinality.  The contracted-John proxy and greedy closed loss then inherit
an explicit source-only card envelope.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFScalarEnvelopeV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8ContractedJohnAffineJacobianLowerV3
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnGlobalNormalizedFreshV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Exact source Katz--Tao constant produced by a low-CF certificate after
the honest selected-subtype retention loss. -/
def selectedFiberLowCFSourceConstant
    (S : StickyScaleCover fine rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower L : ENNReal) : ENNReal :=
  (lower * (16 * L)) *
    ambientFamilyVolumeDensity
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q)

/-- Card-only upper envelope for the exact low-CF source constant. -/
def selectedFiberLowCFCardEnvelope
    (S : StickyScaleCover fine rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower L : ENNReal) : ENNReal :=
  (lower * (16 * L)) * (selected.card : ENNReal)

/-- The exact low-CF source constant is finite under only the finiteness of
the displayed barrier and retention factor. -/
theorem selectedFiberLowCFSourceConstant_ne_top
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower L : ENNReal}
    (hlower : lower ≠ ∞) (hL : L ≠ ∞) :
    selectedFiberLowCFSourceConstant S q selected lower L ≠ ∞ := by
  unfold selectedFiberLowCFSourceConstant
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top hlower
      (ENNReal.mul_ne_top (by norm_num) hL)
  · apply ambientFamilyVolumeDensity_ne_top
    change volume (S.coarse.tubes q.1).carrier ≠ 0
    exact (Tube.volume_pos (S.coarse.tubes q.1) hrho).ne'

/-- Containment in the actual parent bounds the exact ambient density by the
literal retained cardinality. -/
theorem selectedFiberLowCFSourceConstant_le_cardEnvelope
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower L : ENNReal) :
    selectedFiberLowCFSourceConstant S q selected lower L ≤
      selectedFiberLowCFCardEnvelope S q selected lower L := by
  unfold selectedFiberLowCFSourceConstant selectedFiberLowCFCardEnvelope
  apply mul_le_mul' le_rfl
  have hcontained : ∀ i : {i // i ∈ selected},
      (activeSubtypeFamily (S.fiberFamily q.1) selected i : Set Space) ⊆
        (S.activeCoarseFamily q : Set Space) := by
    intro i
    exact S.fiber_carrier_subset_parent q.1 i.1
  have hvolume0 : volume (S.activeCoarseFamily q : Set Space) ≠ 0 := by
    change volume (S.coarse.tubes q.1).carrier ≠ 0
    exact (Tube.volume_pos (S.coarse.tubes q.1) hrho).ne'
  simpa only [Fintype.card_coe] using
    (ambientFamilyVolumeDensity_le_card
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q) hcontained hvolume0)

/-- The normalized selected proxy Katz--Tao constant is finite. -/
theorem selectedFiberLowCF_normalizedConstant_ne_top
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower L : ENNReal}
    (hlower : lower ≠ ∞) (hL : L ≠ ∞) :
    128 * stickyFiberContractedJohnProxyKatzTaoConstant
      S hrho hrhoOne q
        (selectedFiberLowCFSourceConstant S q selected lower L) ≠ ∞ := by
  apply ENNReal.mul_ne_top (by norm_num)
  apply stickyFiberContractedJohnProxyKatzTaoConstant_ne_top
    S hrho hrhoOne hdelta q
  exact selectedFiberLowCFSourceConstant_ne_top
    S hrho q selected hlower hL

/-- The exact normalized proxy constant is bounded by the universal
contracted-John factor times the retained-card source envelope. -/
theorem selectedFiberLowCF_normalizedConstant_le_cardEnvelope
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower L : ENNReal) :
    128 * stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne q
          (selectedFiberLowCFSourceConstant S q selected lower L) ≤
      128 * (93312 * selectedFiberLowCFCardEnvelope S q selected lower L) := by
  calc
    128 * stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne q
          (selectedFiberLowCFSourceConstant S q selected lower L) ≤
      128 * (93312 *
        selectedFiberLowCFSourceConstant S q selected lower L) := by
        gcongr
        exact stickyFiberContractedJohnProxyKatzTaoConstant_le_fixed
          S hdelta hrho hrhoOne q
            (selectedFiberLowCFSourceConstant S q selected lower L)
    _ ≤ 128 * (93312 *
        selectedFiberLowCFCardEnvelope S q selected lower L) := by
      gcongr
      exact selectedFiberLowCFSourceConstant_le_cardEnvelope
        S hrho q selected lower L

/-- The literal proxy greedy loss is bounded by the source-only closed loss
at the retained-card envelope. -/
theorem selectedFiberLowCF_proxyClosedLoss_le_cardEnvelope
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower L : ENNReal) :
    480000 *
          (128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne q
              (selectedFiberLowCFSourceConstant S q selected lower L)) + 2 ≤
      stickyFiberContractedJohnSourceClosedLoss
        (selectedFiberLowCFCardEnvelope S q selected lower L) := by
  unfold stickyFiberContractedJohnSourceClosedLoss
  have hmul :
      (480000 : ENNReal) *
          (128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne q
              (selectedFiberLowCFSourceConstant S q selected lower L)) ≤
        480000 *
          (128 * (93312 *
            selectedFiberLowCFCardEnvelope S q selected lower L)) :=
    mul_le_mul' le_rfl
      (selectedFiberLowCF_normalizedConstant_le_cardEnvelope
        S hdelta hrho hrhoOne q selected lower L)
  simpa only [add_comm] using (add_le_add_right hmul 2)

#print axioms selectedFiberLowCFSourceConstant_ne_top
#print axioms selectedFiberLowCFSourceConstant_le_cardEnvelope
#print axioms selectedFiberLowCF_normalizedConstant_ne_top
#print axioms selectedFiberLowCF_normalizedConstant_le_cardEnvelope
#print axioms selectedFiberLowCF_proxyClosedLoss_le_cardEnvelope

end
end Family8StickySelectedFiberLowCFScalarEnvelopeV4
