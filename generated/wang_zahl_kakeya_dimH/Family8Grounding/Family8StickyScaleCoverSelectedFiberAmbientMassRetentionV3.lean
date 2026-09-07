import Family8Grounding.Family8IsFrostmanInActiveSubtypeRetentionV2
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# Ambient-mass retention in one selected Sticky fibre, V3

The equal-radius tube-volume sandwich converts exact cardinality retention
inside a prescribed parent into the contained-mass retention needed to
restrict `IsFrostmanIn`, at the explicit loss `16`.  V1 exceeded the memory
envelope through a deep import and V2 omitted one namespace/cardinality
rewrite; neither is imported here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverSelectedFiberAmbientMassRetentionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8IsFrostmanInActiveSubtypeRetentionV2
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A cardinality-retained subset of one actual parent fibre retains its
contained body mass in that same parent up to `16 * L`. -/
theorem fiber_containedMass_le_sixteen_mul_cardLoss_mul_selected
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {L : ENNReal}
    (hcard : (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) <=
      L * (selected.card : ENNReal)) :
    containedMass (S.fiberFamily q.1) (S.activeCoarseFamily q) <=
      (16 * L) *
        containedMass
          (activeSubtypeFamily (S.fiberFamily q.1) selected)
          (S.activeCoarseFamily q) := by
  let Fq := S.fiberFamily q.1
  let Fs := activeSubtypeFamily Fq selected
  have hfullContained : forall i,
      (Fq i : Set Space) <= (S.activeCoarseFamily q : Set Space) := by
    intro i
    exact fiberFamily_subset_parent S q i
  have hselectedContained : forall i,
      (Fs i : Set Space) <= (S.activeCoarseFamily q : Set Space) := by
    intro i
    exact hfullContained i.1
  have hfullMass :
      containedMass Fq (S.activeCoarseFamily q) = familyVolume Fq :=
    Family6CanonicalFrostmanConstantCoreV1.containedMass_eq_familyVolume_of_contained
      Fq (S.activeCoarseFamily q) hfullContained
  have hselectedMass :
      containedMass Fs (S.activeCoarseFamily q) = familyVolume Fs :=
    Family6CanonicalFrostmanConstantCoreV1.containedMass_eq_familyVolume_of_contained
      Fs (S.activeCoarseFamily q) hselectedContained
  have hfullUpper : familyVolume Fq <=
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
    unfold familyVolume Fq
    simp only [StickyScaleCover.fiberFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body]
    calc
      (∑ i : {i // i ∈ S.fiber q.1},
          volume (fine.tubes i.1).carrier) <=
          ∑ _i : {i // i ∈ S.fiber q.1},
            8 * (delta : ENNReal) ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          (fine.tubes i.1).volume_le_eight_mul_sq_of_le_half hdeltaHalf
      _ = (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_coe]
  have hselectedLower :
      (selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
        familyVolume Fs := by
    unfold familyVolume Fs activeSubtypeFamily Fq
    simp only [StickyScaleCover.fiberFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body]
    calc
      (selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) =
          ∑ _i : {i // i ∈ selected},
            ((delta : ENNReal) ^ 2 / 2) := by simp
      _ <= ∑ i : {i // i ∈ selected},
          volume (fine.tubes i.1.1).carrier := by
        exact Finset.sum_le_sum fun i _ =>
          (fine.tubes i.1.1).half_sq_le_volume_of_le_half hdeltaHalf
  have hsixteen : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
    calc
      (16 : ENNReal) * (2 : ENNReal)⁻¹ =
          (8 * 2) * (2 : ENNReal)⁻¹ := by norm_num
      _ = 8 * (2 * (2 : ENNReal)⁻¹) := by ring
      _ = 8 := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        simp
  have hnumeric :
      (L * (selected.card : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2) =
        (16 * L) *
          ((selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2)) := by
    rw [div_eq_mul_inv, ← hsixteen]
    ring
  rw [hfullMass, hselectedMass]
  calc
    familyVolume Fq <=
        (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := hfullUpper
    _ <= (L * (selected.card : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2) := mul_le_mul' hcard le_rfl
    _ = (16 * L) *
          ((selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2)) :=
      hnumeric
    _ <= (16 * L) * familyVolume Fs :=
      mul_le_mul' le_rfl hselectedLower

/-- The low-CF certificate therefore restricts to the retained literal
subtype with the explicit constant `lower * (16 * L)`. -/
theorem lowCF_isFrostmanIn_selected_of_card_retention
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower L : ENNReal}
    (hF : IsFrostmanIn lower
      (S.fiberFamily q.1) (S.activeCoarseFamily q))
    (hcard : (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) <=
      L * (selected.card : ENNReal)) :
    IsFrostmanIn (lower * (16 * L))
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q) := by
  apply isFrostmanIn_activeSubtype_of_ambientMass_retention selected hF
  exact fiber_containedMass_le_sixteen_mul_cardLoss_mul_selected
    S hdeltaHalf q selected hcard

#print axioms fiber_containedMass_le_sixteen_mul_cardLoss_mul_selected
#print axioms lowCF_isFrostmanIn_selected_of_card_retention

end
end Family8StickyScaleCoverSelectedFiberAmbientMassRetentionV3
