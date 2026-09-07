import Family8Grounding.Family8IsFrostmanInActiveSubtypeRetentionV2
import Family8Grounding.Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8
import Mathlib.Tactic

/-!
# Uniform-tube cardinal retention implies Frostman retention, V2

For two literal finite subfamilies of one equal-radius tube family, a
cardinality retention inequality converts to contained-mass retention with
the explicit geometric loss `16`. The second theorem feeds precisely that
mass inequality to the existing subset Frostman transport. The upstream
`IsFrostmanOn` certificate remains an explicit hypothesis. V1 omitted the
namespace of one contained-mass identity and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8UniformTubeCardRetentionFrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8

noncomputable section

universe u

/-- A cardinality-retained literal subfamily retains contained tube-body
mass with the exact equal-radius volume-sandwich loss `16`. -/
theorem containedMassOn_le_sixteen_mul_cardLoss_mul_selected
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (full selected : Finset iota) (K : ConvexBody Space)
    (hselected : selected ⊆ full)
    (hcontained : ∀ i, i ∈ full →
      (fine.tubes i).carrier ⊆ (K : Set Space))
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {L : ENNReal}
    (hcard : (full.card : ENNReal) ≤
      L * (selected.card : ENNReal)) :
    containedMassOn fine.bodyFamily full K ≤
      (16 * L) * containedMassOn fine.bodyFamily selected K := by
  have hselectedContained : ∀ i, i ∈ selected →
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := by
    intro i hi
    exact hcontained i (hselected hi)
  have hfullUpper : containedMassOn fine.bodyFamily full K ≤
      (full.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) :=
    containedMassOn_uniformTube_le_activeCard_mul_eight_sq
      full K hcontained hdeltaHalf
  have hselectedLower :
      (selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) ≤
        containedMassOn fine.bodyFamily selected K := by
    rw [containedMassOn_eq_bodyMassOn_of_contained
      fine.bodyFamily selected K hselectedContained]
    unfold bodyMassOn
    calc
      (selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) =
          ∑ _i ∈ selected, ((delta : ENNReal) ^ 2 / 2) := by simp
      _ ≤ ∑ i ∈ selected, volume (fine.bodyFamily i : Set Space) := by
        exact Finset.sum_le_sum fun i _hi ↦ by
          simpa only [UniformTubeFamily.bodyFamily_apply, Tube.coe_body] using
            (fine.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
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
  calc
    containedMassOn fine.bodyFamily full K ≤
        (full.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := hfullUpper
    _ ≤ (L * (selected.card : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2) := mul_le_mul' hcard le_rfl
    _ = (16 * L) *
          ((selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2)) :=
      hnumeric
    _ ≤ (16 * L) * containedMassOn fine.bodyFamily selected K :=
      mul_le_mul' le_rfl hselectedLower

/-- Restrict an explicitly supplied `IsFrostmanOn` certificate to a
cardinality-retained literal subtype, paying exactly `16 * L`. -/
theorem isFrostmanIn_activeSubtype_of_card_retention
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (full selected : Finset iota) (K : ConvexBody Space)
    {C L : ENNReal}
    (hselected : selected ⊆ full)
    (hF : IsFrostmanOn C fine.bodyFamily full K)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hcard : (full.card : ENNReal) ≤
      L * (selected.card : ENNReal)) :
    IsFrostmanIn (C * (16 * L))
      (activeSubtypeFamily fine.bodyFamily selected) K := by
  have hretained : containedMassOn fine.bodyFamily full K ≤
      (16 * L) * containedMassOn fine.bodyFamily selected K :=
    containedMassOn_le_sixteen_mul_cardLoss_mul_selected
      fine full selected K hselected hF.1 hdeltaHalf hcard
  have hselectedFrostman : IsFrostmanOn (C * (16 * L))
      fine.bodyFamily selected K :=
    isFrostmanOn_subset_of_ambientMass_retention
      hselected hF hretained
  exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    fine.bodyFamily selected K).mp hselectedFrostman

end
end Family8UniformTubeCardRetentionFrostmanV2
