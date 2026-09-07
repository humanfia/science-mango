import Family8Grounding.Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV4
import Mathlib.Tactic

/-!
# Active-cardinality bound for the canonical selected ambient loss

Only active fine tubes occur in the numerator of the canonical ambient-mass
quotient.  This sharpens the uniform-tube cardinality loss from the cardinality
of the whole ambient index type to the cardinality of the actual active set.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceAverageRetentionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8Prop51SelectedOccurrenceAmbientMassRatioV1
open Family8Prop51SelectedOccurrenceAmbientMassPositiveV2
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta : NNReal} {index kappa : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset index}

theorem containedMassOn_uniformTube_le_activeCard_mul_eight_sq
    (s : Finset index) (K : ConvexBody Space)
    (hcontained : ∀ i ∈ s,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space))
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    containedMassOn fine.bodyFamily s K <=
      (s.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by
  rw [containedMassOn_eq_bodyMassOn_of_contained
    fine.bodyFamily s K hcontained]
  unfold bodyMassOn
  calc
    ∑ i ∈ s, volume (fine.bodyFamily i : Set Space) <=
        ∑ _i ∈ s, 8 * (delta : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun i _hi => by
        simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
          (fine.tubes i).volume_le_eight_mul_sq_of_le_half hdeltaHalf
    _ = (s.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by simp

theorem prop51SelectedAmbientMassLoss_le_max_activeCardinality
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (Y : Shading fine.bodyFamily) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C fine.bodyFamily active K)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    prop51SelectedAmbientMassLoss P Y base M K <=
      max 1 (16 * (active.card : ENNReal)) := by
  classical
  let selected := prop51SelectedFineIndices P Y base M
  let selectedMass := containedMassOn fine.bodyFamily selected K
  have hselectedSubset : selected ⊆ active := by
    exact selectedOccurrenceFineIndices_subset_active P
      (prop51SelectedOccurrences P Y base M)
  have hactiveContained : ∀ i ∈ active,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := hglobal.1
  have hselectedContained : ∀ i ∈ selected,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := by
    intro i hi
    exact hactiveContained i (hselectedSubset hi)
  have hselected0 : selectedMass ≠ 0 := by
    exact prop51SelectedAmbientMass_ne_zero P Y base M K hfull
      hselectedContained
  have hselectedTop : selectedMass ≠ ∞ := by
    exact prop51SelectedAmbientMass_ne_top P Y base M K
  have hselectedSet : selected.Nonempty := by
    by_contra hnonempty
    have hempty : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    apply hselected0
    simp [selectedMass, hempty, containedMassOn]
  obtain ⟨i, hi⟩ := hselectedSet
  have hselectedLower : (delta : ENNReal) ^ 2 / 2 <= selectedMass := by
    exact half_sq_le_containedMassOn_of_mem selected K i hi
      (hselectedContained i hi) hdeltaHalf
  have hfullUpper : containedMassOn fine.bodyFamily active K <=
      (active.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) :=
    containedMassOn_uniformTube_le_activeCard_mul_eight_sq
      active K hactiveContained hdeltaHalf
  have htwo : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hsixteen : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
    calc
      (16 : ENNReal) * (2 : ENNReal)⁻¹ =
          (8 * 2) * (2 : ENNReal)⁻¹ := by norm_num
      _ = 8 * (2 * (2 : ENNReal)⁻¹) := by ring
      _ = 8 := by rw [htwo]; simp
  have hnumeric :
      (active.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) =
        (16 * (active.card : ENNReal)) *
          ((delta : ENNReal) ^ 2 / 2) := by
    rw [div_eq_mul_inv]
    calc
      (active.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) =
          (active.card : ENNReal) * (delta : ENNReal) ^ 2 * 8 := by ring
      _ = (active.card : ENNReal) * (delta : ENNReal) ^ 2 *
          (16 * (2 : ENNReal)⁻¹) := by rw [hsixteen]
      _ = (16 * (active.card : ENNReal)) *
          ((delta : ENNReal) ^ 2 * (2 : ENNReal)⁻¹) := by ring
  have hquotient : containedMassOn fine.bodyFamily active K / selectedMass <=
      16 * (active.card : ENNReal) := by
    apply (ENNReal.div_le_iff hselected0 hselectedTop).2
    calc
      containedMassOn fine.bodyFamily active K <=
          (active.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := hfullUpper
      _ = (16 * (active.card : ENNReal)) *
          ((delta : ENNReal) ^ 2 / 2) := hnumeric
      _ <= (16 * (active.card : ENNReal)) * selectedMass :=
        mul_le_mul' le_rfl hselectedLower
  unfold prop51SelectedAmbientMassLoss
  exact max_le_max le_rfl hquotient

#print axioms containedMassOn_uniformTube_le_activeCard_mul_eight_sq
#print axioms prop51SelectedAmbientMassLoss_le_max_activeCardinality

end
end Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8
