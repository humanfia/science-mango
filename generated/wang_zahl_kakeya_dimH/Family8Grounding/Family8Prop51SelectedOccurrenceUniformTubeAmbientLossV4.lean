import Family8Grounding.Family8Prop51SelectedOccurrenceAmbientMassPositiveV2
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# Uniform-tube cardinality bound for the canonical ambient loss

The canonical selected fine set is nonempty whenever the retained outer
shading has positive mass.  The standard tube-volume sandwich therefore
bounds its literal full-to-selected ambient mass quotient by
`16 * Fintype.card index`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV4

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

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta : NNReal} {index kappa : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset index}

theorem containedMassOn_uniformTube_le_card_mul_eight_sq
    (s : Finset index) (K : ConvexBody Space)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    containedMassOn fine.bodyFamily s K <=
      (Fintype.card index : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by
  calc
    containedMassOn fine.bodyFamily s K <=
        containedMassOn fine.bodyFamily Finset.univ K :=
      containedMassOn_mono (Finset.subset_univ s) K
    _ = containedMass fine.bodyFamily K := containedMassOn_univ _ _
    _ <= familyVolume fine.bodyFamily :=
      containedMass_le_familyVolume fine.bodyFamily K
    _ <= ∑ _i : index, 8 * (delta : ENNReal) ^ 2 := by
      unfold familyVolume
      exact Finset.sum_le_sum fun i _hi =>
        (fine.tubes i).volume_le_eight_mul_sq_of_le_half hdeltaHalf
    _ = (Fintype.card index : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by simp

theorem half_sq_le_containedMassOn_of_mem
    (s : Finset index) (K : ConvexBody Space) (i : index)
    (hi : i ∈ s)
    (hcontained : (fine.bodyFamily i : Set Space) ⊆ (K : Set Space))
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    (delta : ENNReal) ^ 2 / 2 <=
      containedMassOn fine.bodyFamily s K := by
  have hsingleton : ({i} : Finset index) ⊆ s := by simpa using hi
  have hsingletonContained : ∀ j ∈ ({i} : Finset index),
      (fine.bodyFamily j : Set Space) ⊆ (K : Set Space) := by
    intro j hj
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    exact hcontained
  calc
    (delta : ENNReal) ^ 2 / 2 <= volume (fine.tubes i).carrier :=
      (fine.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
    _ = bodyMassOn fine.bodyFamily ({i} : Finset index) := by
      simp [bodyMassOn, UniformTubeFamily.bodyFamily, Tube.coe_body]
    _ = containedMassOn fine.bodyFamily ({i} : Finset index) K :=
      (containedMassOn_eq_bodyMassOn_of_contained
        fine.bodyFamily ({i} : Finset index) K hsingletonContained).symm
    _ <= containedMassOn fine.bodyFamily s K :=
      containedMassOn_mono hsingleton K

theorem prop51SelectedAmbientMassLoss_le_max_cardinality
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (Y : Shading fine.bodyFamily) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C fine.bodyFamily active K)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    prop51SelectedAmbientMassLoss P Y base M K <=
      max 1 (16 * (Fintype.card index : ENNReal)) := by
  classical
  let selected := prop51SelectedFineIndices P Y base M
  let selectedMass := containedMassOn fine.bodyFamily selected K
  have hselectedSubset : selected ⊆ active := by
    exact selectedOccurrenceFineIndices_subset_active P
      (prop51SelectedOccurrences P Y base M)
  have hselectedContained : ∀ i ∈ selected,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := by
    intro i hi
    exact hglobal.1 i (hselectedSubset hi)
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
      (Fintype.card index : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) :=
    containedMassOn_uniformTube_le_card_mul_eight_sq active K hdeltaHalf
  have htwo : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hsixteen : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
    calc
      (16 : ENNReal) * (2 : ENNReal)⁻¹ =
          (8 * 2) * (2 : ENNReal)⁻¹ := by norm_num
      _ = 8 * (2 * (2 : ENNReal)⁻¹) := by ring
      _ = 8 := by rw [htwo]; simp
  have hnumeric :
      (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) =
        (16 * (Fintype.card index : ENNReal)) *
          ((delta : ENNReal) ^ 2 / 2) := by
    rw [div_eq_mul_inv]
    calc
      (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) =
          (Fintype.card index : ENNReal) * (delta : ENNReal) ^ 2 * 8 := by
        ring
      _ = (Fintype.card index : ENNReal) * (delta : ENNReal) ^ 2 *
          (16 * (2 : ENNReal)⁻¹) := by rw [hsixteen]
      _ = (16 * (Fintype.card index : ENNReal)) *
          ((delta : ENNReal) ^ 2 * (2 : ENNReal)⁻¹) := by ring
  have hquotient : containedMassOn fine.bodyFamily active K / selectedMass <=
      16 * (Fintype.card index : ENNReal) := by
    apply (ENNReal.div_le_iff hselected0 hselectedTop).2
    calc
      containedMassOn fine.bodyFamily active K <=
          (Fintype.card index : ENNReal) *
            (8 * (delta : ENNReal) ^ 2) := hfullUpper
      _ = (16 * (Fintype.card index : ENNReal)) *
          ((delta : ENNReal) ^ 2 / 2) := hnumeric
      _ <= (16 * (Fintype.card index : ENNReal)) * selectedMass :=
        mul_le_mul' le_rfl hselectedLower
  unfold prop51SelectedAmbientMassLoss
  exact max_le_max le_rfl hquotient

#print axioms containedMassOn_uniformTube_le_card_mul_eight_sq
#print axioms half_sq_le_containedMassOn_of_mem
#print axioms prop51SelectedAmbientMassLoss_le_max_cardinality

end
end Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV4
