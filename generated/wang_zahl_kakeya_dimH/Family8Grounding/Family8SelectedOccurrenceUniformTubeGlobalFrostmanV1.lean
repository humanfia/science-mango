import Family8Grounding.Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8
import Mathlib.Tactic

/-!
# Global-to-selected occurrence Frostman transfer for uniform tubes

An arbitrary nonempty occurrence selection need not retain a fixed fraction
of body mass.  For uniform tubes, however, one selected tube supplies the
universal lower volume while the whole active family has the card-weighted
upper volume.  Thus global normalized Frostman control restricts to any
nonempty literal selected occurrence set with the honest `16 * active.card`
loss.  No shaded-mass or target conclusion is assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceUniformTubeGlobalFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV4
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index kappa : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {candidates : Finset kappa}
  {container : kappa → ConvexBody Space} {active : Finset index}

/-- A nonempty literal occurrence restriction of a global uniform-tube
Frostman family loses at most `16 * active.card` in its normalization. -/
theorem selectedOccurrence_source_frostman_of_selectedFine_nonempty
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C fine.bodyFamily active K)
    (hselected : (selectedOccurrenceFineIndices P R).Nonempty)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsFrostmanOn (C * (16 * (active.card : ENNReal)))
      fine.bodyFamily (selectedOccurrenceFineIndices P R) K := by
  let selected := selectedOccurrenceFineIndices P R
  have hsubset : selected ⊆ active :=
    selectedOccurrenceFineIndices_subset_active P R
  have hactiveContained : ∀ i ∈ active,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := hglobal.1
  have hselectedContained : ∀ i ∈ selected,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := by
    intro i hi
    exact hactiveContained i (hsubset hi)
  obtain ⟨i, hi⟩ := hselected
  have hselectedLower : (delta : ENNReal) ^ 2 / 2 ≤
      containedMassOn fine.bodyFamily selected K :=
    half_sq_le_containedMassOn_of_mem selected K i hi
      (hselectedContained i hi) hdeltaHalf
  have hfullUpper : containedMassOn fine.bodyFamily active K ≤
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
  have hretained : containedMassOn fine.bodyFamily active K ≤
      (16 * (active.card : ENNReal)) *
        containedMassOn fine.bodyFamily selected K := by
    calc
      containedMassOn fine.bodyFamily active K ≤
          (active.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) :=
        hfullUpper
      _ = (16 * (active.card : ENNReal)) *
          ((delta : ENNReal) ^ 2 / 2) := hnumeric
      _ ≤ (16 * (active.card : ENNReal)) *
          containedMassOn fine.bodyFamily selected K :=
        mul_le_mul' le_rfl hselectedLower
  exact isFrostmanOn_subset_of_ambientMass_retention hsubset hglobal
    (by simpa only [selected] using hretained)

#print axioms
  selectedOccurrence_source_frostman_of_selectedFine_nonempty

end
end Family8SelectedOccurrenceUniformTubeGlobalFrostmanV1
