import Family8Grounding.Family8StickyShadingAwareSelectedMassPopularFiberV2
import Mathlib.Tactic

/-!
# Mass retained by the actual mass-popular Sticky fibre

The card endpoint intentionally forgets the stronger intermediate estimate
used by its selector.  This proof-only successor exports that estimate for
the very same actual selected parent, without introducing a scalar callback.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareSelectedMassPopularFiberMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareSelectedFiberDensityCrossV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The maximum-mass parent in the retained logarithmic bucket controls the
entire active source mass, with exactly the selector's logarithmic loss. -/
theorem exists_shadingAwareSelected_massPopular_wholeFiber_mass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    let selected := shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass
    let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
    ∃ k ∈ selected,
      shadingMassOn Y S.activeFine ≤
        (retention : ENNReal) * (selected.card : ENNReal) *
          (stickyFiberSourceShading S Y k).shadingMass := by
  dsimp only
  let selected := shadingAwareSelectedParents
    S Y A hA0 hAtop hrho hactive hmass
  let selectedFine := selectedFineIndices S.activeFine S.parent selected
  let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  have hselected : selected.Nonempty := by
    simpa only [selected] using shadingAwareSelectedParents_nonempty
      S Y A hA0 hAtop hrho hactive hmass
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image selected
    (assignedShadingMass S Y) hselected
  have hretain := shadingAwareSelectedFine_withinFactor
    S Y A hA0 hAtop hrho hactive hmass
  have hretain' : shadingMassOn Y S.activeFine ≤
      (retention : ENNReal) * shadingMassOn Y selectedFine := by
    unfold WithinFactor at hretain
    simpa only [retention, selectedFine, selected,
      shadingAwareSelectedFine, nsmul_eq_mul] using hretain
  have hselectedMass : shadingMassOn Y selectedFine =
      ∑ k ∈ selected, assignedShadingMass S Y k := by
    simpa only [selectedFine] using
      selectedFine_shadingMass_eq_sum_assignedShadingMass S Y selected
  have hsum : shadingMassOn Y selectedFine ≤
      (selected.card : ENNReal) * assignedShadingMass S Y k := by
    rw [hselectedMass]
    calc
      (∑ k' ∈ selected, assignedShadingMass S Y k') ≤
          selected.card • assignedShadingMass S Y k :=
        Finset.sum_le_card_nsmul selected
          (assignedShadingMass S Y) (assignedShadingMass S Y k)
          (fun k' hk' => hmax k' hk')
      _ = (selected.card : ENNReal) * assignedShadingMass S Y k := by
        simp only [nsmul_eq_mul]
  refine ⟨k, by simpa only [selected] using hk, ?_⟩
  calc
    shadingMassOn Y S.activeFine ≤
        (retention : ENNReal) * shadingMassOn Y selectedFine := hretain'
    _ ≤ (retention : ENNReal) *
        ((selected.card : ENNReal) * assignedShadingMass S Y k) :=
      mul_le_mul' le_rfl hsum
    _ = (retention : ENNReal) * (selected.card : ENNReal) *
        (stickyFiberSourceShading S Y k).shadingMass := by
      rw [assignedShadingMass_eq_stickyFiberSourceShading_shadingMass]
      ring

#print axioms exists_shadingAwareSelected_massPopular_wholeFiber_mass

end
end Family8StickyShadingAwareSelectedMassPopularFiberMassV1
