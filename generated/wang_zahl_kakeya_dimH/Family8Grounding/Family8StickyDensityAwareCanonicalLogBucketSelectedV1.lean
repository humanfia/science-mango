import Family8Grounding.Family8StickyDensityAwareCanonicalLogBucketChoiceV1

/-!
# Selected sets of the canonical density-aware logarithmic bucket

The chosen level determines literal selected parent and fine sets.  Their
retention, nonemptiness, efficiency, and refinement relations are proved as
independent projections, before any restricted family or partition is built.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareCanonicalLogBucketSelectedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyDensityAwareLogBranchingNNRealAdapterV1
open Family8StickyDensityAwareCanonicalLogBucketChoiceV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The literal efficient logarithmic parent bucket at the canonical level. -/
def densityAwareSelectedParents
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) : Finset (Fin S.coarseCard) :=
  efficientLogCardBucket fine S.coarse S.activeFine S.parent
    (A : ENNReal) (stickyDensityAwareCoverLossNNReal S A : ENNReal)
      (densityAwareLogBucketLevel S A hA hdelta hrho hactive)

/-- Fine indices whose actual parent belongs to the canonical bucket. -/
def densityAwareSelectedFine
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) : Finset iota :=
  selectedFineIndices S.activeFine S.parent
    (densityAwareSelectedParents S A hA hdelta hrho hactive)

/-- The chosen parent bucket retains the weighted assigned mass. -/
theorem densityAwareSelectedParents_withinFactor
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
      (bodyMassOn fine.bodyFamily S.activeFine)
      (∑ k ∈ densityAwareSelectedParents
          S A hA hdelta hrho hactive,
        assignedBodyMass fine S.activeFine S.parent k) := by
  simpa only [densityAwareSelectedParents] using
    densityAwareLogBucketLevel_spec S A hA hdelta hrho hactive

/-- Positive active-fine mass makes the chosen parent bucket nonempty. -/
theorem densityAwareSelectedParents_nonempty
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedParents
      S A hA hdelta hrho hactive).Nonempty := by
  have hretain := densityAwareSelectedParents_withinFactor
    S A hA hdelta hrho hactive
  have hmassPos := bodyMassOn_pos_of_nonempty
    fine S.activeFine hdelta hactive
  by_contra hnot
  have hempty : densityAwareSelectedParents
      S A hA hdelta hrho hactive = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnot
  unfold WithinFactor at hretain
  rw [hempty] at hretain
  simp at hretain
  exact hmassPos.ne' hretain

/-- Every selected parent is efficient for the same density-aware loss. -/
theorem densityAwareSelectedParents_subset_efficient
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    densityAwareSelectedParents S A hA hdelta hrho hactive ⊆
      efficientParents fine S.coarse S.activeFine S.parent
        (A : ENNReal)
        (stickyDensityAwareCoverLossNNReal S A : ENNReal) := by
  intro k hk
  exact (mem_dyadicFiber
    (efficientParents fine S.coarse S.activeFine S.parent
      (A : ENNReal)
      (stickyDensityAwareCoverLossNNReal S A : ENNReal))
    (fiberLogCardLabel S.activeFine S.parent)
    (densityAwareLogBucketLevel S A hA hdelta hrho hactive) k).1 hk |>.1

/-- Selected efficient parents are actual active parents of `S`. -/
theorem densityAwareSelectedParents_subset_activeCoarse
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    densityAwareSelectedParents S A hA hdelta hrho hactive ⊆
      S.activeCoarse := by
  intro k hk
  have hkEff := densityAwareSelectedParents_subset_efficient
    S A hA hdelta hrho hactive hk
  have hkOcc : k ∈ occupiedParents S.activeFine S.parent :=
    (Finset.mem_filter.mp hkEff).1
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkOcc
  simpa [← hik] using S.parent_mem i hi

/-- The selected fine set is a literal subset of the active fine set. -/
theorem densityAwareSelectedFine_subset_activeFine
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    densityAwareSelectedFine S A hA hdelta hrho hactive ⊆
      S.activeFine :=
  Finset.filter_subset _ _

/-- Nonempty selected parents have a nonempty selected fine preimage. -/
theorem densityAwareSelectedFine_nonempty
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedFine S A hA hdelta hrho hactive).Nonempty := by
  obtain ⟨k, hk⟩ := densityAwareSelectedParents_nonempty
    S A hA hdelta hrho hactive
  have hkEff := densityAwareSelectedParents_subset_efficient
    S A hA hdelta hrho hactive hk
  have hkOcc : k ∈ occupiedParents S.activeFine S.parent :=
    (Finset.mem_filter.mp hkEff).1
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkOcc
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
  rw [hik]
  exact hk

/-- The selected fine set lies in the original refined set. -/
theorem densityAwareSelectedFine_subset_refined
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    densityAwareSelectedFine S A hA hdelta hrho hactive ⊆
      fine.refinement.refined := by
  rw [← S.activeFine_eq_refined]
  exact densityAwareSelectedFine_subset_activeFine
    S A hA hdelta hrho hactive

/-- The selected parent set lies in the coarse refined set. -/
theorem densityAwareSelectedParents_subset_refined
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    densityAwareSelectedParents S A hA hdelta hrho hactive ⊆
      S.coarse.refinement.refined := by
  rw [← S.activeCoarse_eq_refined]
  exact densityAwareSelectedParents_subset_activeCoarse
    S A hA hdelta hrho hactive

/-- The selected-fine body mass is the retained assigned-parent sum. -/
theorem densityAwareSelectedFine_bodyMass_withinFactor
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
      (bodyMassOn fine.bodyFamily S.activeFine)
      (bodyMassOn fine.bodyFamily
        (densityAwareSelectedFine S A hA hdelta hrho hactive)) := by
  simpa only [densityAwareSelectedFine,
    selectedFine_bodyMass_eq_sum_assignedBodyMass] using
      densityAwareSelectedParents_withinFactor
        S A hA hdelta hrho hactive

#print axioms densityAwareSelectedParents
#print axioms densityAwareSelectedFine
#print axioms densityAwareSelectedParents_withinFactor
#print axioms densityAwareSelectedParents_nonempty
#print axioms densityAwareSelectedParents_subset_efficient
#print axioms densityAwareSelectedParents_subset_activeCoarse
#print axioms densityAwareSelectedFine_subset_activeFine
#print axioms densityAwareSelectedFine_nonempty
#print axioms densityAwareSelectedFine_subset_refined
#print axioms densityAwareSelectedParents_subset_refined
#print axioms densityAwareSelectedFine_bodyMass_withinFactor

end
end Family8StickyDensityAwareCanonicalLogBucketSelectedV1
