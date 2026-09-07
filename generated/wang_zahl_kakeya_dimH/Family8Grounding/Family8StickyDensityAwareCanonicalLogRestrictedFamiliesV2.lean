import Family8Grounding.Family8StickyDensityAwareCanonicalLogBucketSelectedV1

/-!
# Restricted families for the canonical density-aware logarithmic bucket

The selected sets restrict only refinement metadata, so the tube geometry is
definitionally unchanged.  Parent surjectivity is exposed separately for the
subsequent partition constructor.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareCanonicalLogRestrictedFamiliesV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyDensityAwareLogBranchingNNRealAdapterV1
open Family8StickyDensityAwareCanonicalLogBucketSelectedV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Restrict the fine refinement to the canonically selected fine indices. -/
def densityAwareSelectedFineFamily
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    UniformTubeFamily delta iota :=
  restrictUniformTubeFamilyNonempty fine
    (densityAwareSelectedFine S A hA hdelta hrho hactive)
    (densityAwareSelectedFine_subset_refined
      S A hA hdelta hrho hactive)
    (densityAwareSelectedFine_nonempty
      S A hA hdelta hrho hactive)

/-- Restrict the coarse refinement to the canonically selected parents. -/
def densityAwareSelectedCoarseFamily
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    UniformTubeFamily rho (Fin S.coarseCard) :=
  restrictUniformTubeFamilyNonempty S.coarse
    (densityAwareSelectedParents S A hA hdelta hrho hactive)
    (densityAwareSelectedParents_subset_refined
      S A hA hdelta hrho hactive)
    (densityAwareSelectedParents_nonempty
      S A hA hdelta hrho hactive)

@[simp] theorem densityAwareSelectedFineFamily_tubes
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) (i : iota) :
    (densityAwareSelectedFineFamily
      S A hA hdelta hrho hactive).tubes i = fine.tubes i :=
  rfl

@[simp] theorem densityAwareSelectedCoarseFamily_tubes
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) (k : Fin S.coarseCard) :
    (densityAwareSelectedCoarseFamily
      S A hA hdelta hrho hactive).tubes k = S.coarse.tubes k :=
  rfl

@[simp] theorem densityAwareSelectedFineFamily_refined
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedFineFamily
      S A hA hdelta hrho hactive).refinement.refined =
      densityAwareSelectedFine S A hA hdelta hrho hactive :=
  rfl

@[simp] theorem densityAwareSelectedCoarseFamily_refined
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    (densityAwareSelectedCoarseFamily
      S A hA hdelta hrho hactive).refinement.refined =
      densityAwareSelectedParents S A hA hdelta hrho hactive :=
  rfl

/-- Each selected parent has a selected fine preimage under the same actual
parent map. -/
theorem densityAwareSelected_parent_surjective
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    ∀ k ∈ densityAwareSelectedParents S A hA hdelta hrho hactive,
      ∃ i ∈ densityAwareSelectedFine S A hA hdelta hrho hactive,
        S.parent i = k := by
  intro k hk
  have hkEff := densityAwareSelectedParents_subset_efficient
    S A hA hdelta hrho hactive hk
  have hkOcc : k ∈ occupiedParents S.activeFine S.parent :=
    (Finset.mem_filter.mp hkEff).1
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkOcc
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, hik⟩
  rw [hik]
  exact hk

#print axioms densityAwareSelectedFineFamily
#print axioms densityAwareSelectedCoarseFamily
#print axioms densityAwareSelectedFineFamily_tubes
#print axioms densityAwareSelectedCoarseFamily_tubes
#print axioms densityAwareSelectedFineFamily_refined
#print axioms densityAwareSelectedCoarseFamily_refined
#print axioms densityAwareSelected_parent_surjective

end
end Family8StickyDensityAwareCanonicalLogRestrictedFamiliesV2
