import Family8Grounding.Family8StickyShadingAwareCanonicalLogBucketSelectedV1

/-!
# Restricted families for the canonical shading-aware bucket

The refinement metadata is restricted to the actual shading-aware selected
sets while every tube is kept definitionally unchanged.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareCanonicalLogRestrictedFamiliesV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Restrict the fine family to the actual shading-aware selected fine set. -/
def shadingAwareSelectedFineFamily
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    UniformTubeFamily delta iota :=
  restrictUniformTubeFamilyNonempty fine
    (shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass)
    (shadingAwareSelectedFine_subset_refined
      S Y A hA0 hAtop hrho hactive hmass)
    (shadingAwareSelectedFine_nonempty
      S Y A hA0 hAtop hrho hactive hmass)

/-- Restrict the coarse family to the same actual selected parent set. -/
def shadingAwareSelectedCoarseFamily
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    UniformTubeFamily rho (Fin S.coarseCard) :=
  restrictUniformTubeFamilyNonempty S.coarse
    (shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass)
    (shadingAwareSelectedParents_subset_refined
      S Y A hA0 hAtop hrho hactive hmass)
    (shadingAwareSelectedParents_nonempty
      S Y A hA0 hAtop hrho hactive hmass)

@[simp] theorem shadingAwareSelectedFineFamily_tubes
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) (i : iota) :
    (shadingAwareSelectedFineFamily
      S Y A hA0 hAtop hrho hactive hmass).tubes i = fine.tubes i :=
  rfl

@[simp] theorem shadingAwareSelectedCoarseFamily_tubes
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) (k : Fin S.coarseCard) :
    (shadingAwareSelectedCoarseFamily
      S Y A hA0 hAtop hrho hactive hmass).tubes k = S.coarse.tubes k :=
  rfl

@[simp] theorem shadingAwareSelectedFineFamily_refined
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareSelectedFineFamily
      S Y A hA0 hAtop hrho hactive hmass).refinement.refined =
      shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass :=
  rfl

@[simp] theorem shadingAwareSelectedCoarseFamily_refined
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareSelectedCoarseFamily
      S Y A hA0 hAtop hrho hactive hmass).refinement.refined =
      shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass :=
  rfl

theorem shadingAwareSelected_parent_surjective_restricted
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    ∀ k ∈ shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass,
      ∃ i ∈ shadingAwareSelectedFine
          S Y A hA0 hAtop hrho hactive hmass,
        S.parent i = k :=
  shadingAwareSelected_parent_surjective
    S Y A hA0 hAtop hrho hactive hmass

#print axioms shadingAwareSelectedFineFamily
#print axioms shadingAwareSelectedCoarseFamily
#print axioms shadingAwareSelectedFineFamily_tubes
#print axioms shadingAwareSelectedCoarseFamily_tubes
#print axioms shadingAwareSelectedFineFamily_refined
#print axioms shadingAwareSelectedCoarseFamily_refined
#print axioms shadingAwareSelected_parent_surjective_restricted

end
end Family8StickyShadingAwareCanonicalLogRestrictedFamiliesV1
