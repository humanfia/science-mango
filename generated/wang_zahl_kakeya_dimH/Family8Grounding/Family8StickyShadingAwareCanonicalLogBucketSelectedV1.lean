import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1

/-!
# Canonical shading-aware logarithmic bucket

On the positive source-shading branch, choose the actual weighted logarithmic
bucket and expose all of its geometric and mass-retention projections.  The
selected sets here are literal subsets of the original Sticky hierarchy; no
object-identification premise is introduced.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareCanonicalLogBucketSelectedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The canonically chosen fiber-cardinality level on the positive shading
mass branch. -/
def shadingAwareLogBucketLevel
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    Fin (Nat.log 2 (Fintype.card iota) + 1) :=
  Classical.choose ((shadingAwareLogBucket_zero_or_exists_certificate
    S Y A hA0 hAtop hrho hactive).resolve_left hmass)

/-- The literal selected parent set at the canonical shading-aware level. -/
def shadingAwareSelectedParents
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    Finset (Fin S.coarseCard) :=
  shadingEfficientLogCardBucket S Y A
    (stickyShadingAwareCoverLoss S Y A)
    (shadingAwareLogBucketLevel S Y A hA0 hAtop hrho hactive hmass)

/-- Fine indices whose actual Sticky parent belongs to the chosen bucket. -/
def shadingAwareSelectedFine
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) : Finset iota :=
  selectedFineIndices S.activeFine S.parent
    (shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass)

/-- The complete certificate of the canonical choice. -/
theorem shadingAwareLogBucketLevel_spec
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
        (shadingMassOn Y S.activeFine)
        (shadingMassOn Y
          (shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass)) ∧
      shadingMassOn Y S.activeFine /
          (2 * (Nat.log 2 (Fintype.card iota) + 1) : Nat) ≤
        shadingMassOn Y
          (shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass) ∧
      (shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass).Nonempty ∧
      (shadingAwareSelectedFine
        S Y A hA0 hAtop hrho hactive hmass).Nonempty ∧
      shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass ⊆
        S.activeCoarse ∧
      shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass ⊆
        S.activeFine ∧
      shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass ⊆
        efficientParents fine S.coarse S.activeFine S.parent A
          (stickyShadingAwareCoverLoss S Y A) ∧
      (∀ k ∈ shadingAwareSelectedParents
          S Y A hA0 hAtop hrho hactive hmass,
        logBucketBranching
            (shadingAwareLogBucketLevel
              S Y A hA0 hAtop hrho hactive hmass) ≤
          ((rawIndexFactorization S.activeFine S.parent).fiber k).card ∧
        ((rawIndexFactorization S.activeFine S.parent).fiber k).card <
          2 * logBucketBranching
            (shadingAwareLogBucketLevel
              S Y A hA0 hAtop hrho hactive hmass)) := by
  simpa only [shadingAwareSelectedParents, shadingAwareSelectedFine, shadingAwareLogBucketLevel] using
    Classical.choose_spec
      ((shadingAwareLogBucket_zero_or_exists_certificate
        S Y A hA0 hAtop hrho hactive).resolve_left hmass)

theorem shadingAwareSelectedParents_nonempty
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass).Nonempty :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).2.2.1

theorem shadingAwareSelectedFine_nonempty
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareSelectedFine
      S Y A hA0 hAtop hrho hactive hmass).Nonempty :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).2.2.2.1

theorem shadingAwareSelectedParents_subset_activeCoarse
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass ⊆
      S.activeCoarse :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).2.2.2.2.1

theorem shadingAwareSelectedFine_subset_activeFine
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass ⊆
      S.activeFine :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).2.2.2.2.2.1

theorem shadingAwareSelectedFine_subset_refined
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass ⊆
      fine.refinement.refined := by
  rw [← S.activeFine_eq_refined]
  exact shadingAwareSelectedFine_subset_activeFine
    S Y A hA0 hAtop hrho hactive hmass

theorem shadingAwareSelectedParents_subset_refined
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass ⊆
      S.coarse.refinement.refined := by
  rw [← S.activeCoarse_eq_refined]
  exact shadingAwareSelectedParents_subset_activeCoarse
    S Y A hA0 hAtop hrho hactive hmass

theorem shadingAwareSelectedFine_withinFactor
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
      (shadingMassOn Y S.activeFine)
      (shadingMassOn Y
        (shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass)) :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).1

theorem shadingAwareSelectedFine_sourceFloor
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    shadingMassOn Y S.activeFine /
        (2 * (Nat.log 2 (Fintype.card iota) + 1) : Nat) ≤
      shadingMassOn Y
        (shadingAwareSelectedFine S Y A hA0 hAtop hrho hactive hmass) :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).2.1

theorem shadingAwareSelectedParents_subset_efficient
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    shadingAwareSelectedParents S Y A hA0 hAtop hrho hactive hmass ⊆
      efficientParents fine S.coarse S.activeFine S.parent A
        (stickyShadingAwareCoverLoss S Y A) :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).2.2.2.2.2.2.1

theorem shadingAwareSelected_fiber_bounds
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    ∀ k ∈ shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass,
      logBucketBranching
          (shadingAwareLogBucketLevel
            S Y A hA0 hAtop hrho hactive hmass) ≤
        ((rawIndexFactorization S.activeFine S.parent).fiber k).card ∧
      ((rawIndexFactorization S.activeFine S.parent).fiber k).card <
        2 * logBucketBranching
          (shadingAwareLogBucketLevel
            S Y A hA0 hAtop hrho hactive hmass) :=
  (shadingAwareLogBucketLevel_spec
    S Y A hA0 hAtop hrho hactive hmass).2.2.2.2.2.2.2

/-- Every selected parent has a selected fine preimage under the original
Sticky parent map. -/
theorem shadingAwareSelected_parent_surjective
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    ∀ k ∈ shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass,
      ∃ i ∈ shadingAwareSelectedFine
          S Y A hA0 hAtop hrho hactive hmass,
        S.parent i = k := by
  intro k hk
  have hkEff := shadingAwareSelectedParents_subset_efficient
    S Y A hA0 hAtop hrho hactive hmass hk
  have hkOcc : k ∈ occupiedParents S.activeFine S.parent :=
    (Finset.mem_filter.mp hkEff).1
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkOcc
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, hik⟩
  rw [hik]
  exact hk

#print axioms shadingAwareLogBucketLevel
#print axioms shadingAwareLogBucketLevel_spec
#print axioms shadingAwareSelectedParents_nonempty
#print axioms shadingAwareSelectedFine_nonempty
#print axioms shadingAwareSelectedFine_subset_refined
#print axioms shadingAwareSelectedParents_subset_refined
#print axioms shadingAwareSelectedFine_withinFactor
#print axioms shadingAwareSelectedFine_sourceFloor
#print axioms shadingAwareSelectedParents_subset_efficient
#print axioms shadingAwareSelected_fiber_bounds
#print axioms shadingAwareSelected_parent_surjective

end
end Family8StickyShadingAwareCanonicalLogBucketSelectedV1
