import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Non-concentration for an active indexed subfamily

The greedy factorization keeps the original index type and records each fiber
as a `Finset` of active indices.  This module gives the corresponding
cross-multiplied Frostman predicate without passing to a subtype.  It also
identifies the two equivalent mass functions used by the finite-density and
non-concentration APIs.
-/

/-- `massInside` and `containedMassOn` are the same indexed sum. -/
theorem massInside_eq_containedMassOn
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι)
    (active : Finset ι) (K : ConvexBody Space) :
    massInside F active K = containedMassOn F active K := by
  classical
  unfold massInside containedMassOn indicesInside containedIndices
  congr 1
  ext i
  simp

/-- Cross-multiplied Frostman non-concentration for a retained active
subfamily inside one ambient convex body.  The first conjunct records actual
containment, and the second is safe when either body has zero volume. -/
def IsFrostmanOn {ι : Type*} [Fintype ι] (C : ℝ≥0∞)
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space) : Prop :=
  (∀ i ∈ active, (F i : Set Space) ⊆ (K : Set Space)) ∧
    ∀ K' : ConvexBody Space, (K' : Set Space) ⊆ (K : Set Space) →
      containedMassOn F active K' * volume (K : Set Space) ≤
        C * containedMassOn F active K * volume (K' : Set Space)

namespace IsFrostmanOn

theorem family_subset
    {ι : Type*} [Fintype ι] {C : ℝ≥0∞}
    {F : ConvexFamily ι} {active : Finset ι} {K : ConvexBody Space}
    (h : IsFrostmanOn C F active K) {i : ι} (hi : i ∈ active) :
    (F i : Set Space) ⊆ (K : Set Space) :=
  h.1 i hi

theorem cross_le
    {ι : Type*} [Fintype ι] {C : ℝ≥0∞}
    {F : ConvexFamily ι} {active : Finset ι} {K K' : ConvexBody Space}
    (h : IsFrostmanOn C F active K)
    (hK' : (K' : Set Space) ⊆ (K : Set Space)) :
    containedMassOn F active K' * volume (K : Set Space) ≤
      C * containedMassOn F active K * volume (K' : Set Space) :=
  h.2 K' hK'

/-- Increasing the Frostman constant preserves active non-concentration. -/
theorem mono
    {ι : Type*} [Fintype ι] {C C' : ℝ≥0∞}
    {F : ConvexFamily ι} {active : Finset ι} {K : ConvexBody Space}
    (h : IsFrostmanOn C F active K) (hCC' : C ≤ C') :
    IsFrostmanOn C' F active K := by
  refine ⟨h.1, fun K' hK' ↦ (h.2 K' hK').trans ?_⟩
  gcongr

end IsFrostmanOn

/-- A global cross inequality for one active subfamily gives its exact
constant-one Frostman certificate in the containing body. -/
theorem isFrostmanOn_one_of_globalCross
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    {active : Finset ι} {K : ConvexBody Space}
    (hcontained : ∀ i ∈ active, (F i : Set Space) ⊆ (K : Set Space))
    (hcross : ∀ K' : ConvexBody Space,
      massInside F active K' * volume (K : Set Space) ≤
        massInside F active K * volume (K' : Set Space)) :
    IsFrostmanOn 1 F active K := by
  refine ⟨hcontained, fun K' _hK' ↦ ?_⟩
  simpa [← massInside_eq_containedMassOn] using hcross K'

/-- The fiber of a full-convex maximal-density choice is genuinely Frostman
inside its winning hull, with constant one and no positive-volume premise. -/
theorem FullConvexMaximalDensity.hullChoice_fiber_isFrostmanOn_one
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    {base active : Finset ι}
    (M : MaximalDensityChoice F active
      (FullConvexMaximalDensity.hullCandidates base)
      (FullConvexMaximalDensity.hullContainer F))
    (hbase : base.Nonempty) (hactive : active ⊆ base) :
    IsFrostmanOn 1 F M.fiber
      (FullConvexMaximalDensity.hullContainer F M.index) := by
  apply isFrostmanOn_one_of_globalCross
  · intro i hi
    exact M.body_subset_container hi
  · intro K
    exact FullConvexMaximalDensity.hullChoice_fiber_frostmanCross_le_all
      M hbase hactive K

end

end Submission.Kakeya.ConvexFactoring
