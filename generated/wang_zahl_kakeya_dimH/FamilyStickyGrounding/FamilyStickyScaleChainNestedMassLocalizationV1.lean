import FamilyStickyGrounding.FamilyStickyScaleChainDiscreteRefinementTreeV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainNestedMassLocalizationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyParentFiberMassDecompositionV6.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyAdjacentTestBodyGeometryV1.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: nested-cover mass localization

This module derives coarse-value localization from the actual parent map of a
`StickyScaleCover`.  The only new analytic inputs are the two earliest local
geometric estimates used by the paper:

* the total mass of one fine parent fiber is controlled by the mass of that
  literal parent;
* thickening a test body which captures a fine tube has controlled volume.

Neither structure stores a concentration, maximal-concentration, splitting,
or threshold inequality.  Parent capture in the thickened test body is the
already proved geometric theorem
`capturedCoarseIndices_subset_containedIndices`.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (S : StickyScaleCover fine rho)

/-- The earliest mass input: within each literal parent fiber, the sum of
all child volumes is at most `massLoss` times the parent volume. -/
structure ParentFiberMassMonotonicity (massLoss : ENNReal) : Prop where
  fiberVolume_le_parent : forall k : {k // k ∈ S.activeCoarse},
    familyVolume (S.fiberFamily k.1) <=
      massLoss * MeasureTheory.volume
        (S.activeCoarseFamily k : Set Space)

/-- The remaining test-body geometry: a body which actually captures a fine
member has a controlled `4 rho` thickening.  Empty captured families never
need this estimate because their contained mass is zero. -/
structure CapturingThickeningVolumeControl (bodyLoss : ENNReal) : Prop where
  thickeningVolume_le : forall K : ConvexBody Space,
    (containedIndices (activeFineFamily S) K).Nonempty ->
      MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) <=
        bodyLoss * MeasureTheory.volume (K : Set Space)

/-- The mass in one captured part is bounded by the full fiber mass and then
by the actual parent mass. -/
theorem fiberMassInside_le_parent
    {massLoss : ENNReal}
    (M : ParentFiberMassMonotonicity S massLoss)
    (K : ConvexBody Space) (k : {k // k ∈ S.activeCoarse}) :
    fiberMassInside S k.1 K <=
      massLoss * MeasureTheory.volume
        (S.activeCoarseFamily k : Set Space) := by
  calc
    fiberMassInside S k.1 K =
        containedMass (S.fiberFamily k.1) K := by
      simpa [containedMass] using
        (fiberFamily_containedNumerator_eq S k.1 K).symm
    _ <= familyVolume (S.fiberFamily k.1) :=
      containedMass_le_familyVolume (S.fiberFamily k.1) K
    _ <= massLoss * MeasureTheory.volume
        (S.activeCoarseFamily k : Set Space) :=
      M.fiberVolume_le_parent k

/-- An uncaptured parent has zero fine mass inside the test body. -/
theorem fiberMassInside_eq_zero_of_not_mem_captured
    (K : ConvexBody Space) (k : {k // k ∈ S.activeCoarse})
    (hk : k ∉ capturedCoarseIndices S K) :
    fiberMassInside S k.1 K = 0 := by
  classical
  have hempty : containedIndices (S.fiberFamily k.1) K = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    apply hk
    rw [mem_capturedCoarseIndices]
    have hiK : (S.fiberFamily k.1 i : Set Space) ⊆ (K : Set Space) :=
      (mem_containedIndices (S.fiberFamily k.1) K i).1 hi
    have hifiber := (S.mem_fiber i.1 k.1).mp i.2
    exact ⟨i.1, hifiber.1, hifiber.2, hiK⟩
  calc
    fiberMassInside S k.1 K =
        containedMass (S.fiberFamily k.1) K := by
      simpa [containedMass] using
        (fiberFamily_containedNumerator_eq S k.1 K).symm
    _ = 0 := by simp [containedMass, hempty]

/-- Exact regrouping of actual fine contained mass over precisely the
parents captured by the test body. -/
theorem containedMass_activeFineFamily_eq_sum_captured
    (K : ConvexBody Space) :
    containedMass (activeFineFamily S) K =
      ∑ k ∈ capturedCoarseIndices S K, fiberMassInside S k.1 K := by
  rw [show containedMass (activeFineFamily S) K =
      activeFineMassInside S K by
    simpa [containedMass] using
      activeFineFamily_containedNumerator_eq S K]
  rw [activeFineMassInside_eq_sum_fiberMassInside]
  have hattach :
      (∑ k ∈ S.activeCoarse, fiberMassInside S k K) =
        ∑ k : {k // k ∈ S.activeCoarse}, fiberMassInside S k.1 K := by
    rw [← Finset.attach_eq_univ]
    exact Finset.sum_attach S.activeCoarse
      (fun k => fiberMassInside S k K) |>.symm
  rw [hattach]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hkUniv hkCaptured
  exact fiberMassInside_eq_zero_of_not_mem_captured S K k hkCaptured

/-- The captured parents form a literal subfamily of the coarse members
contained in the geometrically constructed thickening. -/
theorem capturedParentVolume_le_containedMass_thickening
    (K : ConvexBody Space) :
    (∑ k ∈ capturedCoarseIndices S K,
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) <=
      containedMass S.activeCoarseFamily
        (closedThickeningBody K (4 * rho)) := by
  unfold containedMass
  exact Finset.sum_le_sum_of_subset
    (capturedCoarseIndices_subset_containedIndices S K)

/-- Actual contained-mass localization, produced from parent containment and
the per-parent fiber mass monotonicity. -/
theorem containedMass_activeFineFamily_le_coarseThickening
    {massLoss : ENNReal}
    (M : ParentFiberMassMonotonicity S massLoss)
    (K : ConvexBody Space) :
    containedMass (activeFineFamily S) K <=
      massLoss * containedMass S.activeCoarseFamily
        (closedThickeningBody K (4 * rho)) := by
  rw [containedMass_activeFineFamily_eq_sum_captured S K]
  calc
    (∑ k ∈ capturedCoarseIndices S K, fiberMassInside S k.1 K) <=
        ∑ k ∈ capturedCoarseIndices S K,
          massLoss * MeasureTheory.volume
            (S.activeCoarseFamily k : Set Space) := by
      exact Finset.sum_le_sum fun k _hk => fiberMassInside_le_parent S M K k
    _ = massLoss *
        (∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) := by
      rw [Finset.mul_sum]
    _ <= massLoss * containedMass S.activeCoarseFamily
        (closedThickeningBody K (4 * rho)) :=
      by
        gcongr
        exact capturedParentVolume_le_containedMass_thickening S K

/-- Cross-multiplied Katz--Tao localization.  It is a theorem, not a field:
the numerical coarse-value comparison is synthesized from the actual
contained masses and the two local geometric inputs above. -/
theorem isKatzTao_activeFineFamily_of_nestedGeometry
    {massLoss bodyLoss : ENNReal}
    (M : ParentFiberMassMonotonicity S massLoss)
    (V : CapturingThickeningVolumeControl S bodyLoss) :
    IsKatzTao ((massLoss * bodyLoss) * coarseDeltaMax S)
      (activeFineFamily S) := by
  have hcoarse : IsKatzTao (coarseDeltaMax S) S.activeCoarseFamily :=
    (isKatzTao_iff_concentration_le).2 fun K =>
      concentration_le_maximalConcentration S.activeCoarseFamily K
  intro K
  unfold IsKatzTaoAt
  by_cases hcaptured : (containedIndices (activeFineFamily S) K).Nonempty
  · calc
      containedMass (activeFineFamily S) K <=
          massLoss * containedMass S.activeCoarseFamily
            (closedThickeningBody K (4 * rho)) :=
        containedMass_activeFineFamily_le_coarseThickening S M K
      _ <= massLoss * (coarseDeltaMax S *
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space)) :=
        by
          gcongr
          exact hcoarse (closedThickeningBody K (4 * rho))
      _ <= massLoss * (coarseDeltaMax S *
          (bodyLoss * MeasureTheory.volume (K : Set Space))) := by
        gcongr
        exact V.thickeningVolume_le K hcaptured
      _ = ((massLoss * bodyLoss) * coarseDeltaMax S) *
          MeasureTheory.volume (K : Set Space) := by
        ac_rfl
  · have hempty : containedIndices (activeFineFamily S) K = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcaptured
    simp [containedMass, hempty]

/-- The genuine maximal-concentration localization obtained by taking the
supremum of the preceding cross-multiplied Katz--Tao theorem. -/
theorem fineDeltaMax_le_coarseDeltaMax_of_nestedGeometry
    {massLoss bodyLoss : ENNReal}
    (M : ParentFiberMassMonotonicity S massLoss)
    (V : CapturingThickeningVolumeControl S bodyLoss) :
    fineDeltaMax S <= (massLoss * bodyLoss) * coarseDeltaMax S := by
  unfold fineDeltaMax maximalConcentration
  apply iSup_le
  exact (isKatzTao_iff_concentration_le.mp
    (isKatzTao_activeFineFamily_of_nestedGeometry S M V))

end StickyScaleCover

#print axioms StickyScaleCover.fiberMassInside_le_parent
#print axioms StickyScaleCover.fiberMassInside_eq_zero_of_not_mem_captured
#print axioms StickyScaleCover.containedMass_activeFineFamily_eq_sum_captured
#print axioms StickyScaleCover.capturedParentVolume_le_containedMass_thickening
#print axioms StickyScaleCover.containedMass_activeFineFamily_le_coarseThickening
#print axioms StickyScaleCover.isKatzTao_activeFineFamily_of_nestedGeometry
#print axioms StickyScaleCover.fineDeltaMax_le_coarseDeltaMax_of_nestedGeometry

end
end FamilyStickyScaleChainNestedMassLocalizationV1
