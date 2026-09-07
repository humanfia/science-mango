import Family8Grounding.Family8StickySelectedFineAssemblyFiberBridgeV1
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFineAssemblyDenseProductV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineDenseFiberV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Same-parent dense fibre and assembly product

The selected-fine density pigeonhole and the frozen assembly product are
composed on one literal selected parent.  Thus the fibre sent to the
contracted-John endpoint is exactly the second actual-average factor in the
assembly product, rather than an unrelated existential fibre.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal selected refinement has exactly the final refinement mass. -/
theorem selectedFineShading_refinement_shadingMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r) :
    (selectedFineShading S A.refinement.indices
      A.refinement.shading).shadingMass =
        A.refinement.shading.shadingMass := by
  change (actualRefinementShading A).shadingMass =
    A.refinement.shading.shadingMass
  exact actualRefinementShading_shadingMass A

/-- A source-positive assembly admits one actual selected parent that is
density-good for the contracted-John source and is simultaneously the second
factor in the exact four-times assembly average product. -/
theorem exists_selectedFine_dense_sameAssemblyFiber_product
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (hdelta : 0 < delta)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      (selectedFineShading S A.refinement.indices
          A.refinement.shading).shadingDensity ≤
        (stickyFiberSourceShading
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A))
          (selectedFineShading S A.refinement.indices A.refinement.shading)
          q.1).shadingDensity ∧
      0 < volume
        (stickyFiberSourceShading
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A))
          (selectedFineShading S A.refinement.indices A.refinement.shading)
          q.1).shadedUnion ∧
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (stickyFiberSourceShading
            (selectedFineScaleCover S A.refinement.indices
              (assembly_indices_subset_activeFine S Y r A))
            (selectedFineShading S A.refinement.indices A.refinement.shading)
            q.1).averageMultiplicity) := by
  classical
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  have hsourceP :
      (IndexedShadingRefinement.restrictTo Y
        (toConvexFactorization S).index.fine).shading.shadingMass ≠ 0 := by
    simpa only [toConvexFactorization_fine] using hsource
  have hrefinementMass : A.refinement.shading.shadingMass ≠ 0 :=
    refinement_shadingMass_ne_zero A hsourceP
  have hselectedMass : Z.shadingMass ≠ 0 := by
    rw [show Z.shadingMass = A.refinement.shading.shadingMass by
      simpa only [Z] using selectedFineShading_refinement_shadingMass S Y r A]
    exact hrefinementMass
  obtain ⟨q, hdensity, hsourceVolume⟩ :=
    exists_selectedFine_denseFiber S A.refinement.indices hselected
      A.refinement.shading hdelta hselectedMass
  let oldK : Fin S.coarseCard :=
    ((selectedFineParentValues S A.refinement.indices).equivFin.symm q.1).1
  have holdActive : oldK ∈ S.activeCoarse := by
    have hmem : oldK ∈ selectedFineParentValues S A.refinement.indices :=
      ((selectedFineParentValues S A.refinement.indices).equivFin.symm q.1).2
    obtain ⟨i, hiSelected, hiParent⟩ := Finset.mem_image.mp hmem
    rw [← hiParent]
    exact S.parent_mem i (hselected hiSelected)
  have holdP : oldK ∈ (toConvexFactorization S).index.coarse := by
    simpa only [toConvexFactorization_coarse] using holdActive
  obtain ⟨_anyK, _hanyActive, _hanyFiber, _hrefinementVolume,
      houterVolume⟩ := exists_positive_finalFiber A hsourceP
  have hsourceFinalUnion :=
    selectedFine_sourceShading_shadedUnion_eq_finalFiberShading
      S Y r A q.1
  have hfinalVolume : 0 < volume (finalFiberShading A oldK).shadedUnion := by
    rw [← hsourceFinalUnion]
    simpa only [T, Z, oldK, hselected] using hsourceVolume
  have hproduct := refinement_averageMultiplicity_le_four_mul_actualAverages
    A oldK holdP (ne_of_gt hfinalVolume) (ne_of_gt houterVolume)
  have havg :=
    selectedFine_sourceShading_averageMultiplicity_eq_finalFiberShading
      S Y r A q.1
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa only [T, Z, hselected] using hdensity
  · simpa only [T, Z, hselected] using hsourceVolume
  · rw [actualRefinementShading_averageMultiplicity]
    rw [havg]
    exact hproduct

#print axioms selectedFineShading_refinement_shadingMass
#print axioms exists_selectedFine_dense_sameAssemblyFiber_product

end
end Family8StickySelectedFineAssemblyDenseProductV1
