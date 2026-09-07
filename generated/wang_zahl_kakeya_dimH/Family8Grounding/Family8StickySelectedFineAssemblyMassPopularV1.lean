import Family8Grounding.Family8FrozenAssemblyMassPopularFiberV1
import Family8Grounding.Family8StickySelectedFineAssemblyFiberBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFineAssemblyMassPopularV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenAssemblyMassPopularFiberV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Mass-popular literal selected fibre on the same Sticky assembly

The mass-popular old parent has a genuinely nonempty final carrier.  Hence it
lies in the parent image of `A.refinement.indices` and has a literal selected
parent index.  Exact reindexing then turns the mass, union, average, and
assembly product into statements about the contracted-John source shading.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_selectedFine_massPopular_sameAssemblyFiber_product
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass ≤
          (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal) *
            (stickyFiberSourceShading
              (selectedFineScaleCover S A.refinement.indices
                (assembly_indices_subset_activeFine S Y r A))
              (selectedFineShading S A.refinement.indices A.refinement.shading)
              q.1).shadingMass ∧
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
  have hsourceP :
      (IndexedShadingRefinement.restrictTo Y
        (toConvexFactorization S).index.fine).shading.shadingMass ≠ 0 := by
    simpa only [toConvexFactorization_fine] using hsource
  obtain ⟨k, hk, hmass, hvolume, hproduct⟩ :=
    exists_massPopular_finalFiber_sameProduct A hsourceP
  have hsetNonempty : (finalFiberShading A k).shadedUnion.Nonempty := by
    by_contra hnot
    rw [Set.not_nonempty_iff_eq_empty.mp hnot, measure_empty] at hvolume
    exact lt_irrefl 0 hvolume
  obtain ⟨x, hx⟩ := hsetNonempty
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  change x ∈ (fiberShading (toConvexFactorization S)
    A.refinement.shading k).carrier i at hxi
  rw [fiberShading_carrier] at hxi
  have hiFactorFiber : i ∈ (toConvexFactorization S).index.fiber k := by
    by_contra hi
    rw [if_neg hi] at hxi
    exact hxi
  rw [if_pos hiFactorFiber] at hxi
  have hiSelected : i ∈ A.refinement.indices := by
    by_contra hi
    rw [A.refinement.carrier_eq_empty_of_not_mem i hi] at hxi
    exact hxi
  have hiOldFiber : i ∈ S.fiber k := by
    simpa only [toConvexFactorization_fiber] using hiFactorFiber
  have hkImage : k ∈ selectedFineParentValues S A.refinement.indices := by
    apply Finset.mem_image.mpr
    exact ⟨i, hiSelected, ((S.mem_fiber i k).1 hiOldFiber).2⟩
  let parent : SelectedFineParentIndex S A.refinement.indices := ⟨k, hkImage⟩
  let q₀ : Fin (selectedFineParentValues S A.refinement.indices).card :=
    (selectedFineParentValues S A.refinement.indices).equivFin parent
  have hqOld :
      ((selectedFineParentValues S A.refinement.indices).equivFin.symm q₀).1 =
        k := by
    exact congrArg Subtype.val
      ((selectedFineParentValues S A.refinement.indices).equivFin.symm_apply_apply
        parent)
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let q : {q // q ∈ T.activeCoarse} := ⟨q₀, by simp [T]⟩
  have hmassEq :=
    selectedFine_sourceShading_shadingMass_eq_finalFiberShading S Y r A q₀
  have hunionEq :=
    selectedFine_sourceShading_shadedUnion_eq_finalFiberShading S Y r A q₀
  have havgEq :=
    selectedFine_sourceShading_averageMultiplicity_eq_finalFiberShading
      S Y r A q₀
  rw [hqOld] at hmassEq hunionEq havgEq
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [hmassEq]
    simpa only [toConvexFactorization_coarse] using hmass
  · rw [hunionEq]
    exact hvolume
  · rw [havgEq]
    exact hproduct

#print axioms exists_selectedFine_massPopular_sameAssemblyFiber_product

end
end Family8StickySelectedFineAssemblyMassPopularV1
