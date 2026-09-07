import Family8Grounding.Family8StickySelectedFineDenseFiberV1
import Family8Grounding.Family8StickyFiberSubtypeAverageBridgeV1
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFineAssemblyFiberBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberSubtypeAverageBridgeV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineDenseFiberV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Exact selected-subtype / assembly-fibre bridge

For a frozen assembly over a Sticky factorization, the literal selected-fine
cover associated to the genuinely surviving indices has exactly the same
single-parent shaded mass, union, and average as the corresponding final
assembly fibre on the original index type.  Discarded original indices cause
no discrepancy because their final refinement carriers are definitionally
empty.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem assembly_indices_subset_activeFine
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r) :
    A.refinement.indices ⊆ S.activeFine := by
  simpa only [toConvexFactorization_fine] using A.indices_subset_fine

/-- Exact mass reindexing for a selected assembly parent. -/
theorem selectedFine_sourceShading_shadingMass_eq_finalFiberShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (q : Fin (selectedFineParentValues S A.refinement.indices).card) :
    (stickyFiberSourceShading
      (selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A))
      (selectedFineShading S A.refinement.indices A.refinement.shading)
      q).shadingMass =
      (finalFiberShading A
        ((selectedFineParentValues S A.refinement.indices).equivFin.symm q).1
        ).shadingMass := by
  classical
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let k :=
    ((selectedFineParentValues S A.refinement.indices).equivFin.symm q).1
  rw [stickyFiberSourceShading_shadingMass_eq_restrictTo,
    shadingMass_restrictTo_eq_sum,
    finalFiberShading, fiberShading_mass_eq_sum_fiber]
  change (∑ i ∈ T.fiber q, volume (Z.carrier i)) =
    ∑ i ∈ S.fiber k, volume (A.refinement.shading.carrier i)
  refine Finset.sum_bij_ne_zero
    (fun i _hi _hne => i.1) ?_ ?_ ?_ ?_
  · intro i hi _hne
    apply (S.mem_fiber i.1 k).2
    refine ⟨hselected i.2, ?_⟩
    exact (mem_selectedFineScaleCover_fiber_iff
      S A.refinement.indices hselected i q).1 hi
  · intro i₁ _hi₁ _hne₁ i₂ _hi₂ _hne₂ hij
    exact Subtype.ext hij
  · intro i hiFiber hiVolume
    have hiSelected : i ∈ A.refinement.indices := by
      by_contra hi
      rw [A.refinement.carrier_eq_empty_of_not_mem i hi, measure_empty]
        at hiVolume
      exact hiVolume rfl
    let ii : SelectedFineIndex A.refinement.indices := ⟨i, hiSelected⟩
    have hiiFiber : ii ∈ T.fiber q := by
      apply (mem_selectedFineScaleCover_fiber_iff
        S A.refinement.indices hselected ii q).2
      exact ((S.mem_fiber i k).1 hiFiber).2
    refine ⟨ii, hiiFiber, ?_, rfl⟩
    simpa only [Z, selectedFineShading_carrier] using hiVolume
  · intro i _hi _hne
    rfl

/-- Exact shaded-union reindexing for the same selected assembly parent. -/
theorem selectedFine_sourceShading_shadedUnion_eq_finalFiberShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (q : Fin (selectedFineParentValues S A.refinement.indices).card) :
    (stickyFiberSourceShading
      (selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A))
      (selectedFineShading S A.refinement.indices A.refinement.shading)
      q).shadedUnion =
      (finalFiberShading A
        ((selectedFineParentValues S A.refinement.indices).equivFin.symm q).1
        ).shadedUnion := by
  classical
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let k :=
    ((selectedFineParentValues S A.refinement.indices).equivFin.symm q).1
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hiFiber : i.1 ∈ T.fiber q := i.2
    have hiOldFiber : i.1.1 ∈ S.fiber k := by
      apply (S.mem_fiber i.1.1 k).2
      exact ⟨hselected i.1.2,
        (mem_selectedFineScaleCover_fiber_iff
          S A.refinement.indices hselected i.1 q).1 hiFiber⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i.1.1, ?_⟩
    change x ∈ (fiberShading (toConvexFactorization S)
      A.refinement.shading k).carrier i.1.1
    have hiFactorFiber : i.1.1 ∈
        (toConvexFactorization S).index.fiber k := by
      simpa only [toConvexFactorization_fiber] using hiOldFiber
    rw [fiberShading_carrier, if_pos hiFactorFiber]
    simpa only [Z, stickyFiberSourceShading_carrier,
      selectedFineShading_carrier] using hxi
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    change x ∈ (fiberShading (toConvexFactorization S)
      A.refinement.shading k).carrier i at hxi
    rw [fiberShading_carrier] at hxi
    split at hxi
    next hiFiber =>
      have hiSelected : i ∈ A.refinement.indices := by
        by_contra hi
        rw [A.refinement.carrier_eq_empty_of_not_mem i hi] at hxi
        exact hxi
      let ii : SelectedFineIndex A.refinement.indices := ⟨i, hiSelected⟩
      have hiOldFiber : i ∈ S.fiber k := by
        simpa only [toConvexFactorization_fiber] using hiFiber
      have hiiFiber : ii ∈ T.fiber q := by
        apply (mem_selectedFineScaleCover_fiber_iff
          S A.refinement.indices hselected ii q).2
        exact ((S.mem_fiber i k).1 hiOldFiber).2
      apply Set.mem_iUnion.mpr
      refine ⟨⟨ii, hiiFiber⟩, ?_⟩
      simpa only [Z, stickyFiberSourceShading_carrier,
        selectedFineShading_carrier] using hxi
    next hiNotFiber => exact hxi.elim

/-- The contracted-John source average on the literal selected fibre is the
actual final assembly-fibre average on the old index type. -/
theorem selectedFine_sourceShading_averageMultiplicity_eq_finalFiberShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (q : Fin (selectedFineParentValues S A.refinement.indices).card) :
    (stickyFiberSourceShading
      (selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A))
      (selectedFineShading S A.refinement.indices A.refinement.shading)
      q).averageMultiplicity =
      (finalFiberShading A
        ((selectedFineParentValues S A.refinement.indices).equivFin.symm q).1
        ).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [selectedFine_sourceShading_shadingMass_eq_finalFiberShading,
    selectedFine_sourceShading_shadedUnion_eq_finalFiberShading]

#print axioms assembly_indices_subset_activeFine
#print axioms selectedFine_sourceShading_shadingMass_eq_finalFiberShading
#print axioms selectedFine_sourceShading_shadedUnion_eq_finalFiberShading
#print axioms selectedFine_sourceShading_averageMultiplicity_eq_finalFiberShading

end
end Family8StickySelectedFineAssemblyFiberBridgeV1
