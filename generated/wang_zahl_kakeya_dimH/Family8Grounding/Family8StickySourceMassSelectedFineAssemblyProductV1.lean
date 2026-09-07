import Family8Grounding.Family8StickySelectedFineAssemblyMassPopularV1
import Family8Grounding.Family8StickySourceMassFactorizationRoundTripV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySourceMassSelectedFineAssemblyProductV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySourceMassFactorizationRoundTripV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover

noncomputable section

/-!
# The literal source-mass assembly product on a selected fine fibre

This specializes the existing mass-popular selected-fibre theorem to the
exact factorization type produced by `sourceMassCoarseTubePartition`.  The
round-trip is definitional, so the assembly, refinement, and selected parent
are transported without reconstruction or loss.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_sourceMass_selectedFine_massPopular_sameAssemblyFiber_product
    (S : StickyScaleCover fine rho) (hscale : delta <= rho)
    (Y : Shading fine.bodyFamily) (r : Real)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
        Y r) :
    exists q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      (sourceActiveFineShading
          (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
          Y).shadingMass <=
          (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal) *
            (stickyFiberSourceShading
              (selectedFineScaleCover S A.refinement.indices
                (assembly_indices_subset_activeFine S Y r A))
              (selectedFineShading S A.refinement.indices A.refinement.shading)
              q.1).shadingMass /\
      0 < volume
        (stickyFiberSourceShading
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A))
          (selectedFineShading S A.refinement.indices A.refinement.shading)
          q.1).shadedUnion /\
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          (stickyFiberSourceShading
            (selectedFineScaleCover S A.refinement.indices
              (assembly_indices_subset_activeFine S Y r A))
            (selectedFineShading S A.refinement.indices A.refinement.shading)
            q.1).averageMultiplicity) := by
  have hfactor :=
    sourceMass_asConvexFactorization_eq_toConvexFactorization
      S hscale Y hsource
  have hmassEq := congrArg
    (fun Q => (sourceActiveFineShading Q Y).shadingMass) hfactor
  obtain ⟨q, hmass, hvolume, hproduct⟩ :=
    Family8StickySelectedFineAssemblyMassPopularV1.exists_selectedFine_massPopular_sameAssemblyFiber_product
      S Y r A hsource
  refine ⟨q, ?_, hvolume, hproduct⟩
  calc
    (sourceActiveFineShading
        (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
        Y).shadingMass =
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass := hmassEq
    _ <= _ := hmass

#print axioms
  exists_sourceMass_selectedFine_massPopular_sameAssemblyFiber_product

end
end Family8StickySourceMassSelectedFineAssemblyProductV1
