import Family8Grounding.Family8StickySelectedFineRelativePowerFactorV1
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyBoundedSelectedFineRelativePowerFactorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineRelativePowerFactorV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Same-parent relative-power factor for the bounded partition assembly

This is the literal type used by the canonical Katz--Tao bounded assembly.
The bounded partition round trip is `rfl`, so the supplied assembly is not
rebuilt or replaced: its refinement and frozen-coarse shading are the exact
same fields consumed by the selected-fine endpoint.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_boundedAssembly_selectedFine_relativePower_factorized
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hscale : delta ≤ rho) (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ M)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hscale hcoarse M hM
        ).asConvexFactorization Y r)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hp : 0 < p) (ha : 0 < a)
    (hgap : 0 ≤ eta - (p + a))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 ≤ delta0)
    (hsmallRatio : delta / rho ≤
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : C ≤
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0)
    (hselectedDensityRatio :
      (((delta : ENNReal) / (rho : ENNReal)) ^ (eta - (p + a))) ≤
        (selectedFineShading S A.refinement.indices
          A.refinement.shading).shadingDensity / 93312 / 128)
    (hbaseRatio : ∀ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      (3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 * p + a))) ≤
        ((3 / 64 : ENNReal) ^ (-eta) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta))) *
          ((Fintype.card {i // i ∈
              (selectedFineScaleCover S A.refinement.indices
                (assembly_indices_subset_activeFine S Y r A)).fiber q.1} :
              ENNReal) *
            (((3 / 64 : ENNReal) ^ 2 *
                (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2))) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      ∃ selected : Finset {i // i ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).fiber q.1},
        selected.Nonempty ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (stickyFiberContractedJohnSourceClosedLoss C *
              frostmanMultiplicityRHS
                (contractedJohnProxyRadius delta rho / 8)
                (restrictActualTubeDatum
                  (eighthNormalizedDatum
                    (stickyFiberContractedJohnProxyDatum
                      (selectedFineScaleCover S A.refinement.indices
                        (assembly_indices_subset_activeFine S Y r A))
                      (selectedFineShading S A.refinement.indices
                        A.refinement.shading)
                      hrho hrhoOne q)) selected).actualFamilyVolume
                epsilon beta)) := by
  have hround :=
    boundedFiber_asConvexFactorization_eq_toConvexFactorization
      S hscale hcoarse M hM
  exact
    exists_selectedFine_sameAssembly_relativePower_factorized
      hF S Y r A hdelta hdeltaHalf hrho hrhoOne hdeltaRho hKT hp ha hgap
        hdelta0 hsmallRatio hCratio hsource hselectedDensityRatio hbaseRatio

#print axioms exists_boundedAssembly_selectedFine_relativePower_factorized

end
end Family8StickyBoundedSelectedFineRelativePowerFactorV1
