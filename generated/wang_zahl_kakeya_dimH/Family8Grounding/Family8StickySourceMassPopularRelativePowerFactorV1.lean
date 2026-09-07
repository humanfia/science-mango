import Family8Grounding.Family8StickyBoundedMassPopularRelativePowerFactorV1
import Family8Grounding.Family8StickySourceMassFactorizationRoundTripV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySourceMassPopularRelativePowerFactorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Mass-popular relative-power factor on the source-mass assembly

The bounded-fibre and source-mass partitions have the same literal Sticky
factorization.  This specialization keeps the exact source-mass assembly
returned by the canonical product and applies the existing mass-popular
contracted-John argument on that object.  The only remaining inputs are its
two division-free scalar envelopes.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_sourceMassAssembly_massPopular_relativePower_factorized
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (hscale : delta <= rho)
    (Y : Shading fine.bodyFamily) (r : Real)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0)
    (M : Nat)
    (hM : forall k, k ∈ S.activeCoarse -> (S.fiber k).card <= M)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
        Y r)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    {C : ENNReal} (hKT : IsKatzTao C fine.bodyFamily)
    (hp : 0 < p) (ha : 0 < a)
    (hgap : 0 <= eta - (p + a))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hsmallRatio : delta / rho <=
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : C <=
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    (hdensityScalar :
      (((A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
          ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) *
        (((((delta : ENNReal) / (rho : ENNReal)) ^
            (eta - (p + a))) * 93312) * 128) <=
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)
    (hbaseScalar :
      (((A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2)) *
        ((3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 * p + a)))) <=
      (((3 / 64 : ENNReal) ^ (-eta) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-eta)) *
        (((3 / 64 : ENNReal) ^ 2 *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) / 2)) *
        (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)) :
    exists q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      exists selected : Finset {i // i ∈
          (selectedFineScaleCover S A.refinement.indices
            (assembly_indices_subset_activeFine S Y r A)).fiber q.1},
        selected.Nonempty /\
        (actualRefinementShading A).averageMultiplicity <=
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
  have hcoarse : S.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero S Y hsource
  exact
    Family8StickyBoundedMassPopularRelativePowerFactorV1.exists_boundedAssembly_massPopular_relativePower_factorized
      hF S Y r hscale hcoarse M hM A hdelta hdeltaHalf hrho hrhoOne
        hdeltaRho hKT hp ha hgap hdelta0 hsmallRatio hCratio hsource
        hdensityScalar hbaseScalar

#print axioms exists_sourceMassAssembly_massPopular_relativePower_factorized

end
end Family8StickySourceMassPopularRelativePowerFactorV1
