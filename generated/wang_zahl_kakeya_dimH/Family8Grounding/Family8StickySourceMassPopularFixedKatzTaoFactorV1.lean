import Family8Grounding.Family8StickyMassPopularFixedKatzTaoCoefficientV1
import Family8Grounding.Family8StickySourceMassFactorizationRoundTripV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySourceMassPopularFixedKatzTaoFactorV1

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
open Family8StickyMassPopularFixedKatzTaoCoefficientV1
open Family8StickySourceMassFactorizationRoundTripV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Fixed Katz--Tao factor on the literal source-mass assembly

The source-mass and bounded-fibre partitions have definitionally equal
Sticky factorizations.  Hence the sharp local fibre-cap cancellation can be
applied to the exact assembly returned by the source-to-tau product, without
reconstructing the assembly or changing its selected fine fibre.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_sourceMassAssembly_massPopular_relativePower_factorized_of_fixedKatzTaoEnvelope
    {beta epsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (hscale : delta <= rho)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0)
    {C : ENNReal}
    (hM : forall k, k ∈ S.activeCoarse ->
      (S.fiber k).card <=
        Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
          delta rho C)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
        Y r)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hKT : IsKatzTao C fine.bodyFamily)
    (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hp : 0 < p) (ha : 0 < a)
    (hgap : 0 <= eta - (p + a))
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 <= delta0)
    (hsmallRatio : delta / rho <=
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : C <=
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-p)))
    {lossBound XUpper : ENNReal}
    (hloss : (A.loss : ENNReal) <= lossBound)
    (hX : (activeCoarseCardScaleMass S : ENNReal) <= XUpper)
    (hdensityEnvelope :
      (lossBound *
          (8 * (XUpper *
            (Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberNatCapFixedConstant * C)))) *
        (((((delta : ENNReal) / (rho : ENNReal)) ^
            (eta - (p + a))) * 93312) * 128) <=
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass)
    (hbaseEnvelope :
      (lossBound *
          (8 * (XUpper *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2)))) *
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
    exists_boundedAssembly_massPopular_relativePower_factorized_of_fixedKatzTaoEnvelope
      hF S Y r hscale hcoarse hM A hdelta hdeltaHalf hrho hrhoOne hscale
        hKT hCone hCfinite hp ha hgap hdelta0 hsmallRatio hCratio hsource
        hloss hX hdensityEnvelope hbaseEnvelope

#print axioms
  exists_sourceMassAssembly_massPopular_relativePower_factorized_of_fixedKatzTaoEnvelope

end
end Family8StickySourceMassPopularFixedKatzTaoFactorV1
