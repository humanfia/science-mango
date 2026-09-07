import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8ParentInjectiveAggregatedAverageIdentityV2
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import Mathlib.Tactic

/-!
# Exact source mass on the endpoint tau-active cover

For the literal identity coherent cover, the source-to-`tau` parent map is
the finite enumeration equivalence.  Parent aggregation is therefore
injective and preserves shading mass exactly.  The subsequent active-fine
reindexings are both literal universes, so the same source mass is exactly
the `shadingMassOn` consumed by the low-CF selector.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointLongCoreTauActiveSourceMassIdentityV1

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParentInjectiveAggregatedAverageIdentityV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- On the endpoint identity cover, the tau-parent aggregation has exactly
the original source shading mass. -/
theorem endpointLongCore_tauActive_shadingMass_eq_source
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))) :
    (tauActiveCoarseDatum (fullRefinementDatum D)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) W).shading.shadingMass =
      D.shading.shadingMass := by
  let E := fullRefinementDatum D
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let C := identityRadiusCoherentCover E.family
  let S0 := sourceTauCover E C S W.m
  have hcover : S0 = tauScaleCover E C S W := rfl
  have hinjective : Set.InjOn S0.parent (S0.activeFine : Set _) := by
    intro i _hi j _hj hij
    change Fintype.equivFin _ i = Fintype.equivFin _ j at hij
    exact (Fintype.equivFin _).injective hij
  have hactive : S0.activeFine = Finset.univ := by
    rw [S0.activeFine_eq_refined, fullRefinementDatum_refined]
  change (parentAggregatedShading (tauScaleCover E C S W)
    E.shading).shadingMass = D.shading.shadingMass
  rw [← hcover]
  calc
    (parentAggregatedShading S0 E.shading).shadingMass =
        (activeFineShading S0 E.shading).shadingMass :=
      parentAggregatedShading_shadingMass_eq_activeFineShading
        S0 E.shading hinjective
    _ = E.shading.shadingMass :=
      activeFineShading_shadingMass_eq_of_activeFine_eq_univ
        S0 E.shading hactive
    _ = D.shading.shadingMass := fullRefinementDatum_shadingMass D

/-- The literal active-restricted `tau -> b` source mass is exactly the
original datum mass.  No fibre cap or quantitative hypothesis is used. -/
theorem endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon ≤ 1 / 2) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    shadingMassOn Y U.activeFine = D.shading.shadingMass := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hU0 : U0.activeFine = Finset.univ :=
    canonicalBufferedTauActiveCover_activeFine
      E hE C S W P.epsilon_pos.le hepsilonHalf
  have hU : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine U0
  have hselectedMass : shadingMassOn Y U.activeFine = Y.shadingMass := by
    calc
      shadingMassOn Y U.activeFine =
          (IndexedShadingRefinement.restrictTo Y
            U.activeFine).shading.shadingMass := by
        rw [shadingMass_restrictTo_eq_sum]
        rfl
      _ = (activeFineShading U Y).shadingMass :=
        (activeFineShading_shadingMass_eq_restrictTo U Y).symm
      _ = Y.shadingMass :=
        activeFineShading_shadingMass_eq_of_activeFine_eq_univ U Y hU
  have hrestrictedMass : Y.shadingMass = Dtau.shading.shadingMass := by
    calc
      Y.shadingMass = (activeFineShading U0 Dtau.shading).shadingMass :=
        activeFineRestrictedShading_shadingMass U0 Dtau.shading
      _ = Dtau.shading.shadingMass :=
        activeFineShading_shadingMass_eq_of_activeFine_eq_univ
          U0 Dtau.shading hU0
  calc
    shadingMassOn Y U.activeFine = Y.shadingMass := hselectedMass
    _ = Dtau.shading.shadingMass := hrestrictedMass
    _ = D.shading.shadingMass :=
      endpointLongCore_tauActive_shadingMass_eq_source D hD P W

#print axioms endpointLongCore_tauActive_shadingMass_eq_source
#print axioms
  endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source

end

end Family8EndpointLongCoreTauActiveSourceMassIdentityV1
