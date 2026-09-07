import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8Family7FirstCrossingGraphAverageIdentityV4
import Family8Grounding.Family8StickyGraphContractedJohnProxyDatumV2
import Family8Grounding.Family8ActualDatumBufferedCommonScalePlankConnectorV1
import Family8Grounding.Family8SquarePlankHRowSelectionFirstSetupV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ActualDatumBufferedCommonScalePlankConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7CoordinateToVerticalMassTransportV1
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingGraphAverageIdentityV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyGraphContractedJohnProxyDatumV2
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SquarePlankHRowSelectionFirstSetupV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

abbrev sameAssemblyGraph
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    Finset fineIndex :=
  verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    (firstCrossingFamilyVerticalSource R.axis F P R.k) R.label

abbrev sameAssemblyGraphProxyDatum
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hk : R.k ∈ T.activeCoarse) :
    ActualTubeDatum (contractedJohnProxyRadius tau rho)
      {i // i ∈ sameAssemblyGraph R} :=
  stickyGraphContractedJohnProxyDatum T (finalFiberShading R.A R.k)
    hrho hrhoOne ⟨R.k, hk⟩ (sameAssemblyGraph R)
      (Classical.choice R.graphCertificate).graph_subset

abbrev sameAssemblyGraphBufferedPlankDatum
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ T.activeCoarse) :=
  let Dproxy := sameAssemblyGraphProxyDatum R hrho hrhoOne hk
  let hpos := stickyFiberContractedJohnProxyDatum_delta_pos htau hrho
  let hhalf := stickyFiberContractedJohnProxyDatum_delta_le_half htauRho hrho
  have hcontained : ∀ i,
      (Dproxy.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
    simpa only [Dproxy, sameAssemblyGraphProxyDatum] using
      (stickyGraphContractedJohnProxyDatum_contained_in_unit_ball
        T (finalFiberShading R.A R.k) hrho hrhoOne htauRho
          ⟨R.k, hk⟩ (sameAssemblyGraph R)
            (Classical.choice R.graphCertificate).graph_subset)
  actualDatumBufferedCommonScalePlankFamily Dproxy hpos hhalf hcontained

theorem sameAssemblyGraphRestriction_shadingMass_ne_zero
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    (IndexedShadingRefinement.restrictTo
      (finalFiberShading R.A R.k) (sameAssemblyGraph R)).shading.shadingMass ≠ 0 := by
  let Z := (IndexedShadingRefinement.restrictTo
    (finalFiberShading R.A R.k) (sameAssemblyGraph R)).shading
  have hshading :
      firstCrossingFamilyGraphBucketShading R.axis R.label F P R.A R.k =
        coordinateToVerticalShading R.axis F Z := by
    simpa only [sameAssemblyGraph, Z] using
      firstCrossingFamilyGraphBucketShading_eq_coordinate_restrictTo
        R.axis R.label F P R.A R.k
  have hmass :
      (firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k).shadingMass = Z.shadingMass := by
    rw [hshading]
    exact coordinateToVerticalShading_shadingMass R.axis F Z
  intro hzero
  exact (Classical.choice R.graphCertificate).graph_mass_ne_zero
    (hmass.trans hzero)

theorem sameAssemblyGraphBufferedPlankDatum_shadingMass_ne_zero
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ T.activeCoarse) :
    (sameAssemblyGraphBufferedPlankDatum
      R htau hrho hrhoOne htauRho hk).shading.shadingMass ≠ 0 := by
  let proxy := sameAssemblyGraphProxyDatum R hrho hrhoOne hk
  have hproxy : proxy.shading.shadingMass ≠ 0 := by
    change (stickyGraphContractedJohnProxyShading T
      (finalFiberShading R.A R.k) hrho hrhoOne ⟨R.k, hk⟩
        (sameAssemblyGraph R)
          (Classical.choice R.graphCertificate).graph_subset).shadingMass ≠ 0
    rw [
      stickyGraphContractedJohnProxyShading_shadingMass,
      stickyGraphSourceDatum_shadingMass_eq_restrictTo]
    exact mul_ne_zero
      (affineJacobian_pos
        (stickyFiberContractedJohnAffineEquiv T hrho hrhoOne
          ⟨R.k, hk⟩)).ne'
      (sameAssemblyGraphRestriction_shadingMass_ne_zero R)
  change (affineImageShading
    (Family8ClosedBallFourBufferedCommonScaleUnitPlankV1.bufferedCommonScaleEquiv
      (contractedJohnProxyRadius tau rho)) proxy.shading).shadingMass ≠ 0
  rw [affineImageShading_shadingMass]
  exact mul_ne_zero
    (affineJacobian_pos
      (Family8ClosedBallFourBufferedCommonScaleUnitPlankV1.bufferedCommonScaleEquiv
        (contractedJohnProxyRadius tau rho))).ne' hproxy

theorem sameAssemblyGraphBufferedPlankDatum_averageMultiplicity_eq
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ T.activeCoarse) :
    (sameAssemblyGraphBufferedPlankDatum
      R htau hrho hrhoOne htauRho hk).shading.averageMultiplicity =
        R.graphAverage := by
  let Dproxy := sameAssemblyGraphProxyDatum R hrho hrhoOne hk
  have hbuffer :
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk).shading.averageMultiplicity =
        Dproxy.shading.averageMultiplicity := by
    simpa only [sameAssemblyGraphBufferedPlankDatum, Dproxy] using
      actualDatumBufferedCommonScalePlankFamily_averageMultiplicity
        Dproxy
          (stickyFiberContractedJohnProxyDatum_delta_pos htau hrho)
          (stickyFiberContractedJohnProxyDatum_delta_le_half htauRho hrho)
          (stickyGraphContractedJohnProxyDatum_contained_in_unit_ball
            T (finalFiberShading R.A R.k) hrho hrhoOne htauRho
              ⟨R.k, hk⟩ (sameAssemblyGraph R)
                (Classical.choice R.graphCertificate).graph_subset)
  have hproxy :
      Dproxy.shading.averageMultiplicity =
        (IndexedShadingRefinement.restrictTo
          (finalFiberShading R.A R.k)
            (sameAssemblyGraph R)).shading.averageMultiplicity := by
    change
      (stickyGraphContractedJohnProxyShading
        T (finalFiberShading R.A R.k) hrho hrhoOne ⟨R.k, hk⟩
          (sameAssemblyGraph R)
            (Classical.choice R.graphCertificate).graph_subset).averageMultiplicity = _
    exact stickyGraphContractedJohnProxyShading_averageMultiplicity
        T (finalFiberShading R.A R.k) hrho hrhoOne ⟨R.k, hk⟩
          (sameAssemblyGraph R)
            (Classical.choice R.graphCertificate).graph_subset
  have hgraph :
      R.graphAverage =
        (IndexedShadingRefinement.restrictTo
          (finalFiberShading R.A R.k)
            (sameAssemblyGraph R)).shading.averageMultiplicity := by
    simpa only [SameAssemblyFullCoefficientGraphIdentity.graphAverage,
      sameAssemblyGraph] using
      firstCrossingFamilyGraphBucketShading_averageMultiplicity_eq_restrictTo
        R.axis R.label F P R.A R.k
  exact hbuffer.trans (hproxy.trans hgraph.symm)

theorem exists_sameAssemblyGraphHRowSelectionFirstSetup
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ T.activeCoarse) :
    Nonempty (SquarePlankHRowSelectionFirstSetup
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)) := by
  letI : Nonempty {i // i ∈ sameAssemblyGraph R} :=
    Finset.nonempty_coe_sort.mpr
      (Classical.choice R.graphCertificate).graph_nonempty
  apply exists_squarePlankHRowSelectionFirstSetup
  · exact Family8BufferedCommonScaleTubePlankV1.bufferedCommonWidth_pos
      (stickyFiberContractedJohnProxyDatum_delta_pos htau hrho)
  · exact sameAssemblyGraphBufferedPlankDatum_shadingMass_ne_zero
      R htau hrho hrhoOne htauRho hk

theorem graphAverage_le_setupLoss_mul_sameHRowAverage
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ T.activeCoarse)
    (H : SquarePlankHRowSelectionFirstSetup
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk))
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilon beta eta) :
    R.graphAverage ≤ H.loss *
      (HRowFreshPlankDatum
        (sameAssemblyGraphBufferedPlankDatum
          R htau hrho hrhoOne htauRho hk)
        H.C H.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
          B.tau B.S).shading.averageMultiplicity := by
  rw [← sameAssemblyGraphBufferedPlankDatum_averageMultiplicity_eq
    R htau hrho hrhoOne htauRho hk]
  exact H.sourceAverage_le_loss_mul_hRowAverage B

#print axioms sameAssemblyGraphRestriction_shadingMass_ne_zero
#print axioms sameAssemblyGraphBufferedPlankDatum_shadingMass_ne_zero
#print axioms sameAssemblyGraphBufferedPlankDatum_averageMultiplicity_eq
#print axioms exists_sameAssemblyGraphHRowSelectionFirstSetup
#print axioms graphAverage_le_setupLoss_mul_sameHRowAverage

end
end Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
