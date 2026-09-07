import Family8Grounding.Family8SelectedParentPlankCenteredMassFreshCanonicalThinCountV1
import Family8Grounding.Family8SelectedParentPlankCanonicalRadiusScaleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredMassFreshQuadraticScaleThinCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCanonicalRadiusScaleV1
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostFiveParameterPackingV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
open Family8SelectedParentPlankCenteredMassFreshCanonicalThinCountV1
open Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV6
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Same-selected centered endpoint from a quadratic scale separation

This wrapper removes the exact carrier-radius inequality from the endpoint
interface.  It is produced from the actual winning-block bucket and the
label-independent separation `648 * delta ≤ rho^2` proved sufficient in the
canonical radius-scale module.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_selectedParent_centeredHalfPost_massFresh_canonicalThinCount_of_quadraticScale
    {beta epsilon eta lossEta sourceEta coefficientEta
      densityAbsorbEta coefficientAbsorbEta : Real}
    {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (hdelta0Pos : 0 < delta0)
    (Y : Shading fine.bodyFamily)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hquadratic : 648 * delta ≤ rho ^ 2)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hglobalKT : IsKatzTao C fine.bodyFamily)
    (heta : 0 ≤ eta)
    (hlossPower :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let s := selectedPlankFineCanonicalProxyScale r label
      let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C
      let loss := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1
      (loss : ENNReal) ≤ (s : ENNReal) ^ (-lossEta))
    (hsourceDensity :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let s := selectedPlankFineCanonicalProxyScale r label
      let hscalarRadius :=
        selectedParent_centeredHalfPost_canonical_radius_scalar_of_quadratic_scale
          hfineContained S hrho hrhoOne P k r hr label hplank W hquadratic
      let hradius := selectedParent_centeredHalfPost_radius_budget
        S hrho P k r hr label B hplank W s hscalarRadius
      let D := centeredHalfPostSelectedPlankFineMassDatum
        s Y e S B hrho label hplank W hradius
      (s : ENNReal) ^ sourceEta ≤ D.shading.shadingDensity)
    (hCproxyPower :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let s := selectedPlankFineCanonicalProxyScale r label
      let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C
      Cproxy ≤ (s : ENNReal) ^ (-coefficientEta))
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hsmallFresh : selectedPlankFineCanonicalProxyScale r label ≤
      centeredMassFreshKatzTaoThreshold
        delta0 densityAbsorbEta coefficientAbsorbEta)
    (hdensityExponent :
      sourceEta + lossEta + densityAbsorbEta ≤ eta)
    (hcoefficientExponent :
      coefficientEta + coefficientAbsorbEta ≤ eta)
    (hsmallPacking : selectedPlankFineCanonicalProxyScale r label / 8 ≤
      (1 / 100 : NNReal))
    (hthin :
      (((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real)) ^ 2 ≤
        (3 : Real) / 4)) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let s := selectedPlankFineCanonicalProxyScale r label
    let R := selectedPlankFineCanonicalAspect label
    let hscalarRadius :=
      selectedParent_centeredHalfPost_canonical_radius_scalar_of_quadratic_scale
        hfineContained S hrho hrhoOne P k r hr label hplank W hquadratic
    let hradius := selectedParent_centeredHalfPost_radius_budget
      S hrho P k r hr label B hplank W s hscalarRadius
    let D := centeredHalfPostSelectedPlankFineMassDatum
      s Y e S B hrho label hplank W hradius
    let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e S B hrho label hplank W C
    let threshold := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal)
    let loss := threshold + 1
    ∃ selected : Finset (SelectedPlankFineIndex S W),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
        (loss : ENNReal) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass ≤
        (loss : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass ∧
      IsKatzTao (128 * Cproxy)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      KatzTaoHypotheses
        (restrictActualTubeDatum (eighthNormalizedDatum D) selected) eta ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).shading.averageMultiplicity ≤
          katzTaoMultiplicityRHS (s / 8) selected.card epsilon beta ∧
      (selectedPlankFineSourceShading
        Y e S B hrho label W).averageMultiplicity ≤
          (loss : ENNReal) *
            katzTaoMultiplicityRHS (s / 8) selected.card epsilon beta ∧
      selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  let hscalarRadius :=
    selectedParent_centeredHalfPost_canonical_radius_scalar_of_quadratic_scale
      hfineContained S hrho hrhoOne P k r hr label hplank W hquadratic
  exact exists_selectedParent_centeredHalfPost_massFresh_canonicalThinCount_of_power
    hKTP hdelta0Pos Y hfineContained S hrho hrhoOne P k r hr label hplank W
      hdeltaPos hdeltaHalf hscalarRadius hCfinite hglobalKT heta hlossPower
        hsourceDensity hCproxyPower hdensityAbsorbEta hcoefficientAbsorbEta
          hsmallFresh hdensityExponent hcoefficientExponent hsmallPacking hthin

#print axioms
  exists_selectedParent_centeredHalfPost_massFresh_canonicalThinCount_of_quadraticScale

end
end Family8SelectedParentPlankCenteredMassFreshQuadraticScaleThinCountV1
