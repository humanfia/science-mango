import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8Family7FirstCrossingFullCoefficientEighthInputsV13
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1
import Family8Grounding.Family8FullCoefficientEighthNormalizedSameObjectMiddleV6
import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

/-!
# Direct same-object middle estimate from a canonical graph identity

The exact-outer structural bundle contains two logically separate pieces:
the raw source triple and the data needed by the strict-middle theorem.  A
canonical graph identity already has its raw Equation-(66) triple supplied
by the caller.  Consequently it does not need the structural bundle's
`exact_outer` field in order to estimate its literal graph average.

This file constructs the proxy selection directly from the graph certificate
stored by one `SameAssemblyFullCoefficientGraphIdentity`.  No graph, parent,
or frozen assembly is reselected.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenDirectSameObjectMiddleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8ActualRestrictedMassWeightedCriticalBallShadingV4
open Family8ArbitraryFixedRelativeScaleActualVolumeEnvelopeV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8EighthNormalizedActiveKatzTaoFrostmanV4
open Family8EighthNormalizedWZL3SourceV3
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientEighthInputsV13
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8FullCoefficientActualMassProxyAverageV10
open Family8FullCoefficientActualMassProxyDatumV11
open Family8FullCoefficientActualMassProxyGreedyFrostmanV11
open Family8FullCoefficientCriticalScaleEighthRelativeFixedV3
open Family8FullCoefficientEighthNormalizedSameObjectMiddleV6
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- Fix the certificate already stored in `R`.  This chooses only a proof
object; all geometric objects in the certificate are definitionally those
of `R`. -/
theorem selectedCertificate
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    let baseLoss : ENNReal :=
      (R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
    let d : ENNReal :=
      (sourceActiveFineShading P Y).shadingDensity / baseLoss
    let graphLoss : ENNReal :=
      ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal)
    let effectiveCF : ENNReal := fibreCF * (d⁻¹ * graphLoss)
    FirstCrossingFullCoefficientGraphCertificate
      F T P Y R.A R.k R.axis R.label effectiveCF d graphLoss :=
  Classical.choice R.graphCertificate

/-- The literal coefficient multiplying the graph average in
`R.collapsedPrefix`. -/
def directMiddleOuterLoss
    {tau rho delta : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (firstCap : ENNReal) (lossEta : Real) : ENNReal :=
  (firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) * R.graphLoss

/-- The proxy-side choices made directly on the graph stored in `R`. -/
structure SameGraphDirectProxySelection
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) (fibreCF : ENNReal)
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau8 : 0 < tau / 8)
    (htenTau8Sixteen : 10 * (((tau / 8 : NNReal) : Real)) ≤ 16) where
  haxis :
    let cert := selectedCertificate R
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS R.label
    let S8 := eighthNormalizedWZL3Source VS
    let Y8 := eighthNormalizedShading VS.family VY
    let W := fullCoefficientActualMassNormData
      S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
    ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S8 W)
        (S8.family.tubes i.1)‖ ≤ 1
  htransverse :
    let cert := selectedCertificate R
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS R.label
    let S8 := eighthNormalizedWZL3Source VS
    let Y8 := eighthNormalizedShading VS.family VY
    let W := fullCoefficientActualMassNormData
      S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
    affineLinearOperatorNorm
        (weightedCanonicalCriticalScaleAffineEquiv S8 W) *
          ((tau / 8 : NNReal) : Real) ≤
      (criticalScaleProxyRadius (tau / 8) W.criticalScale
        (weightedCanonicalCriticalScale_pos W) : Real)
  output :
    let cert := selectedCertificate R
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS R.label
    let S8 := eighthNormalizedWZL3Source VS
    let Y8 := eighthNormalizedShading VS.family VY
    let W := fullCoefficientActualMassNormData
      S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
    let Dproxy := fullCoefficientActualMassProxyDatum
      S8 Y8 graph cert.graph_nonempty htau8 htenTau8Sixteen
        Set.univ MeasurableSet.univ haxis htransverse
    FullCoefficientActualMassProxyGreedyOutput
      Dproxy (W.family.card + 1)

/-- Construct the direct proxy selection without an exact-outer equality. -/
theorem nonempty_sameGraphDirectProxySelection
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) (fibreCF : ENNReal)
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (htau8 : 0 < tau / 8)
    (htenTau8Sixteen : 10 * (((tau / 8 : NNReal) : Real)) ≤ 16) :
    Nonempty (SameGraphDirectProxySelection
      F T P Y fibreCF R htau8 htenTau8Sixteen) := by
  let cert := selectedCertificate R
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
  let graph := verticalSourceGraphCBucketFiber
    ((tau : Real) / 2) VS R.label
  let S8 := eighthNormalizedWZL3Source VS
  let Y8 := eighthNormalizedShading VS.family VY
  obtain ⟨hsource, hsupport, _hFsource, _haverage⟩ :=
    firstCrossingGraph_fullCoefficientEighth_inputs
      R.axis R.label F P R.A R.k htau htauHalf cert.graph_nonempty
        cert.vertical_b2 cert.graph_katz_tao
  obtain ⟨haxis, htransverse, houtput⟩ :=
    exists_fullCoefficientActualMassProxyGreedyOutput
      S8 Y8 graph cert.graph_nonempty htau8 htenTau8Sixteen
        Set.univ MeasurableSet.univ hsource hsupport
  let W := fullCoefficientActualMassNormData
    S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
  let Dproxy := fullCoefficientActualMassProxyDatum
    S8 Y8 graph cert.graph_nonempty htau8 htenTau8Sixteen
      Set.univ MeasurableSet.univ haxis htransverse
  let O : FullCoefficientActualMassProxyGreedyOutput
      Dproxy (W.family.card + 1) := Classical.choice houtput
  refine ⟨{
    haxis := ?_
    htransverse := ?_
    output := ?_
  }⟩
  · simpa only [cert, VS, VY, graph, S8, Y8, W] using haxis
  · simpa only [cert, VS, VY, graph, S8, Y8, W] using htransverse
  · simpa only [cert, VS, VY, graph, S8, Y8, W, Dproxy, O] using O

/-- The strict middle estimate for the literal `collapsedPrefix` of `R`.
All non-scalar geometric inputs are recovered from `R.graphCertificate`.
In particular, no `exact_outer` premise is present. -/
theorem SameGraphDirectProxySelection.gainedMiddle
    {tau rho globalDelta delta0 delta : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) (fibreCF : ENNReal)
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (firstCap : ENNReal) (lossEta : Real)
    (htau8 : 0 < tau / 8)
    (htau8Half : tau / 8 ≤ (2 : NNReal)⁻¹)
    (htenTau8Sixteen : 10 * (((tau / 8 : NNReal) : Real)) ≤ 16)
    (O : SameGraphDirectProxySelection
      F T P Y fibreCF R htau8 htenTau8Sixteen)
    {frostmanBeta frostmanEpsilon frostmanEta gamma lossExp kappa
      globalEta : Real}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (hdensityBudget :
      let cert := selectedCertificate R
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
      let graph := verticalSourceGraphCBucketFiber
        ((tau : Real) / 2) VS R.label
      let S8 := eighthNormalizedWZL3Source VS
      let Y8 := eighthNormalizedShading VS.family VY
      let W := fullCoefficientActualMassNormData
        S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
      let Dproxy := fullCoefficientActualMassProxyDatum
        S8 Y8 graph cert.graph_nonempty htau8 htenTau8Sixteen
          Set.univ MeasurableSet.univ O.haxis O.htransverse
      (criticalScaleProxyRadius (tau / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ frostmanEta ≤
        Dproxy.shading.shadingDensity / (W.family.card + 1 : Nat))
    (hconstantBudget :
      let cert := selectedCertificate R
      let baseLoss : ENNReal :=
        (R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
      let d : ENNReal :=
        (sourceActiveFineShading P Y).shadingDensity / baseLoss
      let graphLoss : ENNReal :=
        ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal)
      let effectiveCF : ENNReal := fibreCF * (d⁻¹ * graphLoss)
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
      let graph := verticalSourceGraphCBucketFiber
        ((tau : Real) / 2) VS R.label
      let Dvertical := firstCrossingVerticalGraphSourceDatum R.axis F P R.A R.k
      let S8 := eighthNormalizedWZL3Source VS
      let Y8 := eighthNormalizedShading VS.family VY
      let C8 := eighthNormalizedActiveKatzTaoFrostmanConstant
        (fullCoefficientGraphKatzTaoConstant
          R.axis R.label F T P R.k effectiveCF) Dvertical graph
      let W := fullCoefficientActualMassNormData
        S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
      fullCoefficientActualMassProxyFrostmanLoss
          S8 Y8 graph cert.graph_nonempty htau8 htenTau8Sixteen Set.univ C8 *
          (16 * (W.family.card + 1 : Nat)) ≤
        (criticalScaleProxyRadius (tau / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^
            (-frostmanEta))
    (hdelta0 :
      let cert := selectedCertificate R
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
      let graph := verticalSourceGraphCBucketFiber
        ((tau : Real) / 2) VS R.label
      let S8 := eighthNormalizedWZL3Source VS
      let Y8 := eighthNormalizedShading VS.family VY
      let W := fullCoefficientActualMassNormData
        S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
      criticalScaleProxyRadius (tau / 8) W.criticalScale
        (weightedCanonicalCriticalScale_pos W) ≤ delta0)
    (htau : 0 < tau) (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho)
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta)
    {K : ENNReal}
    (hlossPower :
      let cert := selectedCertificate R
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
      let graph := verticalSourceGraphCBucketFiber
        ((tau : Real) / 2) VS R.label
      let S8 := eighthNormalizedWZL3Source VS
      let Y8 := eighthNormalizedShading VS.family VY
      let W := fullCoefficientActualMassNormData
        S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
      (W.family.card + 1 : Nat) ≤
        (criticalScaleProxyRadius (tau / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ (-lossExp))
    (hcount : (O.output.selected.card : ENNReal) ≤
        K * (((tau : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))))
    (habsorb :
      let cert := selectedCertificate R
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
      let graph := verticalSourceGraphCBucketFiber
        ((tau : Real) / 2) VS R.label
      let S8 := eighthNormalizedWZL3Source VS
      let Y8 := eighthNormalizedShading VS.family VY
      let W := fullCoefficientActualMassNormData
        S8 graph cert.graph_nonempty htau8 htenTau8Sixteen Y8 Set.univ
      directMiddleOuterLoss (delta := delta) R firstCap lossEta *
          (arbitraryFixedMiddleActualCoefficient
              (fullCoefficientEighthRelativeFixed rho W) K
              frostmanEpsilon frostmanBeta gamma lossExp *
            (((tau : ENNReal) / (rho : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma lossExp kappa)) ≤
        (globalDelta : ENNReal) ^ (10 * globalEta)) :
    R.collapsedPrefix (delta := delta) firstCap lossEta ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          tau rho O.output.selected.card gamma := by
  let cert := selectedCertificate R
  let baseLoss : ENNReal :=
    (R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  let d : ENNReal :=
    (sourceActiveFineShading P Y).shadingDensity / baseLoss
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal)
  let effectiveCF : ENNReal := fibreCF * (d⁻¹ * graphLoss)
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let VY := firstCrossingFamilyVerticalShading R.axis F P R.A R.k
  let graph := verticalSourceGraphCBucketFiber
    ((tau : Real) / 2) VS R.label
  let Dvertical := firstCrossingVerticalGraphSourceDatum R.axis F P R.A R.k
  let S8 := eighthNormalizedWZL3Source VS
  let Y8 := eighthNormalizedShading VS.family VY
  let C8 := eighthNormalizedActiveKatzTaoFrostmanConstant
    (fullCoefficientGraphKatzTaoConstant
      R.axis R.label F T P R.k effectiveCF) Dvertical graph
  obtain ⟨hsource, hsupport, hFsource, haverage⟩ :=
    firstCrossingGraph_fullCoefficientEighth_inputs
      R.axis R.label F P R.A R.k htau htauHalf
        cert.graph_nonempty cert.vertical_b2 cert.graph_katz_tao
  have hraw :=
    outerLoss_mul_sameObjectAverage_le_strictMiddle
      S8 Y8 graph cert.graph_nonempty R.graphAverage haverage
      htau8 htau8Half htenTau8Sixteen hsource hsupport hFsource
      O.haxis O.htransverse O.output hF
      hdensityBudget hconstantBudget hdelta0
      htau hrho hbetaTwo hgammaTwo hgap
      (outerLoss := directMiddleOuterLoss (delta := delta) R firstCap lossEta)
      hlossPower hcount habsorb
  simpa only [SameAssemblyFullCoefficientGraphIdentity.collapsedPrefix,
    SameAssemblyFullCoefficientGraphIdentity.graphAverage,
    directMiddleOuterLoss, cert, baseLoss, d, graphLoss, effectiveCF,
    VS, VY, graph, Dvertical, S8, Y8, C8] using hraw

#print axioms selectedCertificate
#print axioms directMiddleOuterLoss
#print axioms SameGraphDirectProxySelection
#print axioms nonempty_sameGraphDirectProxySelection
#print axioms SameGraphDirectProxySelection.gainedMiddle

end
end Family8CanonicalGraphFrozenDirectSameObjectMiddleV1
