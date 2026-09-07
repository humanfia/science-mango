import Family8Grounding.Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenV1
import Mathlib.Tactic

/-!
# Canonical graph/frozen identity bridge for the raw Equation (66) product

The canonical graph producer chooses the frozen assembly before the HRow
consumer is instantiated.  This file packages only that choice and the graph
which lives on it.  In particular, the raw Equation-(66) inequality is a
conclusion of the producer below, not a field of the identity record and not
an input which a downstream caller may provide.

The Frostman coefficient in the graph certificate is the coefficient on the
canonical tau-active fibres.  It is intentionally independent of the
augmented row coefficient used later by the HRow Prop. 6.6 argument.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-- The minimum identity data shared by the graph producer and the later HRow
consumer.  There is one literal frozen assembly and one literal graph on that
assembly.  No raw product estimate is stored here. -/
structure SameAssemblyFullCoefficientGraphIdentity
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) (fibreCF : ENNReal) where
  A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y 1
  k : Fin T.coarseCard
  axis : Fin 3
  label : Int
  graphCertificate :
    let baseLoss : ENNReal :=
      (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
    let d : ENNReal :=
      (sourceActiveFineShading P Y).shadingDensity / baseLoss
    let graphLoss : ENNReal :=
      ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal)
    let effectiveCF : ENNReal := fibreCF * (d⁻¹ * graphLoss)
    Nonempty
      (FirstCrossingFullCoefficientGraphCertificate
        F T P Y A k axis label effectiveCF d graphLoss)

/-- The literal graph loss attached to an identity record. -/
def SameAssemblyFullCoefficientGraphIdentity.graphLoss
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (_R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) : ENNReal :=
  ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal)

/-- The literal selected graph average attached to an identity record. -/
def SameAssemblyFullCoefficientGraphIdentity.graphAverage
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) : ENNReal :=
  (firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k).averageMultiplicity

/-- The uninflated collapsed prefix which actually occurs in the raw
Equation-(66) product. -/
def SameAssemblyFullCoefficientGraphIdentity.collapsedPrefix
    {tau rho delta : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (firstCap : ENNReal) (lossEta : Real)
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) : ENNReal :=
  ((firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) * R.graphLoss) *
    R.graphAverage

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Choose the canonical frozen assembly first and produce the sole raw
product inequality needed by the HRow/DSO consumer on that same assembly.

The graph certificate is retained only to identify the producer.  No
factor-one or inflated Equation-(66) theorem is used by this bridge.
-/
theorem exists_canonicalGraphFrozenIdentity_rawEq66
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W ≤
      (1 / 16 : NNReal))
    (fibreCF : ENNReal) (hCFfinite : fibreCF ≠ ∞)
    (hFibres :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let U := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      (activeFineRestrictedScaleCover U).IsFrostmanAtScale fibreCF)
    {etaF etaKT lossEta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hlossEta : 0 < lossEta)
    (hdeltaLoss : delta ≤
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let hscale : S.tau W.m ≤ canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let Y := (tauActiveCoarseDatum E C S W).shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤
            D.shading.shadingMass :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
        have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
            ENNReal.coe_ne_top
        exact ne_of_gt (hpositive.trans_le hfloor)
      exact
        canonicalBufferedTauActiveCover_restrictedMass_ne_zero
          E hE C S P W hepsilonHalf
            (Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
              D C S W.m hmass)
    let T := activeFineRestrictedScaleCover U
    let YR := activeFineRestrictedShading U Y
    let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
    let Psource := sourceMassCoarseTubePartition T hscale YR hsourceR
    ∃ R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U) T Psource.asConvexFactorization YR
          fibreCF,
      R.A.loss = frozenComparableLoss {i // i ∈ U.activeFine}
          (Fin U.activeCoarse.card) ∧
      D.shading.averageMultiplicity ≤
        R.collapsedPrefix (delta := delta)
            (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT)))
            lossEta *
          R.A.frozenCoarse.averageMultiplicity := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let hscale : S.tau W.m ≤ canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Y := (tauActiveCoarseDatum E C S W).shading
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤
        D.shading.shadingMass :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
    have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsourceTau :
      (IndexedShadingRefinement.restrictTo E.shading
        (tauScaleCover E C S W).activeFine).shading.shadingMass ≠ 0 :=
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
      D C S W.m hmass
  let hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE C S P W hepsilonHalf hsourceTau
  let T := activeFineRestrictedScaleCover U
  let YR := activeFineRestrictedShading U Y
  let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
  let Psource := sourceMassCoarseTubePartition T hscale YR hsourceR
  obtain ⟨A, hLoss, k, axis, label, hQ, hRaw⟩ :=
    exists_fullRefinement_normalizedLongCore_canonicalRawEq66GraphFrozen
      D hD C S P W hepsilonHalf hbufferedSixteenth fibreCF hCFfinite
        hFibres hFsource hKTsource hlossEta hdeltaLoss
  let R : SameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) T Psource.asConvexFactorization YR
        fibreCF :=
    { A := A
      k := k
      axis := axis
      label := label
      graphCertificate := hQ }
  refine ⟨R, hLoss, ?_⟩
  simpa only [SameAssemblyFullCoefficientGraphIdentity.collapsedPrefix,
    SameAssemblyFullCoefficientGraphIdentity.graphLoss,
    SameAssemblyFullCoefficientGraphIdentity.graphAverage, R, E, hE, U,
    hscale, Y, hsource, T, YR, hsourceR, Psource] using hRaw

#print axioms SameAssemblyFullCoefficientGraphIdentity
#print axioms exists_canonicalGraphFrozenIdentity_rawEq66

end
end Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
