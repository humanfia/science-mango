import Family8Grounding.Family8ActiveFrozenComparableLogLossAbsorptionV4
import Family8Grounding.Family8CanonicalEndpointBaseThresholdV1
import Family8Grounding.Family8EndpointIdentityDirectNoKTMiddleLossAutomaticV1
import Family8Grounding.Family8EndpointIdentityRecomputedThirdGammaAdapterV1
import Family8Grounding.Family8EndpointLongCoreIdentityIntervalCountsV3
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
import Family8Grounding.Family8EndpointSelectedFineSameAssemblyDSOConnectorV3
import Family8Grounding.Family8EndpointSelectedFineSingletonDirectLongMiddleV2
import Family8Grounding.Family8FirstCrossingRecomputedThirdFullLossPowerV1
import Family8Grounding.Family8HighGammaParameterLadderV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
import Family8Grounding.Family8SelectedFineFiberCardCapTransportV2
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Family8Grounding.Family8StickySelectedFineAssemblyMassPopularV1
import Mathlib.Tactic
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointIdentityParameterLadderProducerV2
import Family8Grounding.Family8ParameterOutputEtaLongCoreOnlyMainLemmaV1

/-!
# The canonical high-gamma ladder at the arbitrary-parameter LongCore endpoint

This file makes the parameter choice which cannot be obtained by rewriting the
old canonical endpoint ladder.  For `2 / 3 < gamma` it chooses
`canonicalHighGammaCertificate ...`, exposes its underlying `.ladder` at the
existential arbitrary-parameter endpoint, and invokes the direct high-gamma
LongCore DSO theorem on that very ladder.

The two remaining scalar inequalities are named below rather than hidden in a
geometric callback.  The residual input package also keeps the genuinely
non-scale `thirdBudget` explicit.  In particular, its term
`targetEpsilon / 4` cannot be made small by decreasing `delta`; the public
LongCore-only wrapper quantifies over every positive `targetEpsilon`.

Thus the final theorem below is an exact connector into
`mainLemmaOne_of_parameter_outputEta_longCoreOnlyDSO`, not a claim that the
high-gamma branch (or all of Family 8) is already closed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaParameterLongCoreConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8CanonicalEndpointBaseThresholdV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityParameterLadderProducerV2
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FirstCrossingRecomputedThirdFixedLossPowerV3
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8HighGammaParameterLadderV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParameterOutputEtaLongCoreOnlyMainLemmaV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SectionEightOutputEtaV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberPartitionFineIndexV3
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The still-open assembly-density inequality in the high-gamma DSO.  This
is the former G1 scalar gate, stated on the exact assembly selected by that
DSO. -/
def endpointIdentityHighGammaDensityGate
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      H.ladder.N H.ladder.epsilon H.ladder.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (sourceEta : Real)
    (hepsilonHalf : H.ladder.epsilon <= 1 / 2)
    (hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta H.ladder sourceEta)) : Prop :=
  let P := H.ladder
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  let hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    have hmass : D.shading.shadingMass ≠ 0 := by
      have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
        D hD hFOutput
      exact ne_of_gt ((ENNReal.rpow_pos
        (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top).trans_le hfloor)
    have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
      rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
        D hD P W hepsilonHalf]
      exact hmass
    rw [shadingMass_restrictTo_eq_sum]
    exact hOn
  let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf k
  let hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
    hcoarse 1 hM
  let CKT := identitySourceFrostmanKatzTaoConstant D rho
    (sectionEightOutputEta P sourceEta)
  let conflictThreshold :=
    Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
  forall A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y 1,
    A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U.coarseCard) ->
    A.frozenCoarse =
        Pcoarse.asConvexFactorization.inducedShading
          A.refinement.shading ->
    (((rho / 8 : NNReal) : ENNReal) ^ sourceEta *
        (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
      Y.shadingDensity ^ 2 /
        ((A.loss : ENNReal) *
          (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2)))

/-- The still-open base/card-scale inequality in the high-gamma DSO.  This
is the former G2 scalar gate. -/
def endpointIdentityHighGammaBaseGate
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      H.ladder.N H.ladder.epsilon H.ladder.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (sourceEta : Real) : Prop :=
  let P := H.ladder
  let rho := canonicalBufferedRadius W
  let CKT := identitySourceFrostmanKatzTaoConstant D rho
    (sectionEightOutputEta P sourceEta)
  let conflictThreshold :=
    Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
  (((conflictThreshold + 1 : Nat) : ENNReal) * 2097152 *
      (delta : ENNReal) ^
        (-(sectionEightOutputEta P sourceEta)) <=
    ((rho / 8 : NNReal) : ENNReal) ^ (-sourceEta))

end
end Family8EndpointIdentityHighGammaParameterLongCoreConnectorV1
