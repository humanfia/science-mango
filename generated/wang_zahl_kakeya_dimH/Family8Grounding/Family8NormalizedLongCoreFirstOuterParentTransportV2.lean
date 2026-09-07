import Family8Grounding.Family8IdentifiedDividingWitnessFirstOuterParentTransportV1
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1

/-!
# Source-to-tau first-factor transport for a normalized long core, V2

The deterministic first-factor theorem reads only the selected interval index.
V1 omitted the source-to-tau shading namespace and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreFirstOuterParentTransportV2

open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The actual source average transports to the literal source-to-tau parent
shading with the genuine doubled-fibre Katz--Tao cap. -/
theorem NormalizedLongIntervalCoreWitness.fullRefinement_averageMultiplicity_le_firstCap_mul_sourceTauParent
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    {etaKT : Real} (hKT : KatzTaoHypotheses D etaKT) :
    D.shading.averageMultiplicity ≤
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
        (parentAggregatedShading
          (sourceTauCover (fullRefinementDatum D) C S W.m)
          (fullRefinementDatum D).shading).averageMultiplicity :=
  fullRefinement_averageMultiplicity_le_hypothesisCap_mul_sourceTauParent
    D hD C S W.m hKT

#print axioms
  NormalizedLongIntervalCoreWitness.fullRefinement_averageMultiplicity_le_firstCap_mul_sourceTauParent

end
end Family8NormalizedLongCoreFirstOuterParentTransportV2
