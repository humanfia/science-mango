import Family8Grounding.Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV3

/-!
# Literal endpoint buffered input from the packaged side conditions, V4

The V3 structure keeps all proof-dependent choices stable.  This successor
feeds its four projections into the existing same-object canonical Eq.
(45/46) input, so downstream numerical code consumes one literal object.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV3
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareCanonicalBufferedInputV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Feed the stable endpoint side-condition package into the exact canonical
buffered input. -/
noncomputable def EndpointFullRefinementShadingAwareBufferedInputData.toCanonicalBufferedInput
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {P : ParameterLadder epsilon0 beta gamma}
    {C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family}
    {hdeltaOne : delta ≤ 1}
    {W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta
        (endpointScaleSequence delta hdeltaOne)}
    (X : EndpointFullRefinementShadingAwareBufferedInputData
      D hD P C hdeltaOne W)
    (sourceA : NNReal) (hsourceA : 0 < sourceA) :=
  coreShadingAwareCanonicalBufferedInput
    (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
    C (endpointScaleSequence delta hdeltaOne) P W
      sourceA hsourceA X.epsilonHalf X.fineNonempty
        X.activeMassNeZero X.radiusHalf

#print axioms
  EndpointFullRefinementShadingAwareBufferedInputData.toCanonicalBufferedInput

end

end Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV4
