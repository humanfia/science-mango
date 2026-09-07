import Family8Grounding.Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
import Family8Grounding.Family8LocalCardRetainedNormalizedLongCoreWitnessV1
import FamilyStickyGrounding.FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2

/-!
# Automatic endpoint identity LongCore with its exact refined-card count

The automatic endpoint selector already produces one normalized LongCore on
the literal full-refinement identity cover and the one-step endpoint scale
sequence.  This file retains the local-card certificate at that same core.

There is no fixed-counted recursion here: its automatic constructor requires
an exponent profile larger than two, whereas the Section 8 parameter ladder
has a small `eta` profile.  For the identity cover the required pointwise
certificate is nevertheless available directly: every adjacent active-fine
cardinality is exactly the refined source cardinality.  The unique endpoint
interval is non-large because the endpoint sequence is not all-large.

Thus the result has no equality/reselection premise, no uniform-card premise,
and no caller-supplied pointwise-card premise.  Its stored bound is honestly
the exact refined cardinality; this module does not assert a smaller packing
bound.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace Family8EndpointIdentityAutomaticRefinedCardRetainedWitnessProducerV1

open Submission.Kakeya.Uniformity
open Family8EndpointIdentityCoreSelectorV2
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LocalCardRetainedNormalizedLongCoreWitnessV1
open Family8LocalCardRetainedNormalizedLongCoreWitnessV1.LocalCardRetainedNormalizedLongCoreWitness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Retain the exact identity-cover adjacent cardinality at the literal
automatic LongCore.  Since the endpoint sequence has depth one, the selected
index is its unique interval; its non-largeness follows from the established
failure of the all-large branch. -/
noncomputable def automaticRefinedCardRetainedNormalizedLongCoreWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P)
    {outputEta : Real} (hFOutput : FrostmanHypotheses D outputEta) :
    LocalCardRetainedNormalizedLongCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) := by
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
  have hnotAll : Not (S.AllStepsLarge P.epsilon) := by
    exact endpointScaleSequence_not_allStepsLarge
      hD.delta_pos hD.delta_le_half
        (parameterLadder_epsilon_lt_one P hbeta hgamma)
  have hnot : Not (S.IsLarge P.epsilon W.m) := by
    intro hlarge
    apply hnotAll
    intro m
    simpa only [Subsingleton.elim m W.m] using hlarge
  exact ofCoreAndBudget W hnot E.family.refinement.refined.card
    (identity_nonLargeLocalCardBudget_of_refined_card_le
      E.family S P.epsilon le_rfl)

@[simp] theorem automaticRefinedCardRetainedNormalizedLongCoreWitness_n
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P)
    {outputEta : Real} (hFOutput : FrostmanHypotheses D outputEta) :
    (automaticRefinedCardRetainedNormalizedLongCoreWitness
      D hD P hbeta hgamma hselectorSmall hFOutput).n =
        (fullRefinementDatum D).family.refinement.refined.card := by
  rfl

@[simp] theorem automaticRefinedCardRetainedNormalizedLongCoreWitness_core
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P)
    {outputEta : Real} (hFOutput : FrostmanHypotheses D outputEta) :
    (automaticRefinedCardRetainedNormalizedLongCoreWitness
      D hD P hbeta hgamma hselectorSmall hFOutput).core =
        automaticNormalizedLongCoreWitness
          D hD P hbeta hgamma hselectorSmall hFOutput := by
  rfl

@[simp] theorem automaticRefinedCardRetainedNormalizedLongCoreWitness_n_eq_card
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P)
    {outputEta : Real} (hFOutput : FrostmanHypotheses D outputEta) :
    (automaticRefinedCardRetainedNormalizedLongCoreWitness
      D hD P hbeta hgamma hselectorSmall hFOutput).n =
        Fintype.card index := by
  rw [automaticRefinedCardRetainedNormalizedLongCoreWitness_n,
    fullRefinementDatum_refined]
  exact Finset.card_univ

#print axioms automaticRefinedCardRetainedNormalizedLongCoreWitness
#print axioms automaticRefinedCardRetainedNormalizedLongCoreWitness_n
#print axioms automaticRefinedCardRetainedNormalizedLongCoreWitness_core
#print axioms automaticRefinedCardRetainedNormalizedLongCoreWitness_n_eq_card

end
end Family8EndpointIdentityAutomaticRefinedCardRetainedWitnessProducerV1
