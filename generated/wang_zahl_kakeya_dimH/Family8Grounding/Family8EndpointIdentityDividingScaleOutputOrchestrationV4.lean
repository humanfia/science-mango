import Family8Grounding.Family8EndpointIdentityCoreSelectorV2
import Family8Grounding.Family8AllFrostmanFixedNuBranchOrchestrationV2

/-!
# Exact two-branch handoff to the dividing-scale output

This file fixes the literal proposition consumed by the existing
`mainLemmaOne_of_allFrostman_or_outerThree_middleTen` theorem and maps the
concrete endpoint identity selector into it.  It is deliberately a branch
orchestrator, not a geometric closure: the two remaining hypotheses are the
honest long-core and first-crossing producers on exactly the selected
objects.

V1--V3 were linter/elaboration drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentityDividingScaleOutputOrchestrationV4

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityCoreSelectorV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- The exact datum-level disjunction required by the fixed-nu top-level
orchestration theorem. -/
def DividingScaleOutput
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon : Real) : Prop :=
  ((delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion) ∨
    (exists j : Nat, exists outerLoss : ENNReal,
      j <= P.N /\
      outerLoss <= (delta : ENNReal) ^ (-3 * P.eta j) /\
      D.shading.averageMultiplicity <=
        (outerLoss * (delta : ENNReal) ^ (10 * P.eta j)) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma)

/-- Once the long-core and first-crossing producers return the exact output,
the concrete stopping selector supplies it without an all-large callback. -/
theorem dividingScaleOutput_of_endpointIdentity_branches
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {epsilon0 beta gamma targetEpsilon : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hLong : forall _W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta
          (endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))),
        DividingScaleOutput D P targetEpsilon)
    (hFirst : forall _W : FirstActualNormalizedCrossingWitness
      D hD (identityRadiusCoherentCover D.family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num)))
        P.epsilon P.epsilon_pos.le P.eta P.N,
        DividingScaleOutput D P targetEpsilon) :
    DividingScaleOutput D P targetEpsilon := by
  rcases endpointIdentity_longCore_or_firstCrossing D hD P hbeta hgamma with
    hlong | hfirst
  · exact Nonempty.elim hlong hLong
  · exact Nonempty.elim hfirst hFirst

#print axioms DividingScaleOutput
#print axioms dividingScaleOutput_of_endpointIdentity_branches

end
end Family8EndpointIdentityDividingScaleOutputOrchestrationV4
