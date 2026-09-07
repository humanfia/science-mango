import Family8Grounding.Family8IdentityCoherentCoreSelectorV1
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2

/-!
# The endpoint identity selector has no all-large branch

For an admissible actual datum the canonical one-step scale sequence is
`1 -> delta`.  The Section 8 ladder exponent is strictly below one, while
`0 < delta <= 1/2`.  Hence `delta < delta^epsilon`, so the unique step cannot
satisfy the all-large inequality.  The concrete identity-cover selector
therefore reduces to a normalized long core or a first normalized crossing.

V1 had an unused explicit positivity argument and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityCoreSelectorV2

open Submission.Kakeya.ConvexGeometry
open Family8IdentityCoherentCoreSelectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

theorem endpointScaleSequence_not_allStepsLarge
    {delta : NNReal}
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {epsilon : Real} (hepsilonLtOne : epsilon < 1) :
    ¬ (endpointScaleSequence delta
        (hdeltaHalf.trans (by norm_num))).AllStepsLarge epsilon := by
  intro hall
  have hlarge := hall (0 : Fin 1)
  have hdeltaLtOne : (delta : ENNReal) < 1 := by
    exact_mod_cast hdeltaHalf.trans_lt (by norm_num : (2 : NNReal)⁻¹ < 1)
  have hdeltaPosE : 0 < (delta : ENNReal) :=
    ENNReal.coe_pos.mpr hdeltaPos
  have hstrict : (delta : ENNReal) < (delta : ENNReal) ^ epsilon := by
    simpa only [ENNReal.rpow_one] using
      (ENNReal.rpow_lt_rpow_of_exponent_gt
        hdeltaPosE hdeltaLtOne hepsilonLtOne)
  unfold FiniteScaleSequence.IsLarge at hlarge
  simp only [endpointScaleSequence_theta_zero,
    endpointScaleSequence_tau_zero, ENNReal.coe_one, mul_one] at hlarge
  exact (not_lt_of_ge hlarge) hstrict

theorem parameterLadder_epsilon_lt_one
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1) :
    P.epsilon < 1 := by
  have hgap : gamma - beta < 1 := by linarith
  have hsixteen : 16 * P.epsilon < 1 := P.epsilon_gap.trans hgap
  nlinarith [P.epsilon_pos]

theorem endpointIdentity_longCore_or_firstCrossing
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1) :
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    Nonempty (NormalizedLongIntervalCoreWitness
        D.family (identityRadiusCoherentCover D.family)
          P.N P.epsilon P.eta S) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD (identityRadiusCoherentCover D.family) S
          P.epsilon P.epsilon_pos.le P.eta P.N) := by
  dsimp only
  have hnotAll := endpointScaleSequence_not_allStepsLarge
    hD.delta_pos hD.delta_le_half
      (parameterLadder_epsilon_lt_one P hbeta hgamma)
  rcases identity_allLarge_or_normalizedLongIntervalCore_or_firstCrossing
      D hD (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) P with
    (hall | hlong) | hfirst
  · exact (hnotAll hall).elim
  · exact Or.inl hlong
  · exact Or.inr hfirst

#print axioms endpointScaleSequence_not_allStepsLarge
#print axioms parameterLadder_epsilon_lt_one
#print axioms endpointIdentity_longCore_or_firstCrossing

end
end Family8EndpointIdentityCoreSelectorV2
