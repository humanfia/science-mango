import Family8Grounding.Family8AllRealBoundaryReductionV1
import Family8Grounding.Family8FrostmanExponentTransportV1
import Family8Grounding.Family8ExponentRangeConsequencesV1

namespace Family8PointwiseSelfImprovementLimitOrchestrationV2

open Family8KatzTaoFrostmanPropertiesV1
open Family8AllRealBoundaryReductionV1
open Family8FrostmanExponentTransportV1
open Family8ExponentRangeConsequencesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Pointwise self-improvement closes Main Lemma 1

The official bootstrap is usually stated with a decrement
`nu = nu gamma beta` which is monotone in `gamma`.  Monotonicity is not
needed once the already-proved right-limit closure of `FrostmanProperty` is
used.

Indeed, let `alpha` be the infimum of the exponents at which a monotone
property `P` is known.  Upward transport and the infimum property give `P`
at every exponent strictly above `alpha`; right-limit closure gives
`P alpha`.  If `alpha` is still above the target, a single pointwise strict
improvement produces `P` below `alpha`, contradicting minimality (or landing
below the target, from where upward transport finishes immediately).

Consequently the sole geometric theorem still required by the property
layer has the explicit type displayed in
`mainLemmaOne_of_positive_pointwise_selfImprovement`: for every
`0 < beta < gamma <= 1`, `KatzTaoProperty beta` and
`FrostmanProperty gamma` produce some positive `nu` and
`FrostmanProperty (gamma - nu)`.  No monotonicity, uniform lower bound, or
endpoint value of `nu` is required.  The `beta = 0` endpoint is recovered
mechanically by upward Katz--Tao transport and Frostman right-limit closure.

V1 is a failed notation draft and is not imported.
-/

/-- An upward-closed, right-limit-closed property reaches a target from a
base exponent if every known exponent above the target admits some strict
downward improvement.  Neither a global choice of decrements nor any
monotonicity/uniformity of those decrements is assumed. -/
theorem property_at_target_of_pointwise_improvement_limit
    (P : Real -> Prop) {beta : Real}
    (hbetaOne : beta < 1)
    (hbase : P 1)
    (htransport : forall {lower upper : Real},
      lower <= upper -> P lower -> P upper)
    (himprove : forall gamma : Real, beta < gamma -> gamma <= 1 ->
      P gamma -> exists nu : Real, 0 < nu /\ P (gamma - nu))
    (hclosure : forall target : Real,
      (forall gamma : Real, target < gamma -> P gamma) -> P target) :
    P beta := by
  let S : Set Real := {gamma | beta <= gamma /\ P gamma}
  have hOneMem : (1 : Real) ∈ S := by
    exact ⟨hbetaOne.le, hbase⟩
  have hSNonempty : S.Nonempty := by
    exact Set.nonempty_of_mem hOneMem
  have hSBdd : BddBelow S := by
    refine ⟨beta, ?_⟩
    intro gamma hgamma
    exact hgamma.1
  let alpha : Real := sInf S
  have hbetaAlpha : beta <= alpha := by
    dsimp only [alpha]
    exact le_csInf hSNonempty (fun gamma hgamma => hgamma.1)
  have halphaOne : alpha <= 1 := by
    dsimp only [alpha]
    exact csInf_le hSBdd hOneMem
  have hAbove : forall gamma : Real, alpha < gamma -> P gamma := by
    intro gamma halphaGamma
    by_cases hOneGamma : 1 <= gamma
    · exact htransport hOneGamma hbase
    · have hgammaOne : gamma < 1 := lt_of_not_ge hOneGamma
      obtain ⟨lower, hlowerS, hlowerGamma⟩ :=
        exists_lt_of_csInf_lt hSNonempty (by
          simpa only [alpha] using halphaGamma)
      exact htransport hlowerGamma.le hlowerS.2
  have hPAlpha : P alpha := hclosure alpha hAbove
  by_cases halphaBeta : alpha = beta
  · simpa only [halphaBeta] using hPAlpha
  · have hbetaAlphaStrict : beta < alpha :=
      lt_of_le_of_ne hbetaAlpha (Ne.symm halphaBeta)
    obtain ⟨nu, hnu, hPImproved⟩ :=
      himprove alpha hbetaAlphaStrict halphaOne hPAlpha
    by_cases htargetImproved : beta <= alpha - nu
    · have hImprovedMem : alpha - nu ∈ S := by
        exact ⟨htargetImproved, hPImproved⟩
      have hminimal : alpha <= alpha - nu := by
        dsimp only [alpha]
        exact csInf_le hSBdd hImprovedMem
      linarith
    · exact htransport (le_of_not_ge htargetImproved) hPImproved

/-- Specialization to the actual Frostman property at a fixed target below
one.  Its premise is precisely the pointwise geometric bootstrap for that
target, after the fixed Katz--Tao hypothesis has been supplied. -/
theorem frostmanProperty_at_target_of_pointwise_selfImprovement
    {beta : Real} (hbetaOne : beta < 1)
    (hstep : forall gamma : Real, beta < gamma -> gamma <= 1 ->
      FrostmanProperty gamma ->
        exists nu : Real, 0 < nu /\ FrostmanProperty (gamma - nu)) :
    FrostmanProperty beta := by
  exact property_at_target_of_pointwise_improvement_limit
    FrostmanProperty hbetaOne
    Family8CommonPointTubePackingV1.frostmanProperty_one
    (fun hlowerUpper hlower => frostmanProperty_mono hlowerUpper hlower)
    hstep
    (fun target hall => frostmanProperty_of_forall_gt hall)

/-- The exact unit-interval orchestration.  Its single non-mechanical input
is the paper's positive-target pointwise bootstrap, with all quantifiers
visible.  In particular the desired `FrostmanProperty beta` is not a
premise, and no theorem input is hidden in a structure. -/
theorem unitInterval_of_positive_pointwise_selfImprovement
    (hstep : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty gamma ->
        exists nu : Real, 0 < nu /\ FrostmanProperty (gamma - nu)) :
    forall beta : Real, 0 <= beta -> beta <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty beta := by
  intro beta hbetaZero hbetaOne hKT
  rcases hbetaZero.eq_or_lt with hbetaEq | hbetaPos
  · subst beta
    apply frostmanProperty_of_forall_gt
    intro gamma hgamma
    by_cases hgammaOne : gamma < 1
    · have hKTGamma : KatzTaoProperty gamma :=
        katzTaoProperty_mono hgamma.le hKT
      exact
        frostmanProperty_at_target_of_pointwise_selfImprovement
          hgammaOne
          (fun upper hgammaUpper hupperOne hFUpper =>
            hstep gamma upper hgamma hgammaUpper hupperOne
              hKTGamma hFUpper)
    · exact frostmanProperty_of_one_le (le_of_not_gt hgammaOne)
  · by_cases hbetaEqOne : beta = 1
    · subst beta
      exact Family8CommonPointTubePackingV1.frostmanProperty_one
    · have hbetaOneStrict : beta < 1 :=
        lt_of_le_of_ne hbetaOne hbetaEqOne
      exact
        frostmanProperty_at_target_of_pointwise_selfImprovement
          hbetaOneStrict
          (fun gamma hbetaGamma hgammaOne hFGamma =>
            hstep beta gamma hbetaPos hbetaGamma hgammaOne hKT hFGamma)

/-- All-real Main Lemma 1 follows mechanically from the sole positive
pointwise geometric bootstrap displayed here. -/
theorem mainLemmaOne_of_positive_pointwise_selfImprovement
    (hstep : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty gamma ->
        exists nu : Real, 0 < nu /\ FrostmanProperty (gamma - nu))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  exact mainLemmaOne_of_unitInterval
    (unitInterval_of_positive_pointwise_selfImprovement hstep) beta

#print axioms property_at_target_of_pointwise_improvement_limit
#print axioms frostmanProperty_at_target_of_pointwise_selfImprovement
#print axioms unitInterval_of_positive_pointwise_selfImprovement
#print axioms mainLemmaOne_of_positive_pointwise_selfImprovement

end

end Family8PointwiseSelfImprovementLimitOrchestrationV2
