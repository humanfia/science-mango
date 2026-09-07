import Family8Grounding.Family8EndpointIdentityDividingScaleOutputOrchestrationV4
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4
import Family8Grounding.Family8LongIntervalBootstrapNumericsV1
import Family8Grounding.Family8MultiplicityLossMonotonicityV4
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8Prop66AActualFamilyVolumeTransportV1
import Mathlib.Tactic

/-!
# Low-fresh long-interval target to the actual-volume DSO right branch

The normalized fresh Katz--Tao step ends at

`longIntervalFrostmanTargetENNReal (delta / 8) delta
  ((freshCard : NNReal) * delta ^ 2) etaPrime gamma`.

This file performs only the scalar transport still needed by the
dividing-scale output.  The fresh cardinality is compared with the ambient
tau-active cardinality, the already-proved card-scale/actual-volume estimate
costs exactly `2 ^ (1 - gamma / 2)`, and endpoint identity then replaces the
tau-active family volume by the source family volume.  No family or selected
set is chosen here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8LowFreshLongIntervalTargetActualDSOTransportV1

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8MultiplicityLossMonotonicityV4
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-! ## Pure scalar transport -/

/-- If `d <= delta <= 1`, a nonnegative stage exponent below
`etaPrime` gives the power in the direction required by the DSO:

`d^(10 etaPrime) <= delta^(10 etaStage)`.

This exposes both monotonicity steps instead of hiding the relation between
`etaPrime` and the official stage exponent. -/
theorem secondaryScale_tenEtaPrime_le_stageTenEta
    {d delta : NNReal} {etaStage etaPrime : Real}
    (hdDelta : d <= delta) (hdeltaOne : delta <= 1)
    (hetaStage0 : 0 <= etaStage)
    (hetaStagePrime : etaStage <= etaPrime) :
    (d : ENNReal) ^ (10 * etaPrime) <=
      (delta : ENNReal) ^ (10 * etaStage) := by
  have hdOneENN : (d : ENNReal) <= 1 := by
    exact_mod_cast hdDelta.trans hdeltaOne
  have hdDeltaENN : (d : ENNReal) <= (delta : ENNReal) := by
    exact_mod_cast hdDelta
  have hten0 : 0 <= 10 * etaStage := by linarith
  have hten : 10 * etaStage <= 10 * etaPrime := by linarith
  calc
    (d : ENNReal) ^ (10 * etaPrime) <=
        (d : ENNReal) ^ (10 * etaStage) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN hten
    _ <= (delta : ENNReal) ^ (10 * etaStage) :=
      ENNReal.rpow_le_rpow hdDeltaENN hten0

/-- For the paper's literal primed exponent, the comparison required by
`secondaryScale_tenEtaPrime_le_stageTenEta` follows from the ordinary
parameter range.  This is a scalar fact only; it does not strengthen the
long-interval target. -/
theorem parameterLadder_eta_le_longIntervalEtaPrime
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (j : Nat) (hbeta : 0 < beta) (hgammaOne : gamma <= 1) :
    P.eta j <= 10 * P.eta j / (P.epsilon * beta) := by
  have hbetaOne : beta <= 1 := by
    nlinarith [P.epsilon_gap, P.epsilon_pos]
  have hepsilonOne : P.epsilon <= 1 := by
    nlinarith [P.epsilon_gap, P.epsilon_pos, hbeta]
  have hepsilonBetaOne : P.epsilon * beta <= 1 := by
    calc
      P.epsilon * beta <= 1 * 1 :=
        mul_le_mul hepsilonOne hbetaOne hbeta.le (by norm_num)
      _ = 1 := by norm_num
  have hden : 0 < P.epsilon * beta :=
    mul_pos P.epsilon_pos hbeta
  apply (le_div_iff₀ hden).2
  calc
    P.eta j * (P.epsilon * beta) <= P.eta j * 1 :=
      mul_le_mul_of_nonneg_left hepsilonBetaOne (P.eta_pos j).le
    _ <= 10 * P.eta j := by
      nlinarith [P.eta_pos j]

/-- Minimal count-to-actual-volume transport for the long-interval target.

The epsilon comparison is deliberately `0 <= targetEpsilon / 4`: the
long-interval target contains no epsilon loss, so it is first identified with
the card-scale Frostman RHS at epsilon zero.  Increasing epsilon enlarges the
RHS on scales at most one.  The factor `2 ^ (1 - gamma / 2)` points from
card-scale volume to actual volume and is valid under `gamma <= 2`.
-/
theorem longIntervalFrostmanTargetENNReal_card_le_actual
    {d delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {tubeCount : Nat}
    {etaStage etaPrime targetEpsilon gamma : Real}
    (hdDelta : d <= delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hcard : tubeCount <= Fintype.card iota)
    (hetaStage0 : 0 <= etaStage)
    (hetaStagePrime : etaStage <= etaPrime)
    (hTargetEpsilon0 : 0 <= targetEpsilon)
    (hgammaTwo : gamma <= 2) :
    longIntervalFrostmanTargetENNReal d delta
        ((tubeCount : NNReal) * delta ^ 2) etaPrime gamma <=
      ((2 : ENNReal) ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (10 * etaStage)) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume (targetEpsilon / 4) gamma := by
  have hdeltaOne : delta <= 1 :=
    hdeltaHalf.trans (by norm_num)
  have hsecondary :
      (d : ENNReal) ^ (10 * etaPrime) <=
        (delta : ENNReal) ^ (10 * etaStage) :=
    secondaryScale_tenEtaPrime_le_stageTenEta
      hdDelta hdeltaOne hetaStage0 hetaStagePrime
  have hcardENN :
      (tubeCount : ENNReal) <= (Fintype.card iota : ENNReal) := by
    exact_mod_cast hcard
  have hvolume :
      (((tubeCount : NNReal) * delta ^ 2 : NNReal) : ENNReal) <=
        proposition66ACardScaleVolume delta (Fintype.card iota) := by
    simpa only [proposition66ACardScaleVolume, ENNReal.coe_mul,
      ENNReal.coe_natCast, ENNReal.coe_pow, mul_comm] using
      (mul_le_mul' hcardENN
        (show (delta : ENNReal) ^ (2 : Nat) <=
          (delta : ENNReal) ^ (2 : Nat) from le_rfl))
  have hvolumePower :
      ((((tubeCount : NNReal) * delta ^ 2 : NNReal) : ENNReal) ^
          (1 - gamma / 2)) <=
        proposition66ACardScaleVolume delta (Fintype.card iota) ^
          (1 - gamma / 2) :=
    ENNReal.rpow_le_rpow hvolume (by linarith)
  have hactual :
      frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta (Fintype.card iota))
          0 gamma <=
        frostmanMultiplicityRHS delta D.actualFamilyVolume 0 gamma *
          (2 : ENNReal) ^ (1 - gamma / 2) :=
    frostmanMultiplicityRHS_cardScale_le_actual_mul_two_rpow
      D hdeltaHalf hgammaTwo
  have hepsilon :
      frostmanMultiplicityRHS delta D.actualFamilyVolume 0 gamma <=
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume (targetEpsilon / 4) gamma :=
    frostmanMultiplicityRHS_mono_epsilon
      hdeltaOne (by linarith)
  unfold longIntervalFrostmanTargetENNReal
  calc
    (d : ENNReal) ^ (10 * etaPrime) *
          (delta : ENNReal) ^ (-2 * gamma) *
          (((tubeCount : NNReal) * delta ^ 2 : NNReal) : ENNReal) ^
            (1 - gamma / 2) <=
        (delta : ENNReal) ^ (10 * etaStage) *
          (delta : ENNReal) ^ (-2 * gamma) *
          proposition66ACardScaleVolume delta (Fintype.card iota) ^
            (1 - gamma / 2) := by
      exact mul_le_mul' (mul_le_mul' hsecondary le_rfl) hvolumePower
    _ = (delta : ENNReal) ^ (10 * etaStage) *
          frostmanMultiplicityRHS delta
            (proposition66ACardScaleVolume delta (Fintype.card iota))
            0 gamma := by
      unfold frostmanMultiplicityRHS
      simp only [neg_zero, ENNReal.rpow_zero, one_mul]
      ac_rfl
    _ <= (delta : ENNReal) ^ (10 * etaStage) *
          (frostmanMultiplicityRHS delta D.actualFamilyVolume 0 gamma *
            (2 : ENNReal) ^ (1 - gamma / 2)) :=
      mul_le_mul' le_rfl hactual
    _ <= (delta : ENNReal) ^ (10 * etaStage) *
          (frostmanMultiplicityRHS delta D.actualFamilyVolume
              (targetEpsilon / 4) gamma *
            (2 : ENNReal) ^ (1 - gamma / 2)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' hepsilon le_rfl)
    _ = ((2 : ENNReal) ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (10 * etaStage)) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume (targetEpsilon / 4) gamma := by
      ac_rfl

/-! ## Endpoint identity and the DSO right branch -/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- At the endpoint, every retained fresh child of a low subset is
automatically a subset of the same tau-active ambient family.  The ambient
actual volume is then definitionally transported back to the source datum.
-/
theorem endpointIdentity_lowFresh_longIntervalTarget_le_sourceActual
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (j : Nat) {etaPrime : Real}
    (hetaStagePrime : P.eta j <= etaPrime)
    (hTargetEpsilon0 : 0 <= targetEpsilon)
    (hgammaTwo : gamma <= 2) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let hdeltaOne : delta <= 1 :=
      hD.delta_le_half.trans (by norm_num)
    let S := endpointScaleSequence delta hdeltaOne
    let T := tauScaleCover E C S W
    forall selectedLow : Finset {k // k ∈ T.activeCoarse},
      forall selectedFresh : Finset {k // k ∈ selectedLow},
        longIntervalFrostmanTargetENNReal (delta / 8) delta
            ((selectedFresh.card : NNReal) * delta ^ 2)
            etaPrime gamma <=
          ((2 : ENNReal) ^ (1 - gamma / 2) *
              (delta : ENNReal) ^ (10 * P.eta j)) *
            frostmanMultiplicityRHS
              delta D.actualFamilyVolume (targetEpsilon / 4) gamma := by
  dsimp only
  intro selectedLow selectedFresh
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let hdeltaOne : delta <= 1 :=
    hD.delta_le_half.trans (by norm_num)
  let S := endpointScaleSequence delta hdeltaOne
  let T := tauScaleCover E C S W
  let Dtau := tauActiveCoarseDatum E C S W
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta hdeltaOne C W
  have hfreshLow : selectedFresh.card <= selectedLow.card := by
    simpa only [Fintype.card_coe] using
      (Finset.card_le_univ selectedFresh)
  have hlowAmbient :
      selectedLow.card <= Fintype.card {k // k ∈ T.activeCoarse} := by
    simpa only [Fintype.card_coe] using
      (Finset.card_le_univ selectedLow)
  have hfreshAmbient :
      selectedFresh.card <= Fintype.card {k // k ∈ T.activeCoarse} :=
    hfreshLow.trans hlowAmbient
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ := by
    simpa only [htau] using hD.delta_le_half
  have htransport :=
    longIntervalFrostmanTargetENNReal_card_le_actual
      (D := Dtau)
      (d := S.tau W.m / 8)
      (tubeCount := selectedFresh.card)
      (etaStage := P.eta j)
      (etaPrime := etaPrime)
      (targetEpsilon := targetEpsilon)
      (gamma := gamma)
      (div_le_self (show 0 <= S.tau W.m from bot_le)
        (by norm_num : (1 : NNReal) <= 8))
      htauHalf hfreshAmbient (P.eta_pos j).le
      hetaStagePrime hTargetEpsilon0 hgammaTwo
  have hvolume :
      Dtau.actualFamilyVolume = D.actualFamilyVolume := by
    simpa only [Dtau, ActualTubeDatum.actualFamilyVolume] using
      (endpointLongCore_identity_tauActive_familyVolume_eq_source
        D hD P W)
  simpa only [htau, hvolume, E, C, hdeltaOne, S, T, Dtau] using
    htransport

/-- Terminal right-branch wrapper for the DSO.  Its two inputs are exactly
the analytic low-fresh estimate and the independent aggregate-loss budget;
the desired DSO inequality itself is not assumed. -/
theorem endpointIdentity_lowFreshTarget_dividingScaleOutput
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (j : Nat) (hj : j <= P.N) {etaPrime : Real}
    (hetaStagePrime : P.eta j <= etaPrime)
    (hTargetEpsilon0 : 0 <= targetEpsilon)
    (hgammaTwo : gamma <= 2) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let hdeltaOne : delta <= 1 :=
      hD.delta_le_half.trans (by norm_num)
    let S := endpointScaleSequence delta hdeltaOne
    let T := tauScaleCover E C S W
    forall selectedLow : Finset {k // k ∈ T.activeCoarse},
      forall selectedFresh : Finset {k // k ∈ selectedLow},
        forall freshOuter : ENNReal,
          D.shading.averageMultiplicity <=
              freshOuter *
                longIntervalFrostmanTargetENNReal (delta / 8) delta
                  ((selectedFresh.card : NNReal) * delta ^ 2)
                  etaPrime gamma ->
          freshOuter * (2 : ENNReal) ^ (1 - gamma / 2) <=
              (delta : ENNReal) ^ (-3 * P.eta j) ->
          DividingScaleOutput D P targetEpsilon := by
  dsimp only
  intro selectedLow selectedFresh freshOuter hsource houter
  have htarget :=
    endpointIdentity_lowFresh_longIntervalTarget_le_sourceActual
      D hD P W j hetaStagePrime hTargetEpsilon0 hgammaTwo
        selectedLow selectedFresh
  refine Or.inr
    ⟨j, freshOuter * (2 : ENNReal) ^ (1 - gamma / 2),
      hj, houter, ?_⟩
  calc
    D.shading.averageMultiplicity <=
        freshOuter *
          longIntervalFrostmanTargetENNReal (delta / 8) delta
            ((selectedFresh.card : NNReal) * delta ^ 2)
            etaPrime gamma := hsource
    _ <= freshOuter *
        (((2 : ENNReal) ^ (1 - gamma / 2) *
            (delta : ENNReal) ^ (10 * P.eta j)) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma) :=
      mul_le_mul' le_rfl htarget
    _ = ((freshOuter * (2 : ENNReal) ^ (1 - gamma / 2)) *
          (delta : ENNReal) ^ (10 * P.eta j)) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume (targetEpsilon / 4) gamma := by
      ac_rfl

#print axioms secondaryScale_tenEtaPrime_le_stageTenEta
#print axioms parameterLadder_eta_le_longIntervalEtaPrime
#print axioms longIntervalFrostmanTargetENNReal_card_le_actual
#print axioms endpointIdentity_lowFresh_longIntervalTarget_le_sourceActual
#print axioms endpointIdentity_lowFreshTarget_dividingScaleOutput

end

end Family8LowFreshLongIntervalTargetActualDSOTransportV1
