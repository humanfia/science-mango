import Family8Grounding.Family8EndpointIdentityLongCoreSourceKatzTaoHypothesesAdapterV1
import Family8Grounding.Family8CanonicalGlobalOuterScaleCountIdentityV1

/-!
# Source Katz--Tao LongCore outer scale-count factor

This successor rewrites the verified V521 endpoint into the exact `b -> 1`
scale-count factor used by the three-scale package.  It also weakens V521's
strong local gain to the global `delta^(10 * eta_stage)` gain.

This remains a numerical factor, not a fabricated average-multiplicity
factorization: a same-object estimate placing an actual average below the
left-hand side is still required before the DSO consumer can use it.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityLongCoreSourceKatzTaoOuterScaleCountV1

open Family8CanonicalGlobalOuterScaleCountIdentityV1
open Family8EndpointIdentityLongCoreDirectNumericsComposerV1
open Family8EndpointIdentityLongCoreSourceKatzTaoHypothesesAdapterV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8SectionEightOutputEtaV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma sourceEta etaKT : Real}

/-- The V521 source-KT endpoint in the exact outer scale-count form used by
the three-scale LongCore records. -/
theorem longIntervalKatzTaoRHSENNReal_le_endpointIdentity_outerScaleCountFactor_of_sourceKatzTaoHypotheses
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta))
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : etaKT <= P.epsilon +
      10 * P.eta W.stage / (P.epsilon * beta))
    (hsmall : delta <=
      endpointIdentityLongCoreDirectNumericsThreshold P W.stage) :
    longIntervalKatzTaoRHSENNReal
        ((endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))).tau W.m)
        (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover W hD.delta_pos P.epsilon_pos.le
            (by
              nlinarith [P.epsilon_gap] : P.epsilon <= 1 / 2)))
        P.epsilon (10 * P.eta W.stage / (P.epsilon * beta)) beta <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (canonicalBufferedRadius W) 1
          (canonicalBufferedGlobalCover W hD.delta_pos P.epsilon_pos.le
            (by
              nlinarith [P.epsilon_gap] : P.epsilon <= 1 / 2)).activeCoarse.card
          gamma := by
  let hepsilonHalf : P.epsilon <= 1 / 2 := by
    nlinarith [P.epsilon_gap]
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  let etaPrime := 10 * P.eta W.stage / (P.epsilon * beta)
  have hraw :=
    longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_endpointIdentity_sourceKatzTaoHypotheses
      D hD P W hbeta hgamma hFOutput hKTsource hetaKT hsmall
  have hbetaOne : beta <= 1 := by
    nlinarith [P.epsilon_gap, P.epsilon_pos]
  have hepsilonOne : P.epsilon <= 1 := by
    nlinarith [P.epsilon_gap]
  have hepsilonBetaOne : P.epsilon * beta <= 1 := by
    calc
      P.epsilon * beta <= 1 * 1 :=
        mul_le_mul hepsilonOne hbetaOne hbeta.le (by norm_num)
      _ = 1 := by norm_num
  have hden : 0 < P.epsilon * beta :=
    mul_pos P.epsilon_pos hbeta
  have hetaGain : P.eta W.stage <= etaPrime := by
    dsimp only [etaPrime]
    apply (le_div_iff₀ hden).2
    calc
      P.eta W.stage * (P.epsilon * beta) <=
          P.eta W.stage * 1 :=
        mul_le_mul_of_nonneg_left hepsilonBetaOne
          (P.eta_pos W.stage).le
      _ <= 10 * P.eta W.stage := by
        nlinarith [P.eta_pos W.stage]
  have hpower : (delta : ENNReal) ^ (10 * etaPrime) <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge
    · exact_mod_cast hD.delta_le_half.trans (by norm_num)
    · nlinarith
  calc
    longIntervalKatzTaoRHSENNReal
          (S.tau W.m) (canonicalBufferedRadius W)
          (activeCoarseCardScaleMass U)
          P.epsilon etaPrime beta <=
        longIntervalFrostmanTargetENNReal
          (S.tau W.m) (canonicalBufferedRadius W)
          (activeCoarseCardScaleMass U) etaPrime gamma := by
      simpa only [S, U, etaPrime, hepsilonHalf] using hraw
    _ = (delta : ENNReal) ^ (10 * etaPrime) *
          sectionEightScaleCountFrostmanFactor
            (canonicalBufferedRadius W) 1 U.activeCoarse.card gamma := by
      rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
        endpointScaleSequence_tau_zero]
      unfold longIntervalFrostmanTargetENNReal
      rw [mul_assoc,
        activeCoarseCardScaleMass_middleFactor_eq_sectionEight]
    _ <= (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            (canonicalBufferedRadius W) 1 U.activeCoarse.card gamma :=
      mul_le_mul' hpower le_rfl

#print axioms
  longIntervalKatzTaoRHSENNReal_le_endpointIdentity_outerScaleCountFactor_of_sourceKatzTaoHypotheses

end
end Family8EndpointIdentityLongCoreSourceKatzTaoOuterScaleCountV1
