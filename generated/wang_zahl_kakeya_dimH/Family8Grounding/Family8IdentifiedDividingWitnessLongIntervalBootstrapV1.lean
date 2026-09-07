import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalXLowerV2
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Family8Grounding.Family8LongIntervalBootstrapNumericsV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessLongIntervalBootstrapV1

open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open Family8LongIntervalBootstrapNumericsV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# The identified first-long witness in the long-interval numerical bootstrap

This module performs the remaining mechanical substitution into
`longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal`.  The lower bound for
`X` comes from the actual canonical Frostman constant, and its upper bound
comes from an actual `IsKatzTaoAtScale` certificate for the same coherent
global cover.  No naked `hXLower`, `hXUpper`, or final-bootstrap premise is
accepted.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The exact identified-witness specialization of the paper's long-interval
numerical implication. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_actual
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (A : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hrhoHalf :
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W <=
        (2 : NNReal)⁻¹)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hKT :
      (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf).IsKatzTaoAtScale
          (A : ENNReal))
    (hAKT : 1024 * A <=
      S.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta)))) :
    longIntervalKatzTaoRHSENNReal
        (S.tau W.m)
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf))
        P.epsilon (10 * P.eta W.stage / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        (S.tau W.m)
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf))
        (10 * P.eta W.stage / (P.epsilon * beta)) gamma := by
  let U :=
    Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf
  let b :=
    Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W
  let X := activeCoarseCardScaleMass U
  have hd : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hdOne : S.tau W.m <= 1 :=
    (S.tau_le_theta W.m).trans (S.theta_le_one W.m)
  have hdb : S.tau W.m <= b := by
    dsimp only [b]
    exact
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.tau_le_canonicalBufferedRadius
        W hD.delta_pos P.epsilon_pos.le
  have hbUpper : b <= S.tau W.m ^ (1 - P.epsilon) := by
    dsimp only [b,
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius]
    exact Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale_le_tau_rpow_one_sub
      (S.theta_le_one W.m) P.epsilon_pos.le
  have hXLower :
      S.tau W.m ^ (10 * P.eta W.stage / (P.epsilon * beta)) <= X := by
    dsimp only [X, U]
    exact
      Family8IdentifiedDividingWitnessCanonicalXLowerV2.Witness.parameterLadder_global_rpow_le_canonicalBufferedCardScaleMass
        D hD C S P W hbeta hepsilonHalf hrhoHalf hfine hC htauSmall
  have hXUpperCore : X <= 1024 * A := by
    dsimp only [X, U]
    exact
      Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover.activeCoarseCardScaleMass_le_1024_mul_nnreal_of_isKatzTaoAtScale
        D hD _ hrhoHalf A hKT
  have hXUpper : X <=
      S.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta))) :=
    hXUpperCore.trans hAKT
  exact longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal
    P W.stage hd hdOne hdb hbUpper hXLower hXUpper hbeta hgamma

#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_actual

end Witness

end
end Family8IdentifiedDividingWitnessLongIntervalBootstrapV1
