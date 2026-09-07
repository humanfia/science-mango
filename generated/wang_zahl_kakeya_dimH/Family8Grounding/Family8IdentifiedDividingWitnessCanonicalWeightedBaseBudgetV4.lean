import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8IdentifiedDividingWitnessTauActiveCoarseB2NormalizationV4
import Family8Grounding.Family8CanonicalFrostmanWeightedFirstLongBaseBudgetV7

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessCanonicalWeightedBaseBudgetV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

/-!
# Identified weighted base budget with automatic parent support

The raw active `tau_m` parent datum is supported in `B(0,2)` at the explicit
small-scale threshold.  The radius-two version of the canonical Frostman
base estimate therefore removes the former
`TauActiveCoarseAdmissibility`/pairwise-parent geometry premise entirely.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem weightedSelected_baseBudget_of_identifiedWitness_canonicalFrostman
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (R : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hbeta : 0 < beta)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (htauSixteenth : S.tau R.m <= (1 / 16 : NNReal))
    (hrhoHalf :
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius R <=
        (2 : NNReal)⁻¹)
    (hfine : D.family.refinement.refined.Nonempty)
    {B A : ENNReal} {loss : Real}
    (W : DoubledParentConflictWeightedSelection
      (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.canonicalBufferedTauActiveCover
        D hD C S R P.epsilon_pos.le hepsilonHalf)
      (parentShadingWeight
        (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.canonicalBufferedTauActiveCover
          D hD C S R P.epsilon_pos.le hepsilonHalf)
        (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
          D C S R).shading) B)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hC : canonicalFrostmanConstant
        (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
          R hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau R.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P R.stage))
    (htauSmall : S.tau R.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P R.stage)
    (hscalarCap :
      B * (A * volume (unitBallBody : Set Space)) <=
        (S.tau R.m : ENNReal) ^ (-loss) *
          ((S.tau R.m : ENNReal) ^
            (10 * P.eta R.stage / (P.epsilon * beta) + 2 * P.epsilon) / 2)) :
    A * volume (unitBallBody : Set Space) <=
      (S.tau R.m : ENNReal) ^ (-loss) *
        (restrictActualTubeDatum
          (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
            D C S R)
          (weightedSelectedFineIndices
            (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
              D C S R).shading W)).actualFamilyVolume := by
  let Dtau :=
    Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauActiveCoarseDatum
      D C S R
  let U :=
    Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.canonicalBufferedTauActiveCover
      D hD C S R P.epsilon_pos.le hepsilonHalf
  have htau : 0 < S.tau R.m :=
    hD.delta_pos.trans_le (S.delta_le_tau R.m)
  have htauHalf : S.tau R.m <= (2 : NNReal)⁻¹ :=
    htauSixteenth.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) <= 16 by norm_num)))
  have hB2 : forall k,
      (Dtau.family.tubes k).carrier ⊆ Metric.closedBall (0 : Space) 2 := by
    intro k
    exact
      Family8IdentifiedDividingWitnessTauActiveCoarseB2NormalizationV4.Witness.tauActiveCoarseDatum_carrier_subset_closedBall_two
        D hD C S R htauSixteenth k
  have hrho : 0 <
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius R :=
    Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius_pos
      R hD.delta_pos P.epsilon_pos.le
  have hcoarseGlobal :
      (Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover
        R hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarse.Nonempty :=
    Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedGlobalCover_activeCoarse_nonempty
      R hD.delta_pos P.epsilon_pos.le hepsilonHalf hfine
  have hcoarse : U.activeCoarse.Nonempty := hcoarseGlobal
  have hClocal : canonicalFrostmanConstant
      U.activeCoarseFamily closedBallFourBody <=
    (S.tau R.m : ENNReal) ^
      (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
        P R.stage) := by
    rw [Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global]
    exact hC
  exact
    Family8CanonicalFrostmanWeightedFirstLongBaseBudgetV7.StickyScaleCover.weightedSelected_baseBudget_of_parameterLadder_canonicalFrostman_B2
      (globalDelta := S.tau R.m) (tau := S.tau R.m)
      (theta := S.theta R.m)
      (index := {k // k ∈
        (Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness.tauScaleCover
          D C S R).activeCoarse})
      Dtau hB2 htauHalf P R.stage hbeta W htau le_rfl
        (S.theta_le_one R.m) hrho hrhoHalf hcoarse hB0 hBTop hClocal
        htauSmall hscalarCap

#print axioms weightedSelected_baseBudget_of_identifiedWitness_canonicalFrostman

end Witness

end
end Family8IdentifiedDividingWitnessCanonicalWeightedBaseBudgetV4
