import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2
import FamilyStickyGrounding.FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedCFDividingWitnessActualCoverBridgeV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Actual-datum specializations of the normalized-CF bridge

These statements expose exactly the three actual covers occurring in the
identified Lemma 7.7(A) witness: source-to-`tau`, `tau`-to-`theta`, and
`tau`-to-an-intermediate-`rho`.  A genuine normalized Frostman estimate on
one of those covers automatically gives the corresponding absolute legacy
upper bound, with the literal computed parent-density loss retained.

The intermediate theorem is intentionally one-sided.  Producing the paper's
normalized lower bound at all buffered radii does not imply the legacy
absolute lower bound unless the actual parent-density normalization has a
separate lower estimate.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A normalized at-scale Frostman bound produces an absolute fibre bound
with exactly the actual parent-density loss and no theorem-valued callback. -/
theorem fiberDeltaMax_le_error_mul_actualParentLoss_of_isFrostmanAtScale
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta) (hrho : 0 < rho)
    {error : ENNReal} (hF : S.IsFrostmanAtScale error) :
    fiberDeltaMax S ≤ error * actualParentFiberMassLoss S := by
  calc
    fiberDeltaMax S ≤
        parentNormalizedFiberCFMax S * actualParentFiberMassLoss S :=
      fiberDeltaMax_le_parentNormalizedFiberCFMax_mul_actualParentLoss
        S hdelta hrho
    _ ≤ error * actualParentFiberMassLoss S := by
      gcongr
      exact
        (isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
          S hdelta error).mp hF

end StickyScaleCover

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The actual source-to-`tau_m` value used in the identified witness is
controlled by its genuine normalized Frostman estimate and computed parent
loss. -/
theorem actualDatum_sourceToTau_fiberDeltaMax_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    {error : ENNReal}
    (hF : (C.base.cover (S.tau m) (S.delta_le_tau m)
      ((S.tau_le_theta m).trans (S.theta_le_one m))).IsFrostmanAtScale error) :
    fiberDeltaMax
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) ≤
      error * actualParentFiberMassLoss
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) := by
  apply
    Family8NormalizedCFDividingWitnessActualCoverBridgeV3.StickyScaleCover.fiberDeltaMax_le_error_mul_actualParentLoss_of_isFrostmanAtScale
      _ hD.delta_pos _ hF
  exact hD.delta_pos.trans_le (S.delta_le_tau m)

/-- The actual `tau_m`-to-`theta_m` adjacent value has the same honest
normalized-to-absolute transport. -/
theorem actualDatum_tauToTheta_fiberDeltaMax_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    {error : ENNReal}
    (hF : (C.intervalScaleCover (S.tau m) (S.theta m)
      (S.delta_le_tau m) (S.tau_le_theta m)
      (S.theta_le_one m)).IsFrostmanAtScale error) :
    fiberDeltaMax
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m)
          (S.theta_le_one m)) ≤
      error * actualParentFiberMassLoss
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m)
          (S.theta_le_one m)) := by
  have htau : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  apply
    Family8NormalizedCFDividingWitnessActualCoverBridgeV3.StickyScaleCover.fiberDeltaMax_le_error_mul_actualParentLoss_of_isFrostmanAtScale
      _ htau _ hF
  exact htau.trans_le (S.tau_le_theta m)

/-- At every legal intermediate radius, the literal interval cover used by
the witness admits the same normalization transport. -/
theorem actualDatum_tauToRho_fiberDeltaMax_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (rho : NNReal) (htauRho : S.tau m ≤ rho) (hrhoOne : rho ≤ 1)
    {error : ENNReal}
    (hF : (C.intervalScaleCover (S.tau m) rho
      (S.delta_le_tau m) htauRho hrhoOne).IsFrostmanAtScale error) :
    fiberDeltaMax
        (C.intervalScaleCover (S.tau m) rho
          (S.delta_le_tau m) htauRho hrhoOne) ≤
      error * actualParentFiberMassLoss
        (C.intervalScaleCover (S.tau m) rho
          (S.delta_le_tau m) htauRho hrhoOne) := by
  have htau : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  exact Family8NormalizedCFDividingWitnessActualCoverBridgeV3.StickyScaleCover.fiberDeltaMax_le_error_mul_actualParentLoss_of_isFrostmanAtScale
    _ htau (htau.trans_le htauRho) hF

#print axioms actualDatum_sourceToTau_fiberDeltaMax_le
#print axioms actualDatum_tauToTheta_fiberDeltaMax_le
#print axioms actualDatum_tauToRho_fiberDeltaMax_le

end CoherentStickyMultiscaleCover

end
end Family8NormalizedCFDividingWitnessActualCoverBridgeV3
