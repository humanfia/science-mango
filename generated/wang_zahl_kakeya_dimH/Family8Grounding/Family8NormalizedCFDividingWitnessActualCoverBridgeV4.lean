import Family8Grounding.Family8NormalizedCFDividingWitnessActualCoverBridgeV3
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV4

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedCFDividingWitnessActualCoverBridgeV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessBridgeV4.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Actual-cover lower normalization for the three dividing values

This file specializes the geometric parent-fibre mass floor to the literal
source-to-`tau`, `tau`-to-`theta`, and buffered `tau`-to-`rho` covers used by
the identified dividing witness.  Each conclusion mentions only computed
quantities of the actual cover.  In particular, no lower concentration
estimate is passed as a theorem-valued premise.
-/

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- Honest lower normalization for the literal source-to-`tau_m` cover. -/
theorem actualDatum_sourceToTau_parentNormalizedCFMax_mul_floor_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (htauHalf : S.tau m <= (2 : NNReal)⁻¹) :
    parentNormalizedFiberCFMax
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) *
        parentFiberMassRatioFloor delta (S.tau m) <=
      fiberDeltaMax
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) := by
  apply parentNormalizedFiberCFMax_mul_floor_le_fiberDeltaMax
  · exact hD.delta_pos
  · exact hD.delta_pos.trans_le (S.delta_le_tau m)
  · exact hD.delta_le_half
  · exact htauHalf

/-- Honest lower normalization for the literal adjacent
`tau_m`-to-`theta_m` cover. -/
theorem actualDatum_tauToTheta_parentNormalizedCFMax_mul_floor_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (htauHalf : S.tau m <= (2 : NNReal)⁻¹)
    (hthetaHalf : S.theta m <= (2 : NNReal)⁻¹) :
    parentNormalizedFiberCFMax
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m)
          (S.theta_le_one m)) *
        parentFiberMassRatioFloor (S.tau m) (S.theta m) <=
      fiberDeltaMax
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m)
          (S.theta_le_one m)) := by
  have htau : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  apply parentNormalizedFiberCFMax_mul_floor_le_fiberDeltaMax
  · exact htau
  · exact htau.trans_le (S.tau_le_theta m)
  · exact htauHalf
  · exact hthetaHalf

/-- Honest lower normalization at every literal buffered intermediate
`tau_m`-to-`rho` cover. -/
theorem actualDatum_tauToRho_parentNormalizedCFMax_mul_floor_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (rho : NNReal) (htauRho : S.tau m <= rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    parentNormalizedFiberCFMax
        (C.intervalScaleCover (S.tau m) rho
          (S.delta_le_tau m) htauRho (hrhoHalf.trans (by norm_num))) *
        parentFiberMassRatioFloor (S.tau m) rho <=
      fiberDeltaMax
        (C.intervalScaleCover (S.tau m) rho
          (S.delta_le_tau m) htauRho (hrhoHalf.trans (by norm_num))) := by
  have htau : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  apply parentNormalizedFiberCFMax_mul_floor_le_fiberDeltaMax
  · exact htau
  · exact htau.trans_le htauRho
  · exact (htauRho.trans hrhoHalf)
  · exact hrhoHalf

#print axioms actualDatum_sourceToTau_parentNormalizedCFMax_mul_floor_le
#print axioms actualDatum_tauToTheta_parentNormalizedCFMax_mul_floor_le
#print axioms actualDatum_tauToRho_parentNormalizedCFMax_mul_floor_le

end CoherentStickyMultiscaleCover

end
end Family8NormalizedCFDividingWitnessActualCoverBridgeV4
