import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8CanonicalBufferedGlobalRelativeScaleGainV1
import Mathlib.Tactic

/-!
# Tau-to-buffered ratio inputs from the normalized long core

The canonical ratio is nonzero, finite, and gains the long-interval
`delta^(epsilon^2)` power using only the core fields.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreTauActiveRatioPowerInputsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8CanonicalBufferedGlobalRelativeScaleGainV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Exact three-part input package for every relative-power consumer on the
core-native canonical `tau -> b` interval. -/
theorem canonicalBufferedTauActive_ratio_power_inputs
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S) :
    let q : ENNReal :=
      (S.tau W.m : ENNReal) / (canonicalBufferedRadius W : ENNReal)
    q ≠ 0 /\ q ≠ ∞ /\
      q <= (delta : ENNReal) ^ (P.epsilon ^ 2) := by
  dsimp only
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hb : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  constructor
  · exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr htau.ne', ENNReal.coe_ne_top⟩
  constructor
  · exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hb.ne')
  · rw [← ENNReal.coe_div hb.ne',
      ← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne', ENNReal.coe_le_coe]
    exact tau_div_canonicalLowerBufferedScale_le_rpow_sq
      hD.delta_pos (S.delta_le_tau W.m) (S.tau_le_theta W.m)
        P.epsilon_pos.le W.long

#print axioms canonicalBufferedTauActive_ratio_power_inputs

end
end Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
