import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import Mathlib.Tactic

/-!
# Absolute canonical buffered-scale bound on a normalized long core, V3

V1 and V2 are failed drafts and are not imported.  The core witness retains
the longness inequality, exactly the field needed here.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreCanonicalBufferedAbsoluteScaleV3

open Submission.Kakeya.Uniformity
open Family8CanonicalLowerBufferedScaleV4
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat → Real}
  {S : FiniteScaleSequence delta depth}

/-- The canonical lower buffered scale of a core long interval satisfies the
same absolute bound as the fuller witness types. -/
theorem canonicalBufferedRadius_le_delta_rpow_mul_one_sub
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedRadius W <= delta ^ (epsilon * (1 - epsilon)) := by
  have hlong := W.long
  change (S.tau W.m : ENNReal) <=
      (delta : ENNReal) ^ epsilon * (S.theta W.m : ENNReal) at hlong
  have hlongNN : S.tau W.m <=
      delta ^ epsilon * S.theta W.m := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' epsilon,
      ← ENNReal.coe_mul] at hlong
    exact ENNReal.coe_le_coe.mp hlong
  have htauDelta : S.tau W.m <= delta ^ epsilon := by
    calc
      S.tau W.m <= delta ^ epsilon * S.theta W.m := hlongNN
      _ <= delta ^ epsilon * 1 :=
        mul_le_mul_of_nonneg_left (S.theta_le_one W.m) (by positivity)
      _ = delta ^ epsilon := mul_one _
  have hrhoTau : canonicalBufferedRadius W <=
      (S.tau W.m) ^ (1 - epsilon) := by
    simpa only [canonicalBufferedRadius] using
      (canonicalLowerBufferedScale_le_tau_rpow_one_sub
        (S.theta_le_one W.m) hepsilon)
  have honeSub : 0 <= 1 - epsilon := by linarith
  calc
    canonicalBufferedRadius W <= (S.tau W.m) ^ (1 - epsilon) := hrhoTau
    _ <= (delta ^ epsilon) ^ (1 - epsilon) :=
      NNReal.rpow_le_rpow htauDelta honeSub
    _ = delta ^ (epsilon * (1 - epsilon)) :=
      (NNReal.rpow_mul delta epsilon (1 - epsilon)).symm

#print axioms canonicalBufferedRadius_le_delta_rpow_mul_one_sub

end
end Family8NormalizedLongCoreCanonicalBufferedAbsoluteScaleV3
