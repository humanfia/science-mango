import Family8Grounding.Family8StickyScaleCoverCFMaxHullChoiceV2
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreCFMaxHullChoiceV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8StickyScaleCoverCFMaxHullChoiceV2
open Family8StickyScaleCoverCFMaxHullChoiceV2.CFMaxHullChoice
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-!
# The normalized long barrier as a literal same-parent hull choice

This is a thin consumer of the compact generic `CFMaxHullChoice`.  The chosen
cover is exactly the canonical `tau -> b` interval cover of the normalized
long core, and the lower input is exactly `W.middle_lower` evaluated at the
canonical buffered radius.
-/

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

/-- The literal canonical interval cover has a compact worst-parent/winning
hull choice whenever the original active fine support is nonempty. -/
theorem canonicalBufferedInterval_cfMaxHullChoice_nonempty
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2)
    (hfine : fine.refinement.refined.Nonempty) :
    Nonempty (CFMaxHullChoice
      (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf)) := by
  apply cfMaxHullChoice_nonempty
  exact canonicalBufferedGlobalCover_activeCoarse_nonempty
    W hdelta hepsilon hepsilonHalf hfine

/-- A fixed compact choice, used so downstream projection theorems do not
re-elaborate a large existential package. -/
noncomputable def canonicalBufferedIntervalCFMaxHullChoice
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2)
    (hfine : fine.refinement.refined.Nonempty) :
    CFMaxHullChoice
      (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf) :=
  Classical.choice
    (canonicalBufferedInterval_cfMaxHullChoice_nonempty
      W hdelta hepsilon hepsilonHalf hfine)

/-- The core middle barrier supplies a genuine cross-multiplied mass lower
bound on one actual parent fibre and its actual winning convex hull. -/
theorem canonicalBufferedInterval_barrier_mul_fiberVolume_le_winner
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2)
    (hfine : fine.refinement.refined.Nonempty) :
    let I := canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf
    let Q := canonicalBufferedIntervalCFMaxHullChoice
      W hdelta hepsilon hepsilonHalf hfine
    ((((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
          eta W.stage) *
        familyVolume (I.fiberFamily Q.parent.1)) ≤
      densityInside (I.fiberFamily Q.parent.1) Finset.univ Q.hull *
        volume (I.activeCoarseFamily Q.parent : Set Space) := by
  dsimp only
  apply lower_mul_fiberVolume_le_winnerDensity_mul_parentVolume
    (canonicalBufferedIntervalCFMaxHullChoice
      W hdelta hepsilon hepsilonHalf hfine)
    (hdelta.trans_le (S.delta_le_tau W.m))
  exact canonicalBufferedIntervalCover_parentNormalizedFiberCFMax_lower
    W hdelta hepsilon hepsilonHalf

#print axioms canonicalBufferedInterval_cfMaxHullChoice_nonempty
#print axioms canonicalBufferedIntervalCFMaxHullChoice
#print axioms
  canonicalBufferedInterval_barrier_mul_fiberVolume_le_winner

end
end Family8NormalizedLongCoreCFMaxHullChoiceV2
