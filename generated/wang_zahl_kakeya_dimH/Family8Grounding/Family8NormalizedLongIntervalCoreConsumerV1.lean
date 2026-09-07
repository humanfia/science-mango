import Family8Grounding.Family8BufferedNormalizedLongTerminalWitnessV1
import Family8Grounding.Family8NormalizedLongIntervalCanonicalBufferedCoverV1

/-!
# Common consumer core for raw and genuinely buffered long witnesses

All current canonical-buffer consumers of `NormalizedLongIntervalWitness`
use only the selected index, stage, longness, and middle lower barrier.  They
do not inspect either outside upper field.  This file factors exactly that
common data and supplies projections from both the legacy raw-theta witness
and the genuine selected-parent buffered witness.

The canonical buffered cover construction is then stated once on the common
core.  Thus downstream geometry can consume the honest buffered terminal
object without manufacturing a raw-theta adjacent estimate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalCoreConsumerV1

open Submission.Kakeya.Uniformity
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8CanonicalLowerBufferedScaleV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedLongIntervalWitnessV1
open Family8ParameterLadderV1
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointNonemptyProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainRootedRefinementTreeV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

/-- Precisely the fields read by the canonical middle-scale consumers. -/
structure NormalizedLongIntervalCoreWitness
    (fine : UniformTubeFamily delta iota)
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (epsilon : Real) (eta : Nat -> Real)
    (S : FiniteScaleSequence delta depth) where
  m : Fin depth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  long : S.IsLong epsilon m
  middle_lower : forall rho, S.IsBuffered epsilon m rho ->
    (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
      normalizedFiberCFValueAt C S m rho

namespace NormalizedLongIntervalCoreWitness

/-- Forget only the two outside upper estimates of the legacy witness. -/
def ofNormalized
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S) :
    NormalizedLongIntervalCoreWitness fine C N epsilon eta S where
  m := W.m
  stage := W.stage
  stage_pos := W.stage_pos
  stage_le := W.stage_le
  long := W.long
  middle_lower := W.middle_lower

/-- Forget only the source and adjacent upper fields of the genuine buffered
terminal witness.  The selected node and lower barrier are unchanged. -/
def ofBuffered
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (P : ParameterLadder epsilon0 beta gamma)
    (S : FiniteScaleSequence delta depth)
    (W : BufferedNormalizedLongTerminalWitness D C P S) :
    NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S where
  m := W.m
  stage := W.stage
  stage_pos := W.stage_pos
  stage_le := W.stage_le
  long := W.long
  middle_lower := W.middle_lower

/-- The paper's canonical scale in the selected long interval. -/
def canonicalBufferedRadius
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S) : NNReal :=
  canonicalLowerBufferedScale (S.tau W.m) (S.theta W.m) epsilon

theorem canonicalBufferedRadius_isBuffered
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    S.IsBuffered epsilon W.m (canonicalBufferedRadius W) := by
  exact canonicalLowerBufferedScale_isBuffered S W.m hdelta
    hepsilon hepsilonHalf

theorem tau_le_canonicalBufferedRadius
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    S.tau W.m <= canonicalBufferedRadius W := by
  exact canonicalLowerBufferedScale_ge_tau
    (hdelta.trans_le (S.delta_le_tau W.m))
    (S.tau_le_theta W.m) hepsilon

theorem canonicalBufferedRadius_le_theta
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedRadius W <= S.theta W.m := by
  exact IntervalRootedRefinementScaleTree.le_theta_of_isBuffered
    hepsilon W.m (canonicalBufferedRadius W)
      (canonicalBufferedRadius_isBuffered W hdelta hepsilon hepsilonHalf)

theorem canonicalBufferedRadius_le_one
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedRadius W <= 1 :=
  (canonicalBufferedRadius_le_theta W hdelta hepsilon hepsilonHalf).trans
    (S.theta_le_one W.m)

theorem canonicalBufferedRadius_pos
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    0 < canonicalBufferedRadius W :=
  (hdelta.trans_le (S.delta_le_tau W.m)).trans_le
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)

/-- The global `delta -> b` cover selected from the common witness core. -/
def canonicalBufferedGlobalCover
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    StickyScaleCover fine (canonicalBufferedRadius W) :=
  lowerScaleCover C S W.m (canonicalBufferedRadius W)
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)
    (canonicalBufferedRadius_le_theta W hdelta hepsilon hepsilonHalf)

/-- The literal `tau -> b` view of the same parents. -/
def canonicalBufferedIntervalCover
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    StickyScaleCover
      (C.base.cover (S.tau W.m) (S.delta_le_tau W.m)
        ((S.tau_le_theta W.m).trans (S.theta_le_one W.m))).coarse
      (canonicalBufferedRadius W) :=
  C.intervalScaleCover (S.tau W.m) (canonicalBufferedRadius W)
    (S.delta_le_tau W.m)
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)
    (canonicalBufferedRadius_le_one W hdelta hepsilon hepsilonHalf)

/-- The core's middle barrier on its literal canonical interval cover. -/
theorem canonicalBufferedIntervalCover_parentNormalizedFiberCFMax_lower
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    (((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage) <=
      parentNormalizedFiberCFMax
        (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf) := by
  have hmiddle := W.middle_lower (canonicalBufferedRadius W)
    (canonicalBufferedRadius_isBuffered W hdelta hepsilon hepsilonHalf)
  rw [normalizedFiberCFValueAt_eq C S W.m (canonicalBufferedRadius W)
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)
    (canonicalBufferedRadius_le_one W hdelta hepsilon hepsilonHalf)] at hmiddle
  simpa only [canonicalBufferedIntervalCover] using hmiddle

theorem canonicalBufferedGlobalCover_activeCoarse_nonempty
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2)
    (hfine : fine.refinement.refined.Nonempty) :
    (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf).activeCoarse.Nonempty :=
  StickyScaleCover.activeCoarse_nonempty_of_refined_nonempty _ hfine

#print axioms ofNormalized
#print axioms ofBuffered
#print axioms canonicalBufferedRadius_isBuffered
#print axioms canonicalBufferedGlobalCover
#print axioms canonicalBufferedIntervalCover
#print axioms canonicalBufferedIntervalCover_parentNormalizedFiberCFMax_lower
#print axioms canonicalBufferedGlobalCover_activeCoarse_nonempty

end NormalizedLongIntervalCoreWitness

end
end Family8NormalizedLongIntervalCoreConsumerV1
