import Family8Grounding.Family8NormalizedLongIntervalWitnessV1
import FamilyStickyGrounding.FamilyStickyScaleChainArbitraryRadiusInterpolationV1
import FamilyStickyGrounding.FamilyStickyScaleChainRootedRefinementTreeV1
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointNonemptyProducerV1
import Family8Grounding.Family8CanonicalLowerBufferedScaleV4
import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalCanonicalBufferedCoverV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyHierarchyEndpointNonemptyProducerV1
open Family8CanonicalLowerBufferedScaleV4
open Family8NormalizedLongIntervalWitnessV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# A normalized first-long witness at its canonical buffered scale

The selected node and both coherent covers are the same geometric objects as
in the older absolute-witness route.  The lower estimate is deliberately
stated for `parentNormalizedFiberCFMax`, exactly as returned by the finite
selector.  No conversion to absolute `fiberDeltaMax` is made here.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

def canonicalBufferedRadius
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S) : NNReal :=
  canonicalLowerBufferedScale (S.tau W.m) (S.theta W.m) epsilon

theorem canonicalBufferedRadius_isBuffered
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    S.IsBuffered epsilon W.m (canonicalBufferedRadius W) := by
  exact canonicalLowerBufferedScale_isBuffered S W.m hdelta
    hepsilon hepsilonHalf

theorem tau_le_canonicalBufferedRadius
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    S.tau W.m <= canonicalBufferedRadius W := by
  exact canonicalLowerBufferedScale_ge_tau
    (hdelta.trans_le (S.delta_le_tau W.m))
    (S.tau_le_theta W.m) hepsilon

theorem canonicalBufferedRadius_le_theta
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedRadius W <= S.theta W.m := by
  exact IntervalRootedRefinementScaleTree.le_theta_of_isBuffered
    hepsilon W.m (canonicalBufferedRadius W)
      (canonicalBufferedRadius_isBuffered W hdelta hepsilon hepsilonHalf)

theorem canonicalBufferedRadius_le_one
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedRadius W <= 1 :=
  (canonicalBufferedRadius_le_theta W hdelta hepsilon hepsilonHalf).trans
    (S.theta_le_one W.m)

theorem canonicalBufferedRadius_pos
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    0 < canonicalBufferedRadius W :=
  (hdelta.trans_le (S.delta_le_tau W.m)).trans_le
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)

/-- The global `delta -> b` cover whose active parents are the paper `T_b`. -/
def canonicalBufferedGlobalCover
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    StickyScaleCover fine (canonicalBufferedRadius W) :=
  lowerScaleCover C S W.m (canonicalBufferedRadius W)
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)
    (canonicalBufferedRadius_le_theta W hdelta hepsilon hepsilonHalf)

/-- The interval `tau -> b` view of the same parents. -/
def canonicalBufferedIntervalCover
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
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

theorem canonicalBufferedIntervalCover_coarse_eq_global
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf).coarse =
      (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf).coarse := by
  rfl

theorem canonicalBufferedIntervalCover_activeCoarse_eq_global
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf).activeCoarse =
      (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf).activeCoarse := by
  rfl

theorem canonicalBufferedIntervalCover_cardScaleMass_eq_global
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    activeCoarseCardScaleMass
        (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf) =
      activeCoarseCardScaleMass
        (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf) := by
  rfl

/-- The selector's literal middle lower barrier at the canonical buffered
radius, kept in its parent-normalized form. -/
theorem canonicalBufferedIntervalCover_parentNormalizedFiberCFMax_lower
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    ((((canonicalBufferedRadius W) / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage) <=
      Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover.parentNormalizedFiberCFMax
        (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf) := by
  have hmiddle := W.middle_lower (canonicalBufferedRadius W)
    (canonicalBufferedRadius_isBuffered W hdelta hepsilon hepsilonHalf)
  rw [normalizedFiberCFValueAt_eq C S W.m (canonicalBufferedRadius W)
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)
    (canonicalBufferedRadius_le_one W hdelta hepsilon hepsilonHalf)] at hmiddle
  simpa only [canonicalBufferedIntervalCover] using hmiddle

theorem canonicalBufferedGlobalCover_activeCoarse_nonempty
    (W : NormalizedLongIntervalWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2)
    (hfine : fine.refinement.refined.Nonempty) :
    (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf).activeCoarse.Nonempty :=
  StickyScaleCover.activeCoarse_nonempty_of_refined_nonempty _ hfine

#print axioms canonicalBufferedRadius_isBuffered
#print axioms tau_le_canonicalBufferedRadius
#print axioms canonicalBufferedRadius_le_theta
#print axioms canonicalBufferedGlobalCover
#print axioms canonicalBufferedIntervalCover
#print axioms canonicalBufferedIntervalCover_coarse_eq_global
#print axioms canonicalBufferedIntervalCover_activeCoarse_eq_global
#print axioms canonicalBufferedIntervalCover_cardScaleMass_eq_global
#print axioms
  canonicalBufferedIntervalCover_parentNormalizedFiberCFMax_lower
#print axioms canonicalBufferedGlobalCover_activeCoarse_nonempty

end Witness

end
end Family8NormalizedLongIntervalCanonicalBufferedCoverV1
