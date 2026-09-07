import FamilyStickyGrounding.FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
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

namespace Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyHierarchyEndpointNonemptyProducerV1
open Family8CanonicalLowerBufferedScaleV4
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Identified first-long witness at its canonical buffered scale

For the identified interval `tau -> theta`, this module constructs both the
global `delta -> b` and interval `tau -> b` covers at the canonical buffered
radius `b`.  Coherence makes their actual coarse family, active parent set,
and normalized parent count `b^2 |T_b|` definitionally equal.  The interval
view retains the witness's actual middle `fiberDeltaMax` lower bound.

No Frostman constant, Katz--Tao estimate, or bootstrap conclusion is assumed.
-/

namespace Witness

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

def canonicalBufferedRadius
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S) : NNReal :=
  canonicalLowerBufferedScale (S.tau W.m) (S.theta W.m) epsilon

theorem canonicalBufferedRadius_isBuffered
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    S.IsBuffered epsilon W.m (canonicalBufferedRadius W) := by
  exact canonicalLowerBufferedScale_isBuffered S W.m hdelta
    hepsilon hepsilonHalf

theorem tau_le_canonicalBufferedRadius
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    S.tau W.m <= canonicalBufferedRadius W := by
  exact canonicalLowerBufferedScale_ge_tau
    (hdelta.trans_le (S.delta_le_tau W.m))
    (S.tau_le_theta W.m) hepsilon

theorem canonicalBufferedRadius_le_theta
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedRadius W <= S.theta W.m := by
  exact IntervalRootedRefinementScaleTree.le_theta_of_isBuffered
    hepsilon W.m (canonicalBufferedRadius W)
      (canonicalBufferedRadius_isBuffered W hdelta hepsilon hepsilonHalf)

theorem canonicalBufferedRadius_le_one
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    canonicalBufferedRadius W <= 1 :=
  (canonicalBufferedRadius_le_theta W hdelta hepsilon hepsilonHalf).trans
    (S.theta_le_one W.m)

theorem canonicalBufferedRadius_pos
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    0 < canonicalBufferedRadius W :=
  (hdelta.trans_le (S.delta_le_tau W.m)).trans_le
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)

/-- The global `delta -> b` cover whose active parents are the paper `T_b`. -/
def canonicalBufferedGlobalCover
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    StickyScaleCover fine (canonicalBufferedRadius W) :=
  lowerScaleCover C S W.m (canonicalBufferedRadius W)
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)
    (canonicalBufferedRadius_le_theta W hdelta hepsilon hepsilonHalf)

/-- The interval `tau -> b` view of the same parents. -/
def canonicalBufferedIntervalCover
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
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
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf).coarse =
      (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf).coarse := by
  rfl

theorem canonicalBufferedIntervalCover_activeCoarse_eq_global
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf).activeCoarse =
      (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf).activeCoarse := by
  rfl

theorem canonicalBufferedIntervalCover_cardScaleMass_eq_global
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    activeCoarseCardScaleMass
        (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf) =
      activeCoarseCardScaleMass
        (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf) := by
  rfl

theorem canonicalBufferedIntervalCover_fiberDeltaMax_lower
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    ((((canonicalBufferedRadius W) / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage) <=
      FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover.fiberDeltaMax
        (canonicalBufferedIntervalCover W hdelta hepsilon hepsilonHalf) := by
  have hmiddle := W.middle_lower (canonicalBufferedRadius W)
    (canonicalBufferedRadius_isBuffered W hdelta hepsilon hepsilonHalf)
  change
    ((((canonicalBufferedRadius W) / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage) <=
      W.toFrostmanDividingWitness.middleValue (canonicalBufferedRadius W)
    at hmiddle
  have heq := W.toFrostmanDividingWitness_middleValue
    (canonicalBufferedRadius W)
    (tau_le_canonicalBufferedRadius W hdelta hepsilon)
    (canonicalBufferedRadius_le_one W hdelta hepsilon hepsilonHalf)
  rw [heq] at hmiddle
  simpa only [canonicalBufferedIntervalCover] using hmiddle

theorem canonicalBufferedGlobalCover_activeCoarse_nonempty
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
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
#print axioms canonicalBufferedIntervalCover_fiberDeltaMax_lower
#print axioms canonicalBufferedGlobalCover_activeCoarse_nonempty

end Witness

end
end Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
