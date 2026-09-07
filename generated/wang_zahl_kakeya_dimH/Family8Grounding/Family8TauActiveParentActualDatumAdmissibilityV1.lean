import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Mathlib.Tactic

/-!
# Admissibility of the literal tau-active parent datum

The active-parent datum used by the greedy high-occurrence interface is
definitionally the canonical tau-active coarse datum when the cover is the
literal `tauScaleCover`.  Thus the existing two-field
`TauActiveCoarseAdmissibility` certificate supplies exactly its geometry.

No buffered parent, fresh restriction, reindexing, or equality premise is
introduced here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8TauActiveParentActualDatumAdmissibilityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The greedy interface's literal active-parent datum at `tau_m` is
admissible from the canonical tau-active geometry certificate. -/
theorem activeParentActualTubeDatum_tauScaleCover_isAdmissible
    (D : ActualTubeDatum delta index) (hdeltaPos : 0 < delta)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (hgeometry : TauActiveCoarseAdmissibility D C S W) :
    (activeParentActualTubeDatum
      (tauScaleCover D C S W) D.shading).IsAdmissible := by
  exact
    { delta_pos := hdeltaPos.trans_le (S.delta_le_tau W.m)
      delta_le_half := htauHalf
      contained_in_unit_ball := hgeometry.contained_in_unit_ball
      pairwise_essentiallyDistinct :=
        hgeometry.pairwise_essentiallyDistinct }

#print axioms activeParentActualTubeDatum_tauScaleCover_isAdmissible

end
end Family8TauActiveParentActualDatumAdmissibilityV1
