import Family8Grounding.Family8DoubledParentPartitioningConflictIffV1
import Family8Grounding.Family8RelevantDef212AutomaticNonpartitionProducerV1
import Mathlib.Tactic

/-!
# Relevant finite Definition 2.12 inputs from no doubled-parent conflicts

This is the geometric form of the last structural adapter.  Pairwise absence
of doubled-parent conflicts on every relevant upper endpoint produces the
literal partitioning field; all other finite Definition 2.12 fields are then
supplied automatically with one data-dependent constant.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace Family8RelevantDef212NoConflictProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8DoubledParentPartitioningConflictIffV1
open Family8DoubledParentPartitioningConflictIffV1.ScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalRelevantDef212InputsV5
open Family8RelevantDef212AutomaticNonpartitionProducerV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The exact no-conflict datum on the literal upper covers is sufficient to
construct all relevant finite Definition 2.12 inputs. -/
theorem exists_relevantFiniteSequenceDef212Inputs_of_theta_pairwise_noConflict
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (hnoConflict : ∀ m : Fin depth, S.IsLong epsilon m →
      Set.Pairwise
        (↑(automaticThetaCover C S m).activeCoarse :
          Set (Fin (automaticThetaCover C S m).coarseCard))
        (fun k l ↦
          ¬ DoubledParentConflict (automaticThetaCover C S m) k l)) :
    ∃ K : NNReal,
      Nonempty (RelevantFiniteSequenceDef212Inputs C S epsilon K) := by
  apply exists_relevantFiniteSequenceDef212Inputs_of_theta_partition
    D hD C S epsilon
  intro m hlong
  exact
    (isDoubledParentPartitioning_iff_pairwise_noDoubledParentConflict
      (automaticThetaCover C S m)).2 (hnoConflict m hlong)

#print axioms
  exists_relevantFiniteSequenceDef212Inputs_of_theta_pairwise_noConflict

end
end Family8RelevantDef212NoConflictProducerV1
