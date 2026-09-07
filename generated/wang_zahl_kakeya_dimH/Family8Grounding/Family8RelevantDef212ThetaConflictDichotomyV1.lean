import Family8Grounding.Family8RelevantDef212NoConflictProducerV1
import Mathlib.Tactic

/-!
# Relevant Definition 2.12 versus a literal doubled-parent conflict

For the finitely many upper endpoint covers which can become long terminal
intervals, either every pair of distinct active parents is conflict-free or
one literal doubled-parent conflict is present.  In the first alternative the
automatic finite producer supplies all relevant Definition 2.12 inputs.  The
second alternative deliberately retains the exact scale, parents, and common
fine tube needed by the geometric conflict branch.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace Family8RelevantDef212ThetaConflictDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8DoubledParentPartitioningConflictIffV1.ScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalRelevantDef212InputsV5
open Family8RelevantDef212AutomaticNonpartitionProducerV1
open Family8RelevantDef212NoConflictProducerV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- One obstruction to the upper doubled-parent partitioning condition at a
relevant long interval.  All fields refer to the literal coherent upper
cover, so downstream conflict geometry does not need an equality transport. -/
structure RelevantThetaDoubledParentConflict
    {fine : UniformTubeFamily delta iota}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (epsilon : Real) where
  m : Fin depth
  long : S.IsLong epsilon m
  k : Fin (automaticThetaCover C S m).coarseCard
  l : Fin (automaticThetaCover C S m).coarseCard
  k_active : k ∈ (automaticThetaCover C S m).activeCoarse
  l_active : l ∈ (automaticThetaCover C S m).activeCoarse
  distinct : k ≠ l
  conflict : DoubledParentConflict (automaticThetaCover C S m) k l

/-- Exact finite dichotomy at the relevant upper endpoints: either the full
relevant Definition 2.12 package exists (with its honest data-dependent
constant), or there is a literal doubled-parent conflict on a long interval. -/
theorem exists_relevantDef212Inputs_or_thetaConflict
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (epsilon : Real) :
    (∃ K : NNReal,
        Nonempty (RelevantFiniteSequenceDef212Inputs C S epsilon K)) ∨
      Nonempty (RelevantThetaDoubledParentConflict C S epsilon) := by
  classical
  by_cases hconflict :
      ∃ (m : Fin depth), S.IsLong epsilon m ∧
        ∃ (k : Fin (automaticThetaCover C S m).coarseCard),
          k ∈ (automaticThetaCover C S m).activeCoarse ∧
          ∃ (l : Fin (automaticThetaCover C S m).coarseCard),
            l ∈ (automaticThetaCover C S m).activeCoarse ∧
            k ≠ l ∧
            DoubledParentConflict (automaticThetaCover C S m) k l
  · right
    obtain ⟨m, hlong, k, hk, l, hl, hkl, hcollision⟩ := hconflict
    exact ⟨{
      m := m
      long := hlong
      k := k
      l := l
      k_active := hk
      l_active := hl
      distinct := hkl
      conflict := hcollision }⟩
  · left
    apply exists_relevantFiniteSequenceDef212Inputs_of_theta_pairwise_noConflict
      D hD C S epsilon
    intro m hlong k hk l hl hkl hcollision
    exact hconflict ⟨m, hlong, k, hk, l, hl, hkl, hcollision⟩

#print axioms RelevantThetaDoubledParentConflict
#print axioms exists_relevantDef212Inputs_or_thetaConflict

end
end Family8RelevantDef212ThetaConflictDichotomyV1
