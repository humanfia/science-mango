import FamilyStickyGrounding.FamilyStickyScaleChainDiscreteRefinementTreeV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainRootedRefinementTreeV1

open Submission.Kakeya.ConvexFactoring
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainAdjacentUpperProducerV1
open FamilyStickyScaleChainDiscreteRefinementTreeV1

noncomputable section

/-!
# Sticky Kakeya: terminal-interval rooted refinement trees

The discrete tree itself contains only ordered finite scales.  To localize a
continuous buffered scale inside a terminal interval, the only additional
scale facts needed are positivity of `tau_m` and identification of the root
with `tau_m`.  In particular, no enumeration/completeness statement about all
`NNReal` scales is stored.
-/

/-- A finite refinement tree rooted at the actual lower endpoint of each
terminal interval. -/
structure IntervalRootedRefinementScaleTree
    {delta : NNReal} {depth : Nat}
    (S : FiniteScaleSequence delta depth) where
  tree : DiscreteRefinementScaleTree depth
  tau_pos : forall m, 0 < S.tau m
  root_eq_tau : forall m,
    tree.scale m ⟨0, tree.levelCount_pos m⟩ = S.tau m

namespace IntervalRootedRefinementScaleTree

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {S : FiniteScaleSequence delta depth}
  (R : IntervalRootedRefinementScaleTree S)

include R

/-- Every node is at or above the terminal lower endpoint. -/
theorem tau_le_scale (m : Fin depth)
    (i : Fin (R.tree.levelCount m)) :
    S.tau m <= R.tree.scale m i := by
  rw [← R.root_eq_tau m]
  exact R.tree.scale_mono m (Nat.zero_le i.1)

/-- A buffered scale lies above `tau_m` whenever the buffer exponent is
nonnegative. -/
theorem tau_le_of_isBuffered (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    S.tau m <= rho := by
  have hbaseNN : 1 <= S.theta m / S.tau m :=
    (one_le_div (R.tau_pos m)).2 (S.tau_le_theta m)
  have hbaseE : (1 : ENNReal) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal)) := by
    exact_mod_cast hbaseNN
  have hfactor : (1 : ENNReal) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon) := by
    have hpow := ENNReal.rpow_le_rpow hbaseE hepsilon
    simpa using hpow
  have htauE : (S.tau m : ENNReal) <= (rho : ENNReal) := by
    calc
      (S.tau m : ENNReal) = (S.tau m : ENNReal) * 1 := by simp
      _ <= (S.tau m : ENNReal) *
          (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon) := by
        gcongr
      _ <= (rho : ENNReal) := hrho.1
  exact ENNReal.coe_le_coe.mp htauE

omit R in
/-- A buffered scale lies below `theta_m` under the same sign condition. -/
theorem le_theta_of_isBuffered (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    rho <= S.theta m := by
  have hratioNN : S.tau m / S.theta m <= 1 :=
    div_le_one_of_le₀ (S.tau_le_theta m) bot_le
  have hratioE :
      (((S.tau m / S.theta m : NNReal) : ENNReal)) <= 1 := by
    exact_mod_cast hratioNN
  have hfactor :
      (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) <= 1 :=
    ENNReal.rpow_le_one hratioE hepsilon
  have hrhoE : (rho : ENNReal) <= (S.theta m : ENNReal) := by
    calc
      (rho : ENNReal) <= (S.theta m : ENNReal) *
          (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) := hrho.2
      _ <= (S.theta m : ENNReal) * 1 := by gcongr
      _ = (S.theta m : ENNReal) := by simp
  exact ENNReal.coe_le_coe.mp hrhoE

omit R in
/-- Hence every buffered scale is a legal scale for the interval's actual
multiscale cover. -/
theorem le_one_of_isBuffered (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    rho <= 1 :=
  (le_theta_of_isBuffered hepsilon m rho hrho).trans (S.theta_le_one m)

/-- The rooted tree always has at least one node no larger than a buffered
continuous scale. -/
theorem root_le_of_isBuffered (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    R.tree.scale m ⟨0, R.tree.levelCount_pos m⟩ <= rho := by
  rw [R.root_eq_tau m]
  exact R.tau_le_of_isBuffered hepsilon m rho hrho

/-- The located node is between `tau_m` and the input buffered scale. -/
theorem located_scale_mem_interval (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal) (hrho : S.IsBuffered epsilon m rho) :
    S.tau m <= R.tree.scale m (R.tree.locate m rho) ∧
      R.tree.scale m (R.tree.locate m rho) <= rho := by
  exact ⟨R.tau_le_scale m _,
    R.tree.locate_scale_le m rho
      (R.root_le_of_isBuffered hepsilon m rho hrho)⟩

/-- Localization produces membership in the finite candidate image without
claiming that the continuous scale itself is a candidate. -/
theorem located_scale_mem_candidates
    (m : Fin depth) (rho : NNReal) :
    R.tree.scale m (R.tree.locate m rho) ∈
      R.tree.candidateScales m :=
  R.tree.locate_scale_mem_candidateScales m rho

end IntervalRootedRefinementScaleTree

variable {delta : NNReal} {outerDepth adjacentDepth : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {A : ActualIntervalCovers S}

/-- Existing adjacent buffered hierarchies produce rooted trees once their
single missing endpoint normalization is supplied.  The effective root has
zero accumulated buffer, so no further geometric assumption is needed. -/
def rootedTreeOfAdjacentBufferedHierarchy
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (tau_pos : forall m, 0 < S.tau m)
    (nominalRoot_eq_tau : forall m, G.nominalRadius m 0 = S.tau m) :
    IntervalRootedRefinementScaleTree S where
  tree := ofAdjacentBufferedHierarchy G
  tau_pos := tau_pos
  root_eq_tau := by
    intro m
    change (G.hierarchy m).effectiveRadius 0 = S.tau m
    rw [MultiscaleTubeHierarchy.effectiveRadius,
      MultiscaleTubeHierarchy.accumulatedBuffer_zero, add_zero,
      nominalRoot_eq_tau m]

#print axioms IntervalRootedRefinementScaleTree.tau_le_scale
#print axioms IntervalRootedRefinementScaleTree.tau_le_of_isBuffered
#print axioms IntervalRootedRefinementScaleTree.le_theta_of_isBuffered
#print axioms IntervalRootedRefinementScaleTree.le_one_of_isBuffered
#print axioms IntervalRootedRefinementScaleTree.located_scale_mem_interval
#print axioms IntervalRootedRefinementScaleTree.located_scale_mem_candidates
#print axioms rootedTreeOfAdjacentBufferedHierarchy

end
end FamilyStickyScaleChainRootedRefinementTreeV1
