import FamilyStickyGrounding.FamilyStickyScaleChainTerminalFiniteSearchV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainDiscreteRefinementTreeV1

open Submission.Kakeya.ConvexFactoring
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainAdjacentUpperProducerV1
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy

noncomputable section

/-!
# Sticky Kakeya: finite refinement-scale trees

This is the discrete, computable part of scale localization.  Each terminal
interval has finitely many ordered refinement levels.  Given an arbitrary
scale, `locate` selects the greatest level whose scale does not exceed it.
No concentration or exponent inequality is stored in the tree.
-/

/-- A finite ordered scale tree on every terminal interval.  Its underlying
tree is the chain `0 -> 1 -> ...`; this is the thinnest tree needed by the
paper's successive scale refinements. -/
structure DiscreteRefinementScaleTree (outerDepth : Nat) where
  levelCount : Fin outerDepth -> Nat
  levelCount_pos : forall m, 0 < levelCount m
  scale : (m : Fin outerDepth) -> Fin (levelCount m) -> NNReal
  scale_mono : forall m, Monotone (scale m)

namespace DiscreteRefinementScaleTree

variable {outerDepth : Nat}
  (T : DiscreteRefinementScaleTree outerDepth)

/-- All actual scales appearing as nodes of interval `m`. -/
def candidateScales (m : Fin outerDepth) : Finset NNReal :=
  Finset.univ.image (T.scale m)

/-- The next coarser node in the chain, when it exists. -/
def parentNode (m : Fin outerDepth) (i : Fin (T.levelCount m)) :
    Option (Fin (T.levelCount m)) :=
  if h : i.1 + 1 < T.levelCount m then some ⟨i.1 + 1, h⟩ else none

/-- Every available parent has no smaller scale. -/
theorem scale_le_parentNode (m : Fin outerDepth)
    (i j : Fin (T.levelCount m))
    (hparent : T.parentNode m i = some j) :
    T.scale m i <= T.scale m j := by
  unfold parentNode at hparent
  split at hparent
  next h =>
    have hj : (⟨i.1 + 1, h⟩ : Fin (T.levelCount m)) = j :=
      Option.some.inj hparent
    have hij : i <= (⟨i.1 + 1, h⟩ : Fin (T.levelCount m)) :=
      Nat.le_succ i.1
    exact (T.scale_mono m hij).trans_eq (congrArg (T.scale m) hj)
  next h =>
    exact (Option.some_ne_none j hparent.symm).elim

/-- Nodes whose scales are no larger than `rho`. -/
def lowerNodes (m : Fin outerDepth) (rho : NNReal) :
    Finset (Fin (T.levelCount m)) :=
  Finset.univ.filter fun i => T.scale m i <= rho

@[simp] theorem mem_lowerNodes (m : Fin outerDepth) (rho : NNReal)
    (i : Fin (T.levelCount m)) :
    i ∈ T.lowerNodes m rho <-> T.scale m i <= rho := by
  simp [lowerNodes]

/-- The root is the canonical witness that the lower-node set is nonempty. -/
theorem lowerNodes_nonempty_of_root_le (m : Fin outerDepth) (rho : NNReal)
    (hroot : T.scale m ⟨0, T.levelCount_pos m⟩ <= rho) :
    (T.lowerNodes m rho).Nonempty := by
  exact ⟨⟨0, T.levelCount_pos m⟩,
    (T.mem_lowerNodes m rho _).2 hroot⟩

/-- Canonical finite localization: the greatest refinement level at or below
`rho`, defaulting to the root only when no such level exists. -/
def locate (m : Fin outerDepth) (rho : NNReal) :
    Fin (T.levelCount m) :=
  if h : (T.lowerNodes m rho).Nonempty then
    (T.lowerNodes m rho).max' h
  else ⟨0, T.levelCount_pos m⟩

/-- Under the single root bound, the located node is genuinely admissible. -/
theorem locate_mem_lowerNodes (m : Fin outerDepth) (rho : NNReal)
    (hroot : T.scale m ⟨0, T.levelCount_pos m⟩ <= rho) :
    T.locate m rho ∈ T.lowerNodes m rho := by
  have hnonempty := T.lowerNodes_nonempty_of_root_le m rho hroot
  rw [locate, dif_pos hnonempty]
  exact Finset.max'_mem (T.lowerNodes m rho) hnonempty

/-- The scale chosen by the finite locator does not exceed the input scale. -/
theorem locate_scale_le (m : Fin outerDepth) (rho : NNReal)
    (hroot : T.scale m ⟨0, T.levelCount_pos m⟩ <= rho) :
    T.scale m (T.locate m rho) <= rho := by
  exact (T.mem_lowerNodes m rho _).1
    (T.locate_mem_lowerNodes m rho hroot)

/-- The locator has greatest level index among all nodes below `rho`. -/
theorem le_locate (m : Fin outerDepth) (rho : NNReal)
    (hroot : T.scale m ⟨0, T.levelCount_pos m⟩ <= rho)
    (i : Fin (T.levelCount m)) (hi : T.scale m i <= rho) :
    i <= T.locate m rho := by
  have hnonempty := T.lowerNodes_nonempty_of_root_le m rho hroot
  rw [locate, dif_pos hnonempty]
  exact Finset.le_max' (T.lowerNodes m rho) i
    ((T.mem_lowerNodes m rho i).2 hi)

/-- Every located scale belongs to the finite candidate-scale image. -/
theorem locate_scale_mem_candidateScales (m : Fin outerDepth) (rho : NNReal) :
    T.scale m (T.locate m rho) ∈ T.candidateScales m := by
  exact Finset.mem_image.mpr ⟨T.locate m rho, Finset.mem_univ _, rfl⟩

end DiscreteRefinementScaleTree

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*} [forall l, DecidableEq (Index l)]

/-- Effective radii are monotone along any finite hierarchy segment, not
only at one adjacent step. -/
theorem effectiveRadius_mono
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {a b : Nat} (hb : b <= depth) (hab : a <= b) :
    H.effectiveRadius a <= H.effectiveRadius b := by
  induction b with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases habEq : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a <= b := by omega
        exact (ih (by omega) hab').trans
          (H.effectiveRadius_step_le b (by omega))

end MultiscaleTubeHierarchy

variable {delta : NNReal} {outerDepth adjacentDepth : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {A : ActualIntervalCovers S}

/-- The effective radii of an actual adjacent buffered hierarchy form the
canonical finite refinement-scale tree. -/
def ofAdjacentBufferedHierarchy
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth) :
    DiscreteRefinementScaleTree outerDepth where
  levelCount := fun _ => adjacentDepth + 1
  levelCount_pos := by intro; omega
  scale := fun m i => (G.hierarchy m).effectiveRadius i.1
  scale_mono := by
    intro m i j hij
    exact MultiscaleTubeHierarchy.effectiveRadius_mono (G.hierarchy m)
      (Nat.le_of_lt_succ j.isLt) hij

@[simp] theorem ofAdjacentBufferedHierarchy_scale
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (m : Fin outerDepth) (i : Fin (adjacentDepth + 1)) :
    (ofAdjacentBufferedHierarchy G).scale m i =
      (G.hierarchy m).effectiveRadius i.1 := by
  rfl

#print axioms DiscreteRefinementScaleTree.scale_le_parentNode
#print axioms DiscreteRefinementScaleTree.locate_mem_lowerNodes
#print axioms DiscreteRefinementScaleTree.locate_scale_le
#print axioms DiscreteRefinementScaleTree.le_locate
#print axioms MultiscaleTubeHierarchy.effectiveRadius_mono
#print axioms ofAdjacentBufferedHierarchy

end
end FamilyStickyScaleChainDiscreteRefinementTreeV1
