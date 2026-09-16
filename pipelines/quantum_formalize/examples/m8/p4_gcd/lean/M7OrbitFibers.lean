import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
open scoped BigOperators
namespace M7.OrbitFibers
/-- Semantic finite orbit; it is not the production numerator evaluator. -/
noncomputable def orbit (G : Type) [Group G] [Fintype G] {X : Type} [MulAction G X] (c : X) : Finset X := by
  classical
  exact Finset.univ.image (fun g : G => g • c)
noncomputable def stabilizerCount (G : Type) [Group G] [Fintype G] {X : Type} [MulAction G X] (c : X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun g : G => g • c = c)).card
noncomputable def fiberCount (G : Type) [Group G] [Fintype G] {X : Type} [MulAction G X] (c y : X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun g : G => g • c = y)).card
noncomputable def actionCount (G : Type) [Group G] [Fintype G] {X : Type} [MulAction G X] (c : X) (P : X → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun g : G => P (g • c))).card
noncomputable def orbitCount (G : Type) [Group G] [Fintype G] {X : Type} [MulAction G X] (c : X) (P : X → Prop) : ℕ := by
  classical
  exact ((orbit G c).filter P).card
end M7.OrbitFibers
