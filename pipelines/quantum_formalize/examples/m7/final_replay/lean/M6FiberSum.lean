import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
open scoped BigOperators
namespace M6.FiberSum
noncomputable def fiber {α β : Type} [Fintype α] (L : α → β) (b : β) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => L a = b)
noncomputable def pullbackSum {α β : Type} [Fintype α] (L : α → β) (w : β → Polynomial ℤ) : Polynomial ℤ :=
  ∑ a, w (L a)
noncomputable def fiberSum {α β : Type} [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ) : Polynomial ℤ :=
  ∑ b, Polynomial.C ((fiber L b).card : ℤ) * w b
def UniformFibers {α β : Type} [Fintype α] (L : α → β) (k : ℕ) : Prop :=
  ∀ b, (fiber L b).card = k
end M6.FiberSum
