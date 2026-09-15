import Mathlib

namespace M7.Selection

inductive Mode where
  | pareto
  | lex
  deriving DecidableEq

def pareto {m : ℕ} (a b : Fin m → ℤ) : Prop :=
  (∀ i, a i ≤ b i) ∧ ∃ i, a i < b i

def lex {m : ℕ} (a b : Fin m → ℤ) : Prop :=
  ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i

def better {m : ℕ} (mode : Mode) (a b : Fin m → ℤ) : Prop :=
  match mode with
  | .pareto => pareto a b
  | .lex => lex a b

noncomputable def feasibleSet {α : Type*} (S : Finset α) (feasible : α → Prop) : Finset α := by
  classical
  exact S.filter feasible

def win {α : Type*} (S : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α) : Prop :=
  x ∈ S ∧ feasible x ∧ ¬ ∃ y ∈ S, feasible y ∧ R y x

noncomputable def winners {α : Type*} (S : Finset α) (feasible : α → Prop) (R : α → α → Prop) : Finset α := by
  classical
  exact S.filter (win S feasible R)

noncomputable def select {α : Type*} {m : ℕ} (S : Finset α) (feasible : α → Prop)
    (objective : α → Fin m → ℤ) (mode : Mode) : Finset α :=
  winners S feasible (fun x y => better mode (objective x) (objective y))

end M7.Selection
