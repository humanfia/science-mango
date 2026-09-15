import Mathlib.Data.List.Infix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
namespace M5.PrefixPartition
noncomputable def count {α : Type} (W : Finset (List α)) (p : List α) : ℤ := by
  classical
  exact ((W.filter (fun q => p.IsPrefix q)).card : ℤ)
end M5.PrefixPartition
