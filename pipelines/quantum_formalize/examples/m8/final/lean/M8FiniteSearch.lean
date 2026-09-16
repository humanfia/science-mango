import Mathlib

namespace M8.FiniteSearch
/-- Count actual tested indices; stop at the first value. No materialized index list. -/
def walk {n : ℕ} {α : Type} (f : Fin n → Option α) (start : ℕ) : ℕ → Option (Fin n × α) × ℕ
  | 0 => (none, 0)
  | fuel+1 => if h : start < n then
      match f ⟨start,h⟩ with
      | some a => (some (⟨start,h⟩,a), 1)
      | none => let r := walk f (start+1) fuel; (r.1, r.2+1)
    else (none, 0)
def find {n : ℕ} {α : Type} (f : Fin n → Option α) := walk f 0 n
def First {n : ℕ} {α : Type} (f : Fin n → Option α) (start fuel : ℕ) (i : Fin n) (a : α) : Prop :=
  start ≤ i.val ∧ i.val < start+fuel ∧ f i = some a ∧
    ∀ j : Fin n, start ≤ j.val → j.val < i.val → f j = none
end M8.FiniteSearch
