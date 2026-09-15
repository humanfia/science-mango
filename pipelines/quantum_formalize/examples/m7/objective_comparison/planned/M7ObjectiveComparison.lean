import M7SelectionAccepted
namespace M7.ObjectiveComparison
/-- Actual sequential Pareto scan. Count one <= comparison, then one < comparison
only when <= succeeds; anyStrict records a strict coordinate already seen. -/
def paretoFrom {m : ℕ} (a b : Fin m → ℤ) (i : ℕ) : ℕ → Bool → Bool × ℕ
  | 0, anyStrict => (anyStrict, 0)
  | fuel + 1, anyStrict => if hi : i < m then
      if a ⟨i,hi⟩ ≤ b ⟨i,hi⟩ then
        let strict := decide (a ⟨i,hi⟩ < b ⟨i,hi⟩)
        let r := paretoFrom a b (i+1) fuel (anyStrict || strict)
        (r.1, 2+r.2)
      else (false, 1)
    else (anyStrict, 0)
/-- Actual first-unequal-coordinate scan; at most two integer comparisons per coordinate. -/
def lexFrom {m : ℕ} (a b : Fin m → ℤ) (i : ℕ) : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | fuel + 1 => if hi : i < m then
      if a ⟨i,hi⟩ < b ⟨i,hi⟩ then (true, 1)
      else if b ⟨i,hi⟩ < a ⟨i,hi⟩ then (false, 2)
      else let r := lexFrom a b (i+1) fuel; (r.1, 2+r.2)
    else (false, 0)
def compare {m : ℕ} (mode : M7.Selection.Mode) (a b : Fin m → ℤ) : Bool × ℕ :=
  match mode with
  | .pareto => paretoFrom a b 0 m false
  | .lex => lexFrom a b 0 m
end M7.ObjectiveComparison
