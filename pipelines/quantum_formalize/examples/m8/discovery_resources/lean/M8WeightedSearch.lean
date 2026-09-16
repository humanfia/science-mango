import M8FiniteSearchAccepted

namespace M8.WeightedSearch
structure Run (n : ℕ) (α : Type) where
  selected : Option (Fin n × α)
  calls : ℕ
  work : ℕ
/-- Calls and callback charges are accumulated only along the executed prefix. -/
def walk {n : ℕ} {α : Type} (f : Fin n → Option α × ℕ) (start : ℕ) : ℕ → Run n α
  | 0 => ⟨none,0,0⟩
  | fuel+1 => if h : start < n then
      let q := f ⟨start,h⟩
      match q.1 with
      | some a => ⟨some (⟨start,h⟩,a),1,q.2⟩
      | none => let r := walk f (start+1) fuel; ⟨r.selected,r.calls+1,q.2+r.work⟩
    else ⟨none,0,0⟩
def find {n : ℕ} {α : Type} (f : Fin n → Option α × ℕ) := walk f 0 n
end M8.WeightedSearch
