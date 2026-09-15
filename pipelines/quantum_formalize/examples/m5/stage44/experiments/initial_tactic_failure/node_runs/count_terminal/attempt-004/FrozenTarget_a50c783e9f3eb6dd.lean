import M5PrefixPartition


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length = m → M5.PrefixPartition.count W p = (if p ∈ W then 1 else 0)
