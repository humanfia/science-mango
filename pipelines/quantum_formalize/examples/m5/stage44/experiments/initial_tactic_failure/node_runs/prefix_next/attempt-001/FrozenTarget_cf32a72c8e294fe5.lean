import M5PrefixPartition


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) (p q : List α) (a : α) (h : p.length < q.length), (p ++ [a]).IsPrefix q ↔ p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a
