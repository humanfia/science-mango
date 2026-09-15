import M7Factorized


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (S T : Type) [Fintype S] [Fintype T] (left : S → Prop) (right : T → Prop), M7.Factorized.count (fun p : S × T => left p.1 ∧ right p.2) = M7.Factorized.count left * M7.Factorized.count right
