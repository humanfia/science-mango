import FrozenTarget_2545f846836a7571
theorem M7.QuotientDegree.adjoin_card : QuantumHarnessFrozenTarget := by
  change ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
  intro F hF
  calc
    Nat.card (AdjoinRoot F) = Nat.card (Fin F.natDegree → ZMod 2) :=
      Nat.card_congr (AdjoinRoot.powerBasis' hF).basis.equivFun.toEquiv
    _ = 2 ^ F.natDegree := by simp [Nat.card_eq_fintype_card]
