import FrozenTarget_64a1efa1bd5431b9
theorem M5.Period.quotient_cardinality : QuantumHarnessFrozenTarget := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
  intro F hF
  classical
  calc
    Nat.card (AdjoinRoot F) = Nat.card (Fin F.natDegree → ZMod 2) :=
      Nat.card_congr ((AdjoinRoot.powerBasisAux' hF).equivFun.toEquiv)
    _ = 2 ^ F.natDegree := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]
