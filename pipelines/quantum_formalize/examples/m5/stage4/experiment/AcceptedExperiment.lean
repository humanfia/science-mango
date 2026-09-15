import M5Cardinality

theorem M5.Period.quotient_cardinality : ∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
  intro F hF
  classical
  calc
    Nat.card (AdjoinRoot F) = Nat.card (Fin F.natDegree → ZMod 2) :=
      Nat.card_congr ((AdjoinRoot.powerBasisAux' hF).equivFun.toEquiv)
    _ = 2 ^ F.natDegree := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem M5.Period.period_cardinality_bound : ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.signaturePeriod F ≤ 2 ^ F.natDegree := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.signaturePeriod F ≤ 2 ^ F.natDegree
  intro F hF h0
  letI : Finite (AdjoinRoot F) := M5.Period.quotient_finite F hF
  unfold M5.signaturePeriod
  calc
    orderOf (AdjoinRoot.root F) ≤ Nat.card (AdjoinRoot F) := orderOf_le_card
    _ = 2 ^ F.natDegree := M5.Period.quotient_cardinality F hF
#print axioms M5.Period.quotient_cardinality
#print axioms M5.Period.period_cardinality_bound
