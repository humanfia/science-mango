import M5AnchoredTupleCount

noncomputable def preflight_anchored_tuple_divisibility : Prop :=
  ∀ (P : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ 1 + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = 1)

noncomputable def preflight_anchored_R_count : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ), M5.ArithmeticTuple.R P hP T d k 1 = (M5.AnchoredTupleCount.count P T d k : ℤ)

noncomputable def preflight_multiples_equivalence : Prop :=
  ∀ T d : ℕ, 0 < T → d ∣ T → ∃ e : Fin (T / d) ≃ {r : Fin T // d ∣ r.val}, ∀ j : Fin (T / d), (e j).val.val = d * j.val

noncomputable def preflight_restricted_R_count : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ), 0 < T → d ∣ T → M5.ArithmeticTuple.R P hP T d k 1 = (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ)
