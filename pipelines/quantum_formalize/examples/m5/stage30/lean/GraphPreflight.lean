import M5OrderBoundary

noncomputable def preflight_range_card : Prop :=
  ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N

noncomputable def preflight_signature_lower_bounds : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F A B → M5.signaturePeriod F ∣ N ∧ w ≤ N ∧ F.natDegree < N

noncomputable def preflight_weight_one_iff : Prop :=
  ∀ (N : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), M5.PhysicalOrder.realizes N 1 F A B ↔ N = 1 ∧ F = 1 ∧ A = {0} ∧ B = {0}
