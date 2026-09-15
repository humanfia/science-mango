import M6Euclid

noncomputable def M6.EuclidTarget.binary_normalization : Prop :=
  ∀ p : M6.Euclid.BP, (p ≠ 0 → p.Monic) ∧ normalize p = p

#check M6.EuclidTarget.binary_normalization

noncomputable def M6.EuclidTarget.rank_order : Prop :=
  ∀ p q : M6.Euclid.BP, (M6.Euclid.rank p < M6.Euclid.rank q ↔ p.degree < q.degree) ∧ (M6.Euclid.rank p ≤ M6.Euclid.rank q ↔ p.degree ≤ q.degree)

#check M6.EuclidTarget.rank_order

noncomputable def M6.EuclidTarget.cancel_drop : Prop :=
  ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p

#check M6.EuclidTarget.cancel_drop

noncomputable def M6.EuclidTarget.cancel_mod : Prop :=
  ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q

#check M6.EuclidTarget.cancel_mod

noncomputable def M6.EuclidTarget.remainder_aux_correct : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ fuel → (M6.Euclid.remainderAux fuel p q).value = p % q ∧ (M6.Euclid.remainderAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.remainderAux fuel p q).value ≤ M6.Euclid.rank p

#check M6.EuclidTarget.remainder_aux_correct

noncomputable def M6.EuclidTarget.remainder_correct : Prop :=
  ∀ p q : M6.Euclid.BP, (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p ∧ (q ≠ 0 → M6.Euclid.rank (M6.Euclid.remainder p q).value < M6.Euclid.rank q)

#check M6.EuclidTarget.remainder_correct

noncomputable def M6.EuclidTarget.euclid_aux_correct : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank q < fuel → (M6.Euclid.euclidAux fuel p q).value = EuclideanDomain.gcd q p ∧ (M6.Euclid.euclidAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclidAux fuel p q).rounds ≤ M6.Euclid.rank q

#check M6.EuclidTarget.euclid_aux_correct

noncomputable def M6.EuclidTarget.normalized_gcd : Prop :=
  ∀ p q : M6.Euclid.BP, EuclideanDomain.gcd q p = GCDMonoid.gcd p q

#check M6.EuclidTarget.normalized_gcd

noncomputable def M6.EuclidTarget.euclid_correct : Prop :=
  ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).value = GCDMonoid.gcd p q ∧ (M6.Euclid.euclid p q).cancellations ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclid p q).rounds ≤ M6.Euclid.rank q

#check M6.EuclidTarget.euclid_correct

noncomputable def M6.EuclidTarget.remainder_passes : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP), (M6.Euclid.remainderAux fuel p q).passes = 2 * (M6.Euclid.remainderAux fuel p q).cancellations + 1

#check M6.EuclidTarget.remainder_passes

noncomputable def M6.EuclidTarget.euclid_aux_passes : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP), (M6.Euclid.euclidAux fuel p q).passes = 2 * (M6.Euclid.euclidAux fuel p q).cancellations + 3 * (M6.Euclid.euclidAux fuel p q).rounds + 1

#check M6.EuclidTarget.euclid_aux_passes

noncomputable def M6.EuclidTarget.euclid_passes : Prop :=
  ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).passes = 2 * (M6.Euclid.euclid p q).cancellations + 3 * (M6.Euclid.euclid p q).rounds + 2

#check M6.EuclidTarget.euclid_passes

noncomputable def M6.EuclidTarget.scan_cost : Prop :=
  ∀ width : ℕ, M6.Euclid.scanCost width = width * (6 * width + 4) ∧ (0 < width → M6.Euclid.scanCost width ≤ 10 * width ^ 2)

#check M6.EuclidTarget.scan_cost

noncomputable def M6.EuclidTarget.dense_cancel : Prop :=
  ∀ (N : ℕ) (p q : M6.Euclid.BP), p ≠ 0 → M6.Euclid.dense N (M6.Euclid.cancel p q) = M6.Euclid.denseXor N p q (p.natDegree - q.natDegree)

#check M6.EuclidTarget.dense_cancel

noncomputable def M6.EuclidTarget.dense_rank : Prop :=
  ∀ (width : ℕ) (p : M6.Euclid.BP), M6.Euclid.rank p ≤ width → M6.Euclid.scanRank width p = M6.Euclid.rank p

#check M6.EuclidTarget.dense_rank

noncomputable def M6.EuclidTarget.dense_injective : Prop :=
  ∀ (N : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ N + 1 → M6.Euclid.rank q ≤ N + 1 → M6.Euclid.dense N p = M6.Euclid.dense N q → p = q

#check M6.EuclidTarget.dense_injective

noncomputable def M6.EuclidTarget.remainder_safe : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.remainderSafe fuel p q width

#check M6.EuclidTarget.remainder_safe

noncomputable def M6.EuclidTarget.euclid_safe : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.euclidSafe fuel p q width

#check M6.EuclidTarget.euclid_safe

noncomputable def M6.EuclidTarget.euclid_output_width : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ max (M6.Euclid.rank p) (M6.Euclid.rank q)

#check M6.EuclidTarget.euclid_output_width

noncomputable def M6.EuclidTarget.bit_cost_bound : Prop :=
  ∀ (N : ℕ) (p q : M6.Euclid.BP), p.natDegree ≤ N → q.natDegree ≤ N → M6.Euclid.bitCost N p q ≤ 90 * (N + 1) ^ 3 ∧ M6.Euclid.euclidSafe (M6.Euclid.rank q + 1) p q (N + 1)

#check M6.EuclidTarget.bit_cost_bound

noncomputable def M6.EuclidTarget.preprocess_correct_cost : Prop :=
  ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → (M6.Euclid.preprocess a b M).value = GCDMonoid.gcd (GCDMonoid.gcd a b) M ∧ M6.Euclid.preprocessBitCost N a b M ≤ 180 * (N + 1) ^ 3

#check M6.EuclidTarget.preprocess_correct_cost

