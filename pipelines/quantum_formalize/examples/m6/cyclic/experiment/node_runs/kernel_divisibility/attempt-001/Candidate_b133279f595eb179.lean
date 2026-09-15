import FrozenTarget_b133279f595eb179
theorem M6.Cyclic.kernel_divisibility : QuantumHarnessFrozenTarget := by
  change ∀ a b M h : M6.Cyclic.BinaryPolynomial, (M ∣ a * h ∧ M ∣ b * h) ↔ M ∣ M6.Cyclic.signature a b M * h
  intro a b M h
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨p, q, r, hs⟩ := M6.Cyclic.signature_bezout a b M
    refine ⟨p * x + q * y + r * h, ?_⟩
    calc
      M6.Cyclic.signature a b M * h = p * (a * h) + q * (b * h) + r * M * h := by rw [hs]; ring
      _ = M * (p * x + q * y + r * h) := by rw [hx, hy]; ring
  · rintro ⟨t, ht⟩
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, _⟩ := M6.Cyclic.signature_divides a b M
    constructor
    · refine ⟨t * u, ?_⟩
      calc
        a * h = (M6.Cyclic.signature a b M * h) * u := by rw [hu]; ring
        _ = M * (t * u) := by rw [ht]; ring
    · refine ⟨t * v, ?_⟩
      calc
        b * h = (M6.Cyclic.signature a b M * h) * v := by rw [hv]; ring
        _ = M * (t * v) := by rw [ht]; ring
