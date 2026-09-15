import FrozenTarget_f0f56c6c97c59f24
theorem M7.Factorized.pair_count : QuantumHarnessFrozenTarget := by
  classical
  intro S T _ _ left right
  change (Finset.univ.filter (fun p : S × T => left p.1 ∧ right p.2)).card =
    (Finset.univ.filter left).card * (Finset.univ.filter right).card
  have h : Finset.univ.filter (fun p : S × T => left p.1 ∧ right p.2) =
      (Finset.univ.filter left).product (Finset.univ.filter right) := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  rw [h, Finset.card_product]
