import FrozenTarget_970909be5b3ce9f0
theorem M5.ArithmeticResidueRecovery.oracle_partition_terminal : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0
  classical
  let W := M5.ArithmeticResidueRecovery.fullWords (2 * (w - 1))
    (M5.ArithmeticResidueRecovery.wordValid w F)
  have hlen : ∀ q ∈ W, q.length = 2 * (w - 1) := by
    intro q hq
    change q ∈ M5.ArithmeticResidueRecovery.fullWords (2 * (w - 1))
      (M5.ArithmeticResidueRecovery.wordValid w F) at hq
    unfold M5.ArithmeticResidueRecovery.fullWords at hq
    obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    subst q
    exact List.length_ofFn
  have horacle : ∀ u : List (Fin (M5.signaturePeriod F)),
      u.length ≤ 2 * (w - 1) →
      M5.ArithmeticResidueRecovery.oracle w F u = M5.PrefixPartition.count W u := by
    intro u hu
    exact M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0 u hu
  constructor
  · intro u hu
    rw [horacle u (Nat.le_of_lt hu)]
    rw [M5.PrefixPartition.count_partition (Fin (M5.signaturePeriod F)) W
      (2 * (w - 1)) u hlen hu]
    apply Finset.sum_congr rfl
    intro a ha
    symm
    apply horacle
    simp only [List.length_append, List.length_singleton]
    omega
  · intro u hu hpos
    rw [horacle u (Nat.le_of_eq hu)] at hpos
    rw [M5.PrefixPartition.count_terminal (Fin (M5.signaturePeriod F)) W
      (2 * (w - 1)) u hlen hu] at hpos
    have hmem : u ∈ W := by
      by_contra hn
      rw [if_neg hn] at hpos
      exact (lt_irrefl (0 : ℤ)) hpos
    change u ∈ M5.ArithmeticResidueRecovery.fullWords (2 * (w - 1))
      (M5.ArithmeticResidueRecovery.wordValid w F) at hmem
    unfold M5.ArithmeticResidueRecovery.fullWords at hmem
    exact (Finset.mem_filter.mp hmem).2
