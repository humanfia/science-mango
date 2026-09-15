import FrozenTarget_a5def6bb14165d76
theorem M5.ArithmeticResidueRecovery.oracle_partition_terminal : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0
  classical
  letI : DecidableEq (Fin (M5.signaturePeriod F)) := fun a b => Classical.propDecidable (a = b)
  let W : Finset (List (Fin (M5.signaturePeriod F))) :=
    M5.ArithmeticResidueRecovery.fullWords (2 * (w - 1))
      (M5.ArithmeticResidueRecovery.wordValid w F)
  have hW : ∀ q ∈ W, q.length = 2 * (w - 1) := by
    intro q hq
    unfold W M5.ArithmeticResidueRecovery.fullWords at hq
    rcases Finset.mem_filter.mp hq with ⟨hq, _⟩
    rcases Finset.mem_image.mp hq with ⟨f, _, hf⟩
    subst q
    exact List.length_ofFn
  have hc : ∀ u : List (Fin (M5.signaturePeriod F)),
      u.length ≤ 2 * (w - 1) →
      M5.ArithmeticResidueRecovery.oracle w F u = M5.PrefixPartition.count W u := by
    intro u hu
    exact M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0 u hu
  constructor
  · intro u hu
    rw [hc u (Nat.le_of_lt hu)]
    rw [M5.PrefixPartition.count_partition (Fin (M5.signaturePeriod F)) W
      (2 * (w - 1)) u hW hu]
    apply Finset.sum_congr rfl
    intro a ha
    apply Eq.symm
    apply hc
    simp only [List.length_append, List.length_singleton]
    omega
  · intro u hu hpos
    rw [hc u (Nat.le_of_eq hu)] at hpos
    rw [M5.PrefixPartition.count_terminal (Fin (M5.signaturePeriod F)) W
      (2 * (w - 1)) u hW hu] at hpos
    have hm : u ∈ W := by
      by_contra hn
      rw [if_neg hn] at hpos
      omega
    unfold W M5.ArithmeticResidueRecovery.fullWords at hm
    exact (Finset.mem_filter.mp hm).2
