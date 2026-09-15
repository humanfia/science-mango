import FrozenTarget_02a584fcab95380b
theorem M5.ArithmeticResidueRecovery.oracle_partition_terminal : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0
  classical
  let W : Finset (List (Fin (M5.signaturePeriod F))) :=
    M5.ArithmeticResidueRecovery.fullWords (2 * (w - 1))
      (M5.ArithmeticResidueRecovery.wordValid w F)
  have hlen : ∀ q ∈ W, q.length = 2 * (w - 1) := by
    intro q hq
    unfold W M5.ArithmeticResidueRecovery.fullWords at hq
    obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    subst q
    exact List.length_ofFn
  constructor
  · intro u hu
    calc
      M5.ArithmeticResidueRecovery.oracle w F u = M5.PrefixPartition.count W u :=
        M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0 u (Nat.le_of_lt hu)
      _ = ∑ a : Fin (M5.signaturePeriod F), M5.PrefixPartition.count W (u ++ [a]) :=
        M5.PrefixPartition.count_partition (Fin (M5.signaturePeriod F)) W
          (2 * (w - 1)) u hlen hu
      _ = ∑ a : Fin (M5.signaturePeriod F), M5.ArithmeticResidueRecovery.oracle w F (u ++ [a]) := by
        apply Finset.sum_congr rfl
        intro a ha
        symm
        apply M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0
        simp only [List.length_append, List.length_singleton]
        omega
  · intro u hu hpos
    rw [M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0 u (Nat.le_of_eq hu)] at hpos
    change 0 < M5.PrefixPartition.count W u at hpos
    rw [M5.PrefixPartition.count_terminal (Fin (M5.signaturePeriod F)) W
      (2 * (w - 1)) u hlen hu] at hpos
    have hmem : u ∈ W := by
      by_contra hnot
      rw [if_neg hnot] at hpos
      exact (lt_irrefl (0 : ℤ)) hpos
    unfold W M5.ArithmeticResidueRecovery.fullWords at hmem
    exact (Finset.mem_filter.mp hmem).2
