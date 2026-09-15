import FrozenTarget_f8105f2653e1b30c
theorem M5.ArithmeticResidueRecovery.oracle_partition_terminal : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0
  letI : DecidableEq (Fin (M5.signaturePeriod F)) := fun a b => Classical.propDecidable (a = b)
  classical
  let W := M5.ArithmeticResidueRecovery.fullWords (2 * (w - 1))
    (M5.ArithmeticResidueRecovery.wordValid w F)
  have hlen : ∀ q ∈ W, q.length = 2 * (w - 1) := by
    intro q hq
    unfold W M5.ArithmeticResidueRecovery.fullWords at hq
    have hi := (Finset.mem_filter.mp hq).1
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hi
    simpa only [List.length_ofFn] using (congrArg List.length he).symm
  have hc : ∀ u : List (Fin (M5.signaturePeriod F)),
      u.length ≤ 2 * (w - 1) →
      M5.ArithmeticResidueRecovery.oracle w F u = M5.PrefixPartition.count W u := by
    intro u hu
    exact M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0 u hu
  constructor
  · intro u hu
    calc
      M5.ArithmeticResidueRecovery.oracle w F u = M5.PrefixPartition.count W u :=
        hc u (Nat.le_of_lt hu)
      _ = ∑ a : Fin (M5.signaturePeriod F), M5.PrefixPartition.count W (u ++ [a]) :=
        M5.PrefixPartition.count_partition (Fin (M5.signaturePeriod F)) W
          (2 * (w - 1)) u hlen hu
      _ = ∑ a : Fin (M5.signaturePeriod F), M5.ArithmeticResidueRecovery.oracle w F (u ++ [a]) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Eq.symm
        apply hc
        simp only [List.length_append, List.length_singleton]
        omega
  · intro u hu hpos
    rw [hc u (Nat.le_of_eq hu),
      M5.PrefixPartition.count_terminal (Fin (M5.signaturePeriod F)) W
        (2 * (w - 1)) u hlen hu] at hpos
    have hmem : u ∈ W := by
      by_contra h
      rw [if_neg h] at hpos
      exact (lt_irrefl (0 : ℤ)) hpos
    unfold W M5.ArithmeticResidueRecovery.fullWords at hmem
    exact (Finset.mem_filter.mp hmem).2
