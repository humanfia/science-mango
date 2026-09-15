import FrozenTarget_59ac0fc1656e0264
theorem M5.ArithmeticResidueRecovery.oracle_partition_terminal : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0
  letI : DecidableEq (Fin (M5.signaturePeriod F)) :=
    fun a b => Classical.propDecidable (a = b)
  classical
  let W := M5.ArithmeticResidueRecovery.fullWords (2 * (w - 1))
    (M5.ArithmeticResidueRecovery.wordValid w F)
  have hlen : ∀ q ∈ W, q.length = 2 * (w - 1) := by
    intro q hq
    unfold W M5.ArithmeticResidueRecovery.fullWords at hq
    rcases Finset.mem_filter.mp hq with ⟨hq, _⟩
    rcases Finset.mem_image.mp hq with ⟨f, _, hf⟩
    subst q
    exact List.length_ofFn
  constructor
  · intro u hu
    calc
      M5.ArithmeticResidueRecovery.oracle w F u =
          M5.PrefixPartition.count W u :=
        M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0 u (by omega)
      _ = ∑ a : Fin (M5.signaturePeriod F), M5.PrefixPartition.count W (u ++ [a]) :=
        M5.PrefixPartition.count_partition _ W (2 * (w - 1)) u hlen hu
      _ = ∑ a : Fin (M5.signaturePeriod F), M5.ArithmeticResidueRecovery.oracle w F (u ++ [a]) := by
        apply Finset.sum_congr rfl
        intro a ha
        symm
        apply M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0
        simp only [List.length_append, List.length_singleton]
        omega
  · intro u hu hpos
    have hc := M5.ArithmeticResidueRecovery.oracle_prefix_count w F hw hF hF0 u (by omega)
    have ht := M5.PrefixPartition.count_terminal
      (Fin (M5.signaturePeriod F)) W (2 * (w - 1)) u hlen hu
    have hm : u ∈ W := by
      by_contra hn
      rw [hc, ht, if_neg hn] at hpos
      exact (lt_irrefl 0) hpos
    unfold W M5.ArithmeticResidueRecovery.fullWords at hm
    exact (Finset.mem_filter.mp hm).2
