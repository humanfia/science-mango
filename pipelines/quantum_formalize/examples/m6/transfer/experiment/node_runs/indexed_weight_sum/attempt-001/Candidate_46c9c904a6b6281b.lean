import FrozenTarget_46c9c904a6b6281b
theorem M6.Transfer.indexed_weight_sum : QuantumHarnessFrozenTarget := by
  intro R N instN K instK W
  classical
  have hm (p : M6.Transfer.ClosedWalk R N) (i : ZMod N) :
      p.val.1 i = M6.Transfer.memoryAt (M6.Transfer.labels p) i := by
    funext j
    exact M6.Transfer.memory_forced R N p i j
  simp_rw [hm]
  let e : M6.Transfer.ClosedWalk R N ≃ M6.Transfer.Input N :=
    Equiv.ofBijective M6.Transfer.labels (M6.Transfer.labels_bijective R N)
  exact e.sum_comp (fun h => ∏ i : ZMod N, W i (M6.Transfer.memoryAt h i) (h i))
