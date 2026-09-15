import FrozenTarget_4f7763dfb3c9fb72
theorem M7.RecoveryInstance.fresh_leaf : QuantumHarnessFrozenTarget := by
  intro N inst w E bases hE hB hpos
  classical
  have hp := M7.RecoveryInstance.positive_path N w E bases hE hB hpos
  have hc := (M7.RecoveryInstance.count_card N w E bases hE hB (M7.RecoveryInstance.word w E bases)).1
  have hcard : 0 < (M7.RecoveryInstance.remaining w E bases (M7.RecoveryInstance.word w E bases)).card := by
    have hz := hp.2.1
    rw [hc] at hz
    exact_mod_cast hz
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
  change y ∈ M7.RecoveryPrefix.completed N w E (M7.RecoveryInstance.word w E bases) \ M7.OrbitResidual.covered bases at hy
  rcases Finset.mem_sdiff.mp hy with ⟨hyC, hyU⟩
  have hyEq : y = M7.RecoveryInstance.recoverLeaf w E bases := by
    have hs := M7.RecoveryPrefix.leaf_singleton N w E (M7.RecoveryInstance.word w E bases) hp.1 hyC
    simpa only [Finset.mem_singleton, M7.RecoveryInstance.recoverLeaf] using hs
  rw [← hyEq]
  refine ⟨?_, hyC⟩
  change y ∈ M7.RecoveryPrefix.completed N w E [] \ M7.OrbitResidual.covered bases
  exact Finset.mem_sdiff.mpr ⟨M7.RecoveryPrefix.completed_subroot N w E (M7.RecoveryInstance.word w E bases) hyC, hyU⟩
