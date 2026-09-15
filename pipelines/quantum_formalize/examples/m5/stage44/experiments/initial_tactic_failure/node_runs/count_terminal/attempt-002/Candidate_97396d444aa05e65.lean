import FrozenTarget_97396d444aa05e65
theorem M5.PrefixPartition.count_terminal : QuantumHarnessFrozenTarget := by
  intro α inst W m p hW hp
  classical
  have hprefix (q : List α) (hq : q ∈ W) : p <+: q ↔ q = p := by
    constructor
    · intro h
      exact (h.eq_of_length (hp.trans (hW q hq).symm)).symm
    · rintro rfl
      exact List.prefix_rfl
  have htake (q : List α) (hq : q ∈ W) : q.take p.length = q := by
    rw [hp, ← hW q hq, List.take_length]
  have hf₁ : W.filter (fun q => p <+: q) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    exact hprefix q hq
  have hf₂ : W.filter (fun q => q.take p.length = p) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    rw [htake q hq]
  have hf₃ : W.filter (fun q => p = q.take p.length) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    rw [htake q hq, eq_comm]
  unfold M5.PrefixPartition.count
  simp +contextual [hf₁, hf₂, hf₃, hprefix, htake, eq_comm]
