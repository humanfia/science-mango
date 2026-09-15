import FrozenTarget_151908f385ee7d0d
theorem M7.Transport.z_logical : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  have hJ : Function.Involutive (M6.Flatten.J N) := M6.Flatten.J_involution N
  have hJL : ∀ (d : M7.Transport.Recipe N) (w : M6.Pinned.Vector (2*N)),
      w ∈ M7.Transport.LX d ↔ M6.Flatten.J N w ∈ M7.Transport.LZ d := by
    intro d w
    exact M6.ActualCSS.J_logical_iff N (M7.Supports.indicator d.1) (M7.Supports.indicator d.2) w
  constructor
  · change Function.Bijective (M6.Flatten.J N ∘ M7.Transport.Xmap g ∘ M6.Flatten.J N)
    exact hJ.bijective.comp ((M7.Transport.action_isometry N g c).1.comp hJ.bijective)
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · change M6.Flatten.J N (M7.Transport.Xmap g (M6.Flatten.J N v)) ∈ M7.Transport.LZ (M7.Action.act g c) ↔ v ∈ M7.Transport.LZ c
      calc
        _ ↔ M7.Transport.Xmap g (M6.Flatten.J N v) ∈ M7.Transport.LX (M7.Action.act g c) := (hJL _ _).symm
        _ ↔ M6.Flatten.J N v ∈ M7.Transport.LX c := M7.Transport.x_logical N g c _
        _ ↔ v ∈ M7.Transport.LZ c := by
          simpa only [M6.Flatten.J_involution] using hJL c (M6.Flatten.J N v)
    · change M6.Pinned.weight (M6.Flatten.J N (M7.Transport.Xmap g (M6.Flatten.J N v))) = M6.Pinned.weight v
      rw [M6.Flatten.J_weight, (M7.Transport.action_isometry N g c).2 (M6.Flatten.J N v) |>.2.2, M6.Flatten.J_weight]
    · change M6.Flatten.J N (M7.Transport.Xmap g (M6.Flatten.J N (M6.Flatten.J N v))) = M6.Flatten.J N (M7.Transport.Xmap g v)
      rw [M6.Flatten.J_involution]
