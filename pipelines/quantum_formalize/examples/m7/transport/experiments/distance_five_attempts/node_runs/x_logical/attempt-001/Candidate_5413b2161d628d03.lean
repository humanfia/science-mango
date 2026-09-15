import FrozenTarget_5413b2161d628d03
theorem M7.Transport.x_logical : QuantumHarnessFrozenTarget := by
  intro N inst g c v
  classical
  have h := (M7.Transport.action_isometry N g c).2 v
  change (M7.Transport.Xmap g v ∈ M7.Transport.CX (M7.Action.act g c) \ M7.Transport.BX (M7.Action.act g c) ↔ v ∈ M7.Transport.CX c \ M7.Transport.BX c)
  simp only [Finset.mem_sdiff, h.1, h.2.1]
