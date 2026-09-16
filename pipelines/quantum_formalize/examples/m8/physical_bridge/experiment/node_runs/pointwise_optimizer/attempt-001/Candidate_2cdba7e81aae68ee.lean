import FrozenTarget_2cdba7e81aae68ee
theorem M8.PhysicalBridge.pointwise_optimizer : QuantumHarnessFrozenTarget := by
  intro N inst c g w hv ha
  rcases hv with ⟨hA, hB, hc⟩
  rcases ha with ⟨haA, haB⟩
  have hcards : (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w := by
    first
    | solve_by_elim [M7.Action.support_cards]
    | simpa [hA, hB] using M7.Action.support_cards N g c
    | simpa [hA, hB] using M7.Action.support_cards N c g
  exact M7.ClosedSolve.closed_pointwise N w (M7.Action.act g c)
    hcards.1 hcards.2 haA haB
    ((M7.Connectivity.connected_action N g c).mpr hc)
