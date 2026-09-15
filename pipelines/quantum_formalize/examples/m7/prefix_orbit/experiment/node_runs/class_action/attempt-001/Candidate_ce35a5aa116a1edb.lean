import FrozenTarget_ce35a5aa116a1edb
theorem M7.PrefixOrbit.class_action : QuantumHarnessFrozenTarget := by
  intro N inst w c g h
  change c.1.card = w ∧ c.2.card = w ∧ M7.Connectivity.connected c at h
  change (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w ∧ M7.Connectivity.connected (M7.Action.act g c)
  have hc := (M7.Connectivity.connected_action N g c).mpr h.2.2
  first
  | have hcards := M7.Action.support_cards N g c
  | have hcards := M7.Action.support_cards N c g
  all_goals
    aesop
