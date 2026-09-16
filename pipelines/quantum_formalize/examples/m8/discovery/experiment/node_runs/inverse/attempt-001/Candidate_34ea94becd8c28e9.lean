import FrozenTarget_34ea94becd8c28e9
theorem M8.Discovery.inverse : QuantumHarnessFrozenTarget := by
  intro N inst c k
  change M7.Action.act (M7.Action.inverse (M8.Discovery.action k)) (M7.Action.act (M8.Discovery.action k) c) = c
  exact M7.Action.act_inverse N (M8.Discovery.action k) c
