import FrozenTarget_3f6dc572d3f4cd85
theorem M8.Discovery.inverse : QuantumHarnessFrozenTarget := by
  intro N inst c k
  change M7.Action.act (M7.Action.inverse (M8.Discovery.action k)) (M7.Action.act (M8.Discovery.action k) c) = c
  exact M7.Action.act_inverse N (M8.Discovery.action k) c
