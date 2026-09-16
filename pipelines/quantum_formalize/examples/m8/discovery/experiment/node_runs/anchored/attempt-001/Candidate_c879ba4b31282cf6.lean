import FrozenTarget_c879ba4b31282cf6
theorem M8.Discovery.anchored : QuantumHarnessFrozenTarget := by
  intro N _ c k h
  have hg := M8.Discovery.sound N c k h
  change M8.Anchor.Anchored (M8.Anchor.trial c k.exchange (M8.Discovery.unit k) (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N))
  exact M8.Anchor.anchored N c k.exchange (M8.Discovery.unit k) (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N) hg.2.1
