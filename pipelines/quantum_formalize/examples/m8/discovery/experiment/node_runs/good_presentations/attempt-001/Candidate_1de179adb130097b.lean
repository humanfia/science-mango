import FrozenTarget_1de179adb130097b
theorem M8.Discovery.good_presentations : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c
  constructor
  · rintro ⟨k, hk, he, hs⟩
    exact ⟨k.exchange, M8.Discovery.unit k,
      (k.leftAnchor.val : ZMod N), (k.rightAnchor.val : ZMod N), he, hs⟩
  · rintro ⟨e, u, a, b, he, hs⟩
    let k : M8.Discovery.Choice N :=
      ⟨e, ⟨(u : ZMod N).val, ZMod.val_lt (u : ZMod N)⟩,
        ⟨a.val, ZMod.val_lt a⟩, ⟨b.val, ZMod.val_lt b⟩⟩
    have ht : (k.unitIndex.val : ZMod N) = (u : ZMod N) := by
      exact ZMod.natCast_zmod_val (u : ZMod N)
    have ha : (k.leftAnchor.val : ZMod N) = a := by
      exact ZMod.natCast_zmod_val a
    have hb : (k.rightAnchor.val : ZMod N) = b := by
      exact ZMod.natCast_zmod_val b
    have hi : IsUnit (k.unitIndex.val : ZMod N) := by
      rw [ht]
      exact u.isUnit
    have hu : M8.Discovery.unit k = u := by
      unfold M8.Discovery.unit
      rw [dif_pos hi]
      apply Units.ext
      exact hi.unit_spec.trans ht
    refine ⟨k, hi, ?_, ?_⟩
    · change M8.Anchor.Eligible c e (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N)
      rw [ha, hb]
      exact he
    · change M8.Anchor.span (M8.Anchor.trial c e (M8.Discovery.unit k)
        (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N)) ≤ M8.Cutoff.limit N
      rw [hu, ha, hb]
      exact hs
