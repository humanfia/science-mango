import M8Discovery

theorem M8.Discovery.good_presentations : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (∃ k : M8.Discovery.Choice N, M8.Discovery.Good c k) ↔ ∃ (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b ∧ M8.Anchor.span (M8.Anchor.trial c e u a b) ≤ M8.Cutoff.limit N := by
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

theorem M8.Discovery.inverse : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M7.Action.act (M7.Action.inverse (M8.Discovery.action k)) (M8.Discovery.transformed c k) = c := by
  intro N inst c k
  change M7.Action.act (M7.Action.inverse (M8.Discovery.action k)) (M7.Action.act (M8.Discovery.action k) c) = c
  exact M7.Action.act_inverse N (M8.Discovery.action k) c
#print axioms M8.Discovery.good_presentations
#print axioms M8.Discovery.inverse
