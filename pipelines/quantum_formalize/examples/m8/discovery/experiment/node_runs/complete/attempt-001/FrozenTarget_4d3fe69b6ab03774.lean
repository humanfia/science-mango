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

theorem M8.Discovery.test_spec : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.Discovery.test c k = true ↔ M8.Discovery.Good c k := by
  classical
  intro N _ c k
  have hv (i : ZMod N) (a : Fin N) : i.val = a.val ↔ i = (a.val : ZMod N) := by
    constructor
    · intro h
      rw [← ZMod.natCast_zmod_val i, h]
    · intro h
      subst i
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  have hs (s : Finset (ZMod N)) (a : ZMod N) :
      s.sup (fun i => if i = a then (1 : ℕ) else 0) =
        if a ∈ s then 1 else 0 := by
    by_cases ha : a ∈ s
    · rw [if_pos ha]
      apply le_antisymm
      · apply Finset.sup_le
        intro i hi
        split <;> omega
      · simpa using (Finset.le_sup (f := fun i : ZMod N => if i = a then (1 : ℕ) else 0) ha)
    · rw [if_neg ha]
      apply le_antisymm
      · apply Finset.sup_le
        intro i hi
        have hia : i ≠ a := by
          intro h
          exact ha (h ▸ hi)
        simp only [if_neg hia, le_refl]
      · exact Nat.zero_le _
  have hg : Nat.gcd k.unitIndex.val N = 1 ↔
      IsUnit (k.unitIndex.val : ZMod N) := by
    simpa [Nat.Coprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt k.unitIndex.isLt] using
      (ZMod.isUnit_iff_coprime k.unitIndex.val N).symm
  by_cases hu : IsUnit (k.unitIndex.val : ZMod N)
  · have hc : (M8.Discovery.unit k : ZMod N) = (k.unitIndex.val : ZMod N) := by
      simpa only [M8.Discovery.unit, dif_pos hu] using hu.unit_spec
    have ht : M8.Anchor.span (M8.Discovery.transformed c k) =
        max
          ((M8.Anchor.left c k.exchange).sup (fun i =>
            (((k.unitIndex.val : ZMod N) * (i - (k.leftAnchor.val : ZMod N))).val)))
          ((M8.Anchor.right c k.exchange).sup (fun i =>
            (((k.unitIndex.val : ZMod N) * (i - (k.rightAnchor.val : ZMod N))).val))) := by
      change M8.Anchor.span (M8.Anchor.trial c k.exchange
        (M8.Discovery.unit k) (k.leftAnchor.val : ZMod N)
        (k.rightAnchor.val : ZMod N)) = _
      rw [M8.Anchor.trial_formula]
      simp [M8.Anchor.span, Finset.sup_image, Function.comp_def, hc]
    simp [M8.Discovery.test, M8.Discovery.Good, M8.Anchor.Eligible,
      hv, hs, hg, hu, ht, and_assoc]
  · simp [M8.Discovery.test, M8.Discovery.Good, hg, hu]

theorem M8.Discovery.right_none : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t a : Fin N), M8.Discovery.atRight c e t a = none ↔ ∀ b : Fin N, ¬ M8.Discovery.Good c ⟨e,t,a,b⟩ := by
  classical
  intro N _ c e t a
  have hm (o : Option (Fin N × M8.Discovery.Choice N)) :
      o.map Prod.snd = none ↔ o = none := by
    cases o <;> simp
  rw [M8.Discovery.atRight, hm, M8.FiniteSearch.find_none]
  simp [M8.Discovery.test_spec]

theorem M8.Discovery.none_iff : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Discovery.discover c = none ↔ ∀ k : M8.Discovery.Choice N, ¬ M8.Discovery.Good c k := by
  classical
  intro N _ c
  have hm {m : ℕ} (o : Option (Fin m × M8.Discovery.Choice N)) :
      o.map Prod.snd = none ↔ o = none := by
    cases o <;> simp
  simp only [M8.Discovery.discover, M8.Discovery.atUnit,
    M8.Discovery.atLeft, hm, M8.FiniteSearch.find_none,
    M8.Discovery.right_none]
  constructor
  · intro h k
    rcases k with ⟨e, t, a, b⟩
    cases e
    · simpa using h (0 : Fin 2) t a b
    · simpa using h (1 : Fin 2) t a b
  · intro h e t a b
    exact h ⟨decide (e.val = 1), t, a, b⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Discovery.discover c ≠ none ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ M8.Cutoff.limit N
