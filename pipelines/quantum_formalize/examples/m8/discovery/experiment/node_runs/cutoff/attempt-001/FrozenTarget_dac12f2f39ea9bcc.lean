import M8Discovery

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

theorem M8.Discovery.sound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → M8.Discovery.Good c k := by
  classical
  intro N _ c k h
  have step (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (hs : (M8.FiniteSearch.find f).1.map Prod.snd = some k) :
      ∃ i, f i = some k := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none => simp [hf] at hs
    | some p =>
      rcases p with ⟨i, v⟩
      have hv : v = k := by simpa [hf] using hs
      subst v
      exact ⟨i, ((M8.FiniteSearch.find_some n (M8.Discovery.Choice N) f i k).mp hf).1⟩
  unfold M8.Discovery.discover at h
  obtain ⟨e, he⟩ := step 2 _ h
  unfold M8.Discovery.atUnit at he
  obtain ⟨t, ht⟩ := step N _ he
  unfold M8.Discovery.atLeft at ht
  obtain ⟨a, ha⟩ := step N _ ht
  unfold M8.Discovery.atRight at ha
  obtain ⟨b, hb⟩ := step N _ ha
  change (if M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true then
    some ⟨decide (e.val = 1), t, a, b⟩ else none) = some k at hb
  by_cases hp : M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true
  · rw [if_pos hp] at hb
    have hk := Option.some.inj hb
    rw [hk] at hp
    exact (M8.Discovery.test_spec N c k).mp hp
  · simp [hp] at hb
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → M8.Anchor.span (M8.Discovery.transformed c k) ≤ M8.Cutoff.limit N
