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

theorem M8.Discovery.anchored : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → M8.Anchor.Anchored (M8.Discovery.transformed c k) := by
  intro N _ c k h
  have hg := M8.Discovery.sound N c k h
  change M8.Anchor.Anchored (M8.Anchor.trial c k.exchange (M8.Discovery.unit k) (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N))
  exact M8.Anchor.anchored N c k.exchange (M8.Discovery.unit k) (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N) hg.2.1

theorem M8.Discovery.cutoff : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → M8.Anchor.span (M8.Discovery.transformed c k) ≤ M8.Cutoff.limit N := by
  intro N _ c k h
  exact (M8.Discovery.sound N c k h).2.2

theorem M8.Discovery.lex_first : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → ∀ j : M8.Discovery.Choice N, M8.Discovery.Good c j → M8.Discovery.key k ≤ M8.Discovery.key j := by
  classical
  intro N _ c k h j hj
  have lift (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (i : Fin n) (hi : f i ≠ none) :
      (M8.FiniteSearch.find f).1.map Prod.snd ≠ none := by
    intro hz
    have hf : (M8.FiniteSearch.find f).1 = none := by
      cases hh : (M8.FiniteSearch.find f).1 <;> simp_all
    exact hi ((M8.FiniteSearch.find_none n (M8.Discovery.Choice N) f).mp hf i)
  have step (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (hs : (M8.FiniteSearch.find f).1.map Prod.snd = some k) :
      ∃ i, f i = some k ∧ ∀ q, f q ≠ none → i ≤ q := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none => simp [hf] at hs
    | some p =>
      rcases p with ⟨i, v⟩
      have hv : v = k := by simpa [hf] using hs
      subst v
      have hp := (M8.FiniteSearch.find_some n (M8.Discovery.Choice N) f i k).mp hf
      refine ⟨i, hp.1, ?_⟩
      intro q hq
      by_contra hn
      exact hq (hp.2 q (by omega))
  have hjtest := (M8.Discovery.test_spec N c j).mpr hj
  have hr : M8.Discovery.atRight c j.exchange j.unitIndex j.leftAnchor ≠ none := by
    unfold M8.Discovery.atRight
    apply lift N _ j.rightAnchor
    change (if M8.Discovery.test c j = true then some j else none) ≠ none
    simp [hjtest]
  have hl : M8.Discovery.atLeft c j.exchange j.unitIndex ≠ none := by
    unfold M8.Discovery.atLeft
    exact lift N _ j.leftAnchor hr
  have hu : M8.Discovery.atUnit c j.exchange ≠ none := by
    unfold M8.Discovery.atUnit
    exact lift N _ j.unitIndex hl
  let ej : Fin 2 := if j.exchange then 1 else 0
  have hej : decide (ej.val = 1) = j.exchange := by
    cases hx : j.exchange <;> simp [ej, hx]
  unfold M8.Discovery.discover at h
  obtain ⟨e, he, emin⟩ := step 2 _ h
  have ele : e ≤ ej := emin ej (by simpa only [hej] using hu)
  unfold M8.Discovery.atUnit at he
  obtain ⟨t, ht, tmin⟩ := step N _ he
  unfold M8.Discovery.atLeft at ht
  obtain ⟨a, ha, amin⟩ := step N _ ht
  unfold M8.Discovery.atRight at ha
  obtain ⟨b, hb, bmin⟩ := step N _ ha
  change (if M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true then
    some ⟨decide (e.val = 1), t, a, b⟩ else none) = some k at hb
  have hk : (⟨decide (e.val = 1), t, a, b⟩ : M8.Discovery.Choice N) = k := by
    split at hb
    · exact Option.some.inj hb
    · simp at hb
  rw [← hk]
  change toLex (decide (e.val = 1), toLex (t, toLex (a, b))) ≤
    toLex (j.exchange, toLex (j.unitIndex, toLex (j.leftAnchor, j.rightAnchor)))
  rcases lt_or_eq_of_le ele with elt | eeq
  · have hex : decide (e.val = 1) < j.exchange := by
      fin_cases e <;> cases hx : j.exchange <;> simp_all [ej]
    apply Prod.Lex.left
    exact hex
  · have hex : decide (e.val = 1) = j.exchange := by
      rw [eeq]
      exact hej
    rw [hex] at tmin amin bmin ⊢
    apply Prod.Lex.right
    have tle : t ≤ j.unitIndex := tmin j.unitIndex hl
    rcases lt_or_eq_of_le tle with tlt | teq
    · apply Prod.Lex.left
      exact tlt
    · subst t
      apply Prod.Lex.right
      have ale : a ≤ j.leftAnchor := amin j.leftAnchor hr
      rcases lt_or_eq_of_le ale with alt | aeq
      · apply Prod.Lex.left
        exact alt
      · subst a
        apply Prod.Lex.right
        apply bmin j.rightAnchor
        change (if M8.Discovery.test c j = true then some j else none) ≠ none
        simp [hjtest]

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

theorem M8.Discovery.complete : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Discovery.discover c ≠ none ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ M8.Cutoff.limit N := by
  classical
  intro N inst c
  change (¬ M8.Discovery.discover c = none) ↔ _
  rw [M8.Discovery.none_iff N c]
  simp only [not_forall, not_not]
  exact (M8.Discovery.good_presentations N c).trans
    (M8.Anchor.passing_presentations N c (M8.Cutoff.limit N))
#print axioms M8.Discovery.good_presentations
#print axioms M8.Discovery.inverse
#print axioms M8.Discovery.test_spec
#print axioms M8.Discovery.right_none
#print axioms M8.Discovery.none_iff
#print axioms M8.Discovery.complete
#print axioms M8.Discovery.sound
#print axioms M8.Discovery.anchored
#print axioms M8.Discovery.cutoff
#print axioms M8.Discovery.lex_first
