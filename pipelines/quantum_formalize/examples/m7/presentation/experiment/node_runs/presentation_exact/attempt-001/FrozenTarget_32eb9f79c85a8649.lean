import M7Presentation
import M7SelectionAccepted

theorem M7.Presentation.candidates_sound : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.candidates K L R → M7.Presentation.valid K L R a := by
  classical
  intro κ σ τ _ _ _ K L R a ha
  unfold M7.Presentation.candidates at ha
  rcases Finset.mem_biUnion.mp ha with ⟨k, hk, ha⟩
  split at ha
  · have heq := Finset.mem_singleton.mp ha
    subst a
    simp [M7.Presentation.valid, M7.Presentation.outer,
      M7.Presentation.left, M7.Presentation.right,
      M7.Presentation.mk, hk, Finset.min'_mem]
  · simp at ha

theorem M7.Presentation.leastOf_spec : ∀ (α : Type) [LinearOrder α] (T : Finset α), (∀ x, M7.Presentation.leastOf T = some x ↔ x ∈ T ∧ ∀ y ∈ T, x ≤ y) ∧ (M7.Presentation.leastOf T = none ↔ T = ∅) := by
  classical
  intro α inst T
  by_cases h : T.Nonempty
  · constructor
    · intro x
      simp only [M7.Presentation.leastOf, dif_pos h, Option.some.injEq]
      constructor
      · intro hx
        rw [← hx]
        exact ⟨Finset.min'_mem T h, fun y hy => Finset.min'_le T y hy⟩
      · rintro ⟨hx, hmin⟩
        exact le_antisymm (Finset.min'_le T x hx) (hmin _ (Finset.min'_mem T h))
    · simp [M7.Presentation.leastOf, h, h.ne_empty]
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst T
    simp [M7.Presentation.leastOf]

theorem M7.Presentation.record_eta : ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a := by
  change ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a
  intro κ σ τ a
  rcases a with ⟨k, s, t⟩
  rfl

theorem M7.Presentation.record_mono : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (k : κ) (s s1 : σ) (t t1 : τ), s ≤ s1 → t ≤ t1 → M7.Presentation.mk k s t ≤ M7.Presentation.mk k s1 t1 := by
  intro κ σ τ _ _ _ k s s1 t t1 hs ht
  rcases lt_or_eq_of_le hs with h | h
  · simp [M7.Presentation.mk, Prod.Lex.toLex_le_toLex, h, le_of_lt h, not_le_of_gt h, ht]
  · subst s1
    simp [M7.Presentation.mk, Prod.Lex.toLex_le_toLex, ht]

theorem M7.Presentation.winning_fiber : ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (m : ℕ) (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode) (a b : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T → b ∈ M7.Presentation.domain K S T → M7.Presentation.realize l r a = M7.Presentation.realize l r b → (a ∈ M7.Presentation.selected K S T l r feasible objective mode ↔ b ∈ M7.Presentation.selected K S T l r feasible objective mode) := by
  intro κ σ τ X Y _ _ _ K S T l r m feasible objective mode a b ha hb hab
  classical
  change a ∈ M7.Selection.select (M7.Presentation.domain K S T)
      (fun x => feasible (M7.Presentation.realize l r x))
      (fun x => objective (M7.Presentation.realize l r x)) mode ↔
    b ∈ M7.Selection.select (M7.Presentation.domain K S T)
      (fun x => feasible (M7.Presentation.realize l r x))
      (fun x => objective (M7.Presentation.realize l r x)) mode
  have hex := (M7.Selection.selector_exact (M7.Presentation.Record κ σ τ) m
    (M7.Presentation.domain K S T)
    (fun x => feasible (M7.Presentation.realize l r x))
    (fun x => objective (M7.Presentation.realize l r x)) mode).1
  rw [hex a, hex b]
  simp only [ha, hb, hab]

theorem M7.Presentation.candidate_dominates : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.valid K L R a → ∃ b ∈ M7.Presentation.candidates K L R, b ≤ a := by
  change ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.valid K L R a → ∃ b ∈ M7.Presentation.candidates K L R, b ≤ a
  intro κ σ τ _ _ _ K L R a ha
  classical
  rcases ha with ⟨hk, hs, ht⟩
  have hL : (L (M7.Presentation.outer a)).Nonempty := ⟨_, hs⟩
  have hR : (R (M7.Presentation.outer a)).Nonempty := ⟨_, ht⟩
  refine ⟨M7.Presentation.mk (M7.Presentation.outer a) ((L (M7.Presentation.outer a)).min' hL) ((R (M7.Presentation.outer a)).min' hR), ?_, ?_⟩
  · unfold M7.Presentation.candidates
    apply Finset.mem_biUnion.mpr
    refine ⟨M7.Presentation.outer a, hk, ?_⟩
    simp [hL, hR]
  · simpa only [M7.Presentation.record_eta] using
      (M7.Presentation.record_mono κ σ τ (M7.Presentation.outer a)
        ((L (M7.Presentation.outer a)).min' hL) (M7.Presentation.left a)
        ((R (M7.Presentation.outer a)).min' hR) (M7.Presentation.right a)
        (Finset.min'_le _ _ hs) (Finset.min'_le _ _ ht))

theorem M7.Presentation.domain_membership : ∀ (κ σ τ : Type) (K : Finset κ) (S : Finset σ) (T : Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T ↔ M7.Presentation.outer a ∈ K ∧ M7.Presentation.left a ∈ S ∧ M7.Presentation.right a ∈ T := by
  change ∀ (κ σ τ : Type) (K : Finset κ) (S : Finset σ) (T : Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T ↔ M7.Presentation.outer a ∈ K ∧ M7.Presentation.left a ∈ S ∧ M7.Presentation.right a ∈ T
  intro κ σ τ K S T a
  classical
  unfold M7.Presentation.domain
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨k, hk, h⟩
    rcases Finset.mem_image.mp h with ⟨p, hp, ha⟩
    rw [← ha]
    change k ∈ K ∧ p.1 ∈ S ∧ p.2 ∈ T
    exact ⟨hk, Finset.mem_product.mp hp⟩
  · rintro ⟨hk, hs, ht⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨M7.Presentation.outer a, hk, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(M7.Presentation.left a, M7.Presentation.right a), Finset.mem_product.mpr ⟨hs, ht⟩, ?_⟩
    exact M7.Presentation.record_eta κ σ τ a

theorem M7.Presentation.factorLeast_none : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ), M7.Presentation.factorLeast K L R = none ↔ ¬ ∃ a : M7.Presentation.Record κ σ τ, M7.Presentation.valid K L R a := by
  change ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ), M7.Presentation.factorLeast K L R = none ↔ ¬ ∃ a : M7.Presentation.Record κ σ τ, M7.Presentation.valid K L R a
  intro κ σ τ _ _ _ K L R
  classical
  change M7.Presentation.leastOf (M7.Presentation.candidates K L R) = none ↔ _
  rw [(M7.Presentation.leastOf_spec (M7.Presentation.Record κ σ τ) (M7.Presentation.candidates K L R)).2]
  constructor
  · intro he ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := M7.Presentation.candidate_dominates κ σ τ K L R a ha
    simpa [he] using hb
  · intro h
    ext a
    constructor
    · intro ha
      exact False.elim (h ⟨a, M7.Presentation.candidates_sound κ σ τ K L R a ha⟩)
    · intro ha
      simp at ha

theorem M7.Presentation.factorLeast_spec : ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.factorLeast K L R = some a ↔ M7.Presentation.valid K L R a ∧ ∀ b, M7.Presentation.valid K L R b → a ≤ b := by
  change ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.factorLeast K L R = some a ↔ M7.Presentation.valid K L R a ∧ ∀ b, M7.Presentation.valid K L R b → a ≤ b
  intro κ σ τ _ _ _ K L R a
  classical
  change M7.Presentation.leastOf (M7.Presentation.candidates K L R) = some a ↔ _
  rw [(M7.Presentation.leastOf_spec (M7.Presentation.Record κ σ τ) (M7.Presentation.candidates K L R)).1 a]
  constructor
  · rintro ⟨ha, hmin⟩
    refine ⟨M7.Presentation.candidates_sound κ σ τ K L R a ha, ?_⟩
    intro b hb
    obtain ⟨c, hc, hcb⟩ := M7.Presentation.candidate_dominates κ σ τ K L R b hb
    exact le_trans (hmin c hc) hcb
  · rintro ⟨ha, hmin⟩
    obtain ⟨c, hc, hca⟩ := M7.Presentation.candidate_dominates κ σ τ K L R a ha
    have heq : c = a := le_antisymm hca (hmin c (M7.Presentation.candidates_sound κ σ τ K L R c hc))
    refine ⟨heq ▸ hc, ?_⟩
    intro b hb
    exact hmin b (M7.Presentation.candidates_sound κ σ τ K L R b hb)

theorem M7.Presentation.targetLeast_spec : ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (q : X × Y), (∀ a : M7.Presentation.Record κ σ τ, M7.Presentation.targetLeast K S T l r q = some a ↔ a ∈ M7.Presentation.domain K S T ∧ M7.Presentation.realize l r a = q ∧ ∀ b ∈ M7.Presentation.domain K S T, M7.Presentation.realize l r b = q → a ≤ b) ∧ (M7.Presentation.targetLeast K S T l r q = none ↔ ¬ ∃ a ∈ M7.Presentation.domain K S T, M7.Presentation.realize l r a = q) := by
  classical
  intro κ σ τ X Y _ _ _ K S T l r q
  let L : κ → Finset σ := fun k => S.filter (fun s => l k s = q.1)
  let R : κ → Finset τ := fun k => T.filter (fun t => r k t = q.2)
  have hv : ∀ a : M7.Presentation.Record κ σ τ,
      M7.Presentation.valid K L R a ↔
        a ∈ M7.Presentation.domain K S T ∧ M7.Presentation.realize l r a = q := by
    intro a
    rw [M7.Presentation.domain_membership κ σ τ K S T a]
    simp only [M7.Presentation.valid, L, R, Finset.mem_filter]
    constructor
    · rintro ⟨hk, ⟨hs, hl⟩, ⟨ht, hr⟩⟩
      refine ⟨⟨hk, hs, ht⟩, ?_⟩
      apply Prod.ext
      · exact hl
      · exact hr
    · rintro ⟨⟨hk, hs, ht⟩, he⟩
      exact ⟨hk, ⟨hs, congrArg Prod.fst he⟩, ⟨ht, congrArg Prod.snd he⟩⟩
  constructor
  · intro a
    change M7.Presentation.factorLeast K L R = some a ↔ _
    rw [M7.Presentation.factorLeast_spec κ σ τ K L R a]
    constructor
    · rintro ⟨ha, hmin⟩
      obtain ⟨hd, he⟩ := (hv a).mp ha
      exact ⟨hd, he, fun b hb hq => hmin b ((hv b).mpr ⟨hb, hq⟩)⟩
    · rintro ⟨hd, he, hmin⟩
      refine ⟨(hv a).mpr ⟨hd, he⟩, ?_⟩
      intro b hb
      obtain ⟨hbd, hbe⟩ := (hv b).mp hb
      exact hmin b hbd hbe
  · change M7.Presentation.factorLeast K L R = none ↔ _
    simpa only [hv] using (M7.Presentation.factorLeast_none κ σ τ K L R)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (m : ℕ) (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.selected K S T l r feasible objective mode → ∃! b : M7.Presentation.Record κ σ τ, M7.Presentation.present K S T l r feasible objective mode b ∧ M7.Presentation.realize l r b = M7.Presentation.realize l r a
