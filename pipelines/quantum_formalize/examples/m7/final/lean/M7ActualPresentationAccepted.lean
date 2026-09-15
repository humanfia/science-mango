import M7ActualPresentation
import M7PresentationAccepted

theorem M7.ActualPresentation.decode_encode : ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N), M7.ActualPresentation.decode (M7.ActualPresentation.encode g) = g := by
  change ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N), M7.ActualPresentation.decode (M7.ActualPresentation.encode g) = g
  intro N inst g
  rcases g with ⟨u, s, t, e⟩
  simp [M7.ActualPresentation.decode, M7.ActualPresentation.encode,
    M7.Presentation.mk, M7.Presentation.outer, M7.Presentation.left,
    M7.Presentation.right, ZMod.natCast_zmod_val]

theorem M7.ActualPresentation.domain_univ : ∀ (N : ℕ) [NeZero N], M7.Presentation.domain (Finset.univ : Finset (M7.ActualPresentation.Outer N)) (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N)) = (Finset.univ : Finset (M7.ActualPresentation.Encoded N)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N], M7.Presentation.domain (Finset.univ : Finset (M7.ActualPresentation.Outer N)) (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N)) = (Finset.univ : Finset (M7.ActualPresentation.Encoded N))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N hN
  classical
  apply Finset.ext
  intro a
  rw [M7.Presentation.domain_membership]
  simp

theorem M7.ActualPresentation.encode_decode : ∀ (N : ℕ) [NeZero N] (a : M7.ActualPresentation.Encoded N), M7.ActualPresentation.encode (M7.ActualPresentation.decode a) = a := by
  change ∀ (N : ℕ) [NeZero N] (a : M7.ActualPresentation.Encoded N), M7.ActualPresentation.encode (M7.ActualPresentation.decode a) = a
  intro N inst a
  have h : ∀ s : Fin N, ((s.val : ZMod N).val) = s.val := by
    intro s
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt]
  rcases a with ⟨⟨u, b⟩, s, t⟩
  cases u
  cases b <;>
    simp [M7.ActualPresentation.encode, M7.ActualPresentation.decode,
      M7.Presentation.mk, M7.Presentation.outer,
      M7.Presentation.left, M7.Presentation.right, h] <;> rfl

theorem M7.ActualPresentation.four_field_order : ∀ (N : ℕ) [NeZero N] (g h : M7.Action.Record N), (M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h ↔ (g.unit : ZMod N).val < (h.unit : ZMod N).val ∨ (g.unit : ZMod N).val = (h.unit : ZMod N).val ∧ (g.exchange < h.exchange ∨ g.exchange = h.exchange ∧ (g.leftShift.val < h.leftShift.val ∨ g.leftShift.val = h.leftShift.val ∧ g.rightShift.val ≤ h.rightShift.val))) := by
  intro N _ g h
  have unit_eq (a b : M7.ActualPresentation.UnitKey N) :
      a = b ↔ (a.unit : ZMod N).val = (b.unit : ZMod N).val := by
    constructor
    · rintro rfl
      rfl
    · intro hab
      have hu : a.unit = b.unit := Units.ext (ZMod.val_injective N hab)
      cases a
      cases b
      cases hu
      rfl
  have unit_lt (a b : M7.ActualPresentation.UnitKey N) :
      a < b ↔ (a.unit : ZMod N).val < (b.unit : ZMod N).val := by
    rfl
  simp [M7.ActualPresentation.encode, M7.Presentation.mk,
    Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex,
    Prod.mk.injEq, unit_eq, unit_lt, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    <;> tauto

theorem M7.ActualPresentation.realize_decode : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (a : M7.ActualPresentation.Encoded N), M7.Presentation.realize (M7.ActualPresentation.leftImage c) (M7.ActualPresentation.rightImage c) a = M7.Action.act (M7.ActualPresentation.decode a) c := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (a : M7.ActualPresentation.Encoded N), M7.Presentation.realize (M7.ActualPresentation.leftImage c) (M7.ActualPresentation.rightImage c) a = M7.Action.act (M7.ActualPresentation.decode a) c
  intro N inst c a
  rfl

theorem M7.ActualPresentation.winning_fiber : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g h : M7.Action.Record N), M7.Action.act g c = M7.Action.act h c → (g ∈ M7.ActualPresentation.selected c feasible objective mode ↔ h ∈ M7.ActualPresentation.selected c feasible objective mode) := by
  intro N inst c m feasible objective mode g h heq
  classical
  unfold M7.ActualPresentation.selected
  rw [(M7.Selection.selector_exact _ _ _ _ _ _).1 g,
      (M7.Selection.selector_exact _ _ _ _ _ _).1 h]
  simp only [Finset.mem_univ, true_and, heq]

theorem M7.ActualPresentation.leastAction_spec : ∀ (N : ℕ) [NeZero N] (c q : M7.Action.Recipe N), (∀ g : M7.Action.Record N, M7.ActualPresentation.leastAction c q = some g ↔ M7.Action.act g c = q ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = q → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h) ∧ (M7.ActualPresentation.leastAction c q = none ↔ ¬ ∃ g : M7.Action.Record N, M7.Action.act g c = q) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (c q : M7.Action.Recipe N), (∀ g : M7.Action.Record N, M7.ActualPresentation.leastAction c q = some g ↔ M7.Action.act g c = q ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = q → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h) ∧ (M7.ActualPresentation.leastAction c q = none ↔ ¬ ∃ g : M7.Action.Record N, M7.Action.act g c = q)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst c q
  classical
  let t := M7.Presentation.targetLeast
    (Finset.univ : Finset (M7.ActualPresentation.Outer N))
    (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N))
    (M7.ActualPresentation.leftImage c) (M7.ActualPresentation.rightImage c) q
  have hs :
      (∀ a : M7.ActualPresentation.Encoded N, t = some a ↔
        M7.Action.act (M7.ActualPresentation.decode a) c = q ∧
        ∀ b : M7.ActualPresentation.Encoded N,
          M7.Action.act (M7.ActualPresentation.decode b) c = q → a ≤ b) ∧
      (t = none ↔ ¬ ∃ a : M7.ActualPresentation.Encoded N,
        M7.Action.act (M7.ActualPresentation.decode a) c = q) := by
    simpa [t, M7.ActualPresentation.domain_univ,
      M7.ActualPresentation.realize_decode] using
      (M7.Presentation.targetLeast_spec
        (M7.ActualPresentation.Outer N) (Fin N) (Fin N)
        (Finset (ZMod N)) (Finset (ZMod N))
        Finset.univ Finset.univ Finset.univ
        (M7.ActualPresentation.leftImage c)
        (M7.ActualPresentation.rightImage c) q)
  have hm (g : M7.Action.Record N) :
      M7.ActualPresentation.leastAction c q = some g ↔
        t = some (M7.ActualPresentation.encode g) := by
    change Option.map M7.ActualPresentation.decode t = some g ↔
      t = some (M7.ActualPresentation.encode g)
    cases t with
    | none => simp
    | some a =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h
        rw [← h, M7.ActualPresentation.encode_decode N a]
      · intro h
        rw [h, M7.ActualPresentation.decode_encode N g]
  have hn : M7.ActualPresentation.leastAction c q = none ↔ t = none := by
    change Option.map M7.ActualPresentation.decode t = none ↔ t = none
    cases t <;> simp
  constructor
  · intro g
    rw [hm g, hs.1 (M7.ActualPresentation.encode g),
      M7.ActualPresentation.decode_encode N g]
    constructor
    · rintro ⟨hg, hmin⟩
      refine ⟨hg, ?_⟩
      intro h hh
      apply hmin (M7.ActualPresentation.encode h)
      simpa only [M7.ActualPresentation.decode_encode N h] using hh
    · rintro ⟨hg, hmin⟩
      refine ⟨hg, ?_⟩
      intro b hb
      simpa only [M7.ActualPresentation.encode_decode N b] using
        hmin (M7.ActualPresentation.decode b) hb
  · rw [hn, hs.2]
    constructor
    · intro h hex
      rcases hex with ⟨g, hg⟩
      apply h
      refine ⟨M7.ActualPresentation.encode g, ?_⟩
      simpa only [M7.ActualPresentation.decode_encode N g] using hg
    · intro h hex
      rcases hex with ⟨a, ha⟩
      exact h ⟨M7.ActualPresentation.decode a, ha⟩

theorem M7.ActualPresentation.presentation_exact : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g : M7.Action.Record N), g ∈ M7.ActualPresentation.selected c feasible objective mode → ∃! h : M7.Action.Record N, M7.ActualPresentation.present c feasible objective mode h ∧ M7.Action.act h c = M7.Action.act g c := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g : M7.Action.Record N), g ∈ M7.ActualPresentation.selected c feasible objective mode → ∃! h : M7.Action.Record N, M7.ActualPresentation.present c feasible objective mode h ∧ M7.Action.act h c = M7.Action.act g c
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst c m feasible objective mode g hg
  classical
  cases hl : M7.ActualPresentation.leastAction c (M7.Action.act g c) with
  | none =>
      exact False.elim ((M7.ActualPresentation.leastAction_spec N c
        (M7.Action.act g c)).2.mp hl ⟨g, rfl⟩)
  | some h =>
      have heq : M7.Action.act h c = M7.Action.act g c :=
        ((M7.ActualPresentation.leastAction_spec N c
          (M7.Action.act g c)).1 h).mp hl |>.1
      have hw : h ∈ M7.ActualPresentation.selected c feasible objective mode :=
        (M7.ActualPresentation.winning_fiber N c m feasible objective mode h g heq).mpr hg
      refine ⟨h, ⟨?_, heq⟩, ?_⟩
      · unfold M7.ActualPresentation.present
        refine ⟨hw, ?_⟩
        rw [heq]
        exact hl
      · intro k hk
        have hkLeast : M7.ActualPresentation.leastAction c (M7.Action.act k c) = some k :=
          hk.1.2
        rw [hk.2] at hkLeast
        exact Option.some.inj (hkLeast.symm.trans hl)

theorem M7.ActualPresentation.presentation_sound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g : M7.Action.Record N), M7.ActualPresentation.present c feasible objective mode g → g ∈ M7.ActualPresentation.selected c feasible objective mode ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = M7.Action.act g c → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g : M7.Action.Record N), M7.ActualPresentation.present c feasible objective mode g → g ∈ M7.ActualPresentation.selected c feasible objective mode ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = M7.Action.act g c → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst c m feasible objective mode g hg
  unfold M7.ActualPresentation.present at hg
  refine ⟨hg.1, ?_⟩
  exact (((M7.ActualPresentation.leastAction_spec N c (M7.Action.act g c)).1 g).mp hg.2).2
#print axioms M7.ActualPresentation.decode_encode
#print axioms M7.ActualPresentation.domain_univ
#print axioms M7.ActualPresentation.encode_decode
#print axioms M7.ActualPresentation.four_field_order
#print axioms M7.ActualPresentation.realize_decode
#print axioms M7.ActualPresentation.leastAction_spec
#print axioms M7.ActualPresentation.presentation_sound
#print axioms M7.ActualPresentation.winning_fiber
#print axioms M7.ActualPresentation.presentation_exact
