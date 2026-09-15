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

theorem M7.ActualPresentation.realize_decode : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (a : M7.ActualPresentation.Encoded N), M7.Presentation.realize (M7.ActualPresentation.leftImage c) (M7.ActualPresentation.rightImage c) a = M7.Action.act (M7.ActualPresentation.decode a) c := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (a : M7.ActualPresentation.Encoded N), M7.Presentation.realize (M7.ActualPresentation.leftImage c) (M7.ActualPresentation.rightImage c) a = M7.Action.act (M7.ActualPresentation.decode a) c
  intro N inst c a
  rfl

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g : M7.Action.Record N), M7.ActualPresentation.present c feasible objective mode g → g ∈ M7.ActualPresentation.selected c feasible objective mode ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = M7.Action.act g c → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h
