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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c q : M7.Action.Recipe N), (∀ g : M7.Action.Record N, M7.ActualPresentation.leastAction c q = some g ↔ M7.Action.act g c = q ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = q → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h) ∧ (M7.ActualPresentation.leastAction c q = none ↔ ¬ ∃ g : M7.Action.Record N, M7.Action.act g c = q)
