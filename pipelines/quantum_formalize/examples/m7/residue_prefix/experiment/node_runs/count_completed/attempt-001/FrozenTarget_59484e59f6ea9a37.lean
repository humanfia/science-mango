import M7ResiduePrefix

theorem M7.ResiduePrefix.completed_bounds : ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ x ∈ M7.PrefixCompleted.completed N w E A B WA WB, x.1 ⊆ Finset.range N ∧ x.2 ⊆ Finset.range N := by
  intro N inst w E A B WA WB hBase x hx
  have hDA : Disjoint A WA := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hDB : Disjoint B WB := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hWithin := ((M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB x).mp hx).1
  have hXA : x.1 ⊆ A ∪ WA := by
    unfold M7.PrefixCompleted.Within at hWithin
    tauto
  have hXB : x.2 ⊆ B ∪ WB := by
    unfold M7.PrefixCompleted.Within at hWithin
    tauto
  have hA : A ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hB : B ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hWA : WA ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hWB : WB ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  constructor
  · intro i hi
    rcases Finset.mem_union.mp (hXA hi) with h | h
    · exact hA h
    · exact hWA h
  · intro i hi
    rcases Finset.mem_union.mp (hXB hi) with h | h
    · exact hB h
    · exact hWB h

theorem M7.ResiduePrefix.nat_roundtrip : ∀ (N : ℕ) [NeZero N], ∀ A : Finset ℕ, A ⊆ Finset.range N → M7.ResiduePrefix.encode (M7.ResiduePrefix.decode N A) = A := by
  change ∀ (N : ℕ) [NeZero N], ∀ A : Finset ℕ, A ⊆ Finset.range N → M7.ResiduePrefix.encode (M7.ResiduePrefix.decode N A) = A
  intro N inst A hA
  classical
  change (A.image (fun i : ℕ => (i : ZMod N))).image ZMod.val = A
  rw [Finset.image_image]
  ext n
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, he⟩
    have hv : (i : ZMod N).val = i :=
      ZMod.val_natCast_of_lt (Finset.mem_range.mp (hA hi))
    rw [hv] at he
    exact he ▸ hi
  · intro hn
    exact ⟨n, hn, ZMod.val_natCast_of_lt (Finset.mem_range.mp (hA hn))⟩

theorem M7.ResiduePrefix.decode_injective : ∀ (N : ℕ) [NeZero N], ∀ (x y : Finset ℕ × Finset ℕ), x.1 ⊆ Finset.range N → x.2 ⊆ Finset.range N → y.1 ⊆ Finset.range N → y.2 ⊆ Finset.range N → M7.ResiduePrefix.decodePair N x = M7.ResiduePrefix.decodePair N y → x = y := by
  change ∀ (N : ℕ) [NeZero N], ∀ (x y : Finset ℕ × Finset ℕ), x.1 ⊆ Finset.range N → x.2 ⊆ Finset.range N → y.1 ⊆ Finset.range N → y.2 ⊆ Finset.range N → M7.ResiduePrefix.decodePair N x = M7.ResiduePrefix.decodePair N y → x = y
  intro N inst x y hx₁ hx₂ hy₁ hy₂ h
  apply Prod.ext
  · have h₁ := congrArg (fun p : Finset (ZMod N) × Finset (ZMod N) => M7.ResiduePrefix.encode p.1) h
    change M7.ResiduePrefix.encode (M7.ResiduePrefix.decode N x.1) = M7.ResiduePrefix.encode (M7.ResiduePrefix.decode N y.1) at h₁
    rw [M7.ResiduePrefix.nat_roundtrip N x.1 hx₁, M7.ResiduePrefix.nat_roundtrip N y.1 hy₁] at h₁
    exact h₁
  · have h₂ := congrArg (fun p : Finset (ZMod N) × Finset (ZMod N) => M7.ResiduePrefix.encode p.2) h
    change M7.ResiduePrefix.encode (M7.ResiduePrefix.decode N x.2) = M7.ResiduePrefix.encode (M7.ResiduePrefix.decode N y.2) at h₂
    rw [M7.ResiduePrefix.nat_roundtrip N x.2 hx₂, M7.ResiduePrefix.nat_roundtrip N y.2 hy₂] at h₂
    exact h₂
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixSector.ValidSector N E → M7.PrefixCompleted.Base N A B WA WB → M7.PrefixSector.count N w E A B WA WB = (M7.ResiduePrefix.completed N w E A B WA WB).card
