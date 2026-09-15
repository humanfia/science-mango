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

theorem M7.ResiduePrefix.residue_roundtrip : ∀ (N : ℕ) [NeZero N], ∀ A : Finset (ZMod N), M7.ResiduePrefix.decode N (M7.ResiduePrefix.encode A) = A := by
  classical
  intro N hN A
  change (A.image (fun x : ZMod N => x.val)).image (fun i : ℕ => (i : ZMod N)) = A
  simp [Finset.image_image, ZMod.natCast_zmod_val]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ x : Finset (ZMod N) × Finset (ZMod N), x ∈ M7.ResiduePrefix.completed N w E A B WA WB ↔ M7.PrefixCompleted.Within A B WA WB (M7.ResiduePrefix.encodePair x) ∧ M7.PrefixCompleted.Valid N w E (M7.ResiduePrefix.encodePair x)
