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

theorem M7.ResiduePrefix.encode_card : ∀ (N : ℕ) [NeZero N], ∀ A : Finset (ZMod N), (M7.ResiduePrefix.encode A).card = A.card := by
  intro N inst A
  change (M7.Supports.natSupport A).card = A.card
  rw [← M7.Supports.support N A]
  exact M7.Supports.support_card N A

theorem M7.ResiduePrefix.gcd_union : ∀ (N : ℕ) (A B : Finset ℕ), M5.Connectivity.supportGcd N A B = Nat.gcd N ((A ∪ B).gcd id) := by
  intro N A B
  change Nat.gcd N (Nat.gcd (A.gcd id) (B.gcd id)) = Nat.gcd N ((A ∪ B).gcd id)
  rw [Finset.gcd_union] <;> rfl

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

theorem M7.ResiduePrefix.polynomial_bridge : ∀ (N : ℕ) [NeZero N], ∀ A : Finset (ZMod N), M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode A) = M7.Supports.polynomial A := by
  classical
  intro N inst A
  unfold M7.ResiduePrefix.encode M7.Supports.natSupport M5.SupportPolynomial.ofSupport M7.Supports.polynomial
  rw [Finset.sum_image]
  intro a ha b hb hab
  have h := congrArg (fun k : ℕ => (k : ZMod N)) hab
  simpa only [ZMod.natCast_zmod_val] using h

theorem M7.ResiduePrefix.residue_roundtrip : ∀ (N : ℕ) [NeZero N], ∀ A : Finset (ZMod N), M7.ResiduePrefix.decode N (M7.ResiduePrefix.encode A) = A := by
  classical
  intro N hN A
  change (A.image (fun x : ZMod N => x.val)).image (fun i : ℕ => (i : ZMod N)) = A
  simp [Finset.image_image, ZMod.natCast_zmod_val]

theorem M7.ResiduePrefix.completed_membership : ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ x : Finset (ZMod N) × Finset (ZMod N), x ∈ M7.ResiduePrefix.completed N w E A B WA WB ↔ M7.PrefixCompleted.Within A B WA WB (M7.ResiduePrefix.encodePair x) ∧ M7.PrefixCompleted.Valid N w E (M7.ResiduePrefix.encodePair x) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ x : Finset (ZMod N) × Finset (ZMod N), x ∈ M7.ResiduePrefix.completed N w E A B WA WB ↔ M7.PrefixCompleted.Within A B WA WB (M7.ResiduePrefix.encodePair x) ∧ M7.PrefixCompleted.Valid N w E (M7.ResiduePrefix.encodePair x)
  intro N inst w E A B WA WB hBase x
  classical
  have hDA : Disjoint A WA := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  have hDB : Disjoint B WB := by
    unfold M7.PrefixCompleted.Base at hBase
    tauto
  unfold M7.ResiduePrefix.completed
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hb := M7.ResiduePrefix.completed_bounds N w E A B WA WB hBase y hy
    have hr : M7.ResiduePrefix.encodePair (M7.ResiduePrefix.decodePair N y) = y := by
      apply Prod.ext
      · exact M7.ResiduePrefix.nat_roundtrip N y.1 hb.1
      · exact M7.ResiduePrefix.nat_roundtrip N y.2 hb.2
    rw [← hxy, hr]
    exact (M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB y).mp hy
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨M7.ResiduePrefix.encodePair x, ?_, ?_⟩
    · exact (M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB (M7.ResiduePrefix.encodePair x)).mpr hx
    · apply Prod.ext
      · exact M7.ResiduePrefix.residue_roundtrip N x.1
      · exact M7.ResiduePrefix.residue_roundtrip N x.2

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

theorem M7.ResiduePrefix.signature_bridge : ∀ (N : ℕ) [NeZero N], ∀ A B : Finset (ZMod N), M5.completeSignature (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode A)) (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode B)) N = M6.Cyclic.signature (M7.Supports.polynomial A) (M7.Supports.polynomial B) (M6.Cyclic.modulus N) := by
  classical
  intro N inst A B
  rw [M7.ResiduePrefix.polynomial_bridge N A, M7.ResiduePrefix.polynomial_bridge N B]
  rfl

theorem M7.ResiduePrefix.count_completed : ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixSector.ValidSector N E → M7.PrefixCompleted.Base N A B WA WB → M7.PrefixSector.count N w E A B WA WB = (M7.ResiduePrefix.completed N w E A B WA WB).card := by
  intro N inst w E A B WA WB hSector hBase
  classical
  have hcard : ((M7.PrefixCompleted.completed N w E A B WA WB).image (M7.ResiduePrefix.decodePair N)).card = (M7.PrefixCompleted.completed N w E A B WA WB).card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    obtain ⟨hx₁, hx₂⟩ := M7.ResiduePrefix.completed_bounds N w E A B WA WB hBase x hx
    obtain ⟨hy₁, hy₂⟩ := M7.ResiduePrefix.completed_bounds N w E A B WA WB hBase y hy
    exact M7.ResiduePrefix.decode_injective N x y hx₁ hx₂ hy₁ hy₂ hxy
  change M7.PrefixSector.count N w E A B WA WB = ↑(((M7.PrefixCompleted.completed N w E A B WA WB).image (M7.ResiduePrefix.decodePair N)).card)
  rw [hcard]
  exact M7.PrefixCompleted.count_completed N w E A B WA WB (Nat.pos_of_ne_zero (NeZero.ne N)) hSector hBase
#print axioms M7.ResiduePrefix.completed_bounds
#print axioms M7.ResiduePrefix.encode_card
#print axioms M7.ResiduePrefix.gcd_union
#print axioms M7.ResiduePrefix.nat_roundtrip
#print axioms M7.ResiduePrefix.decode_injective
#print axioms M7.ResiduePrefix.count_completed
#print axioms M7.ResiduePrefix.polynomial_bridge
#print axioms M7.ResiduePrefix.residue_roundtrip
#print axioms M7.ResiduePrefix.completed_membership
#print axioms M7.ResiduePrefix.signature_bridge
