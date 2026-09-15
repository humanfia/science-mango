import FrozenTarget_3ae151e660a15c2f
theorem M7.CompactStorage.encode_core : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (e f : M7.CompactGeneration.Emission N), _
  intro N inst e f he hf h
  classical
  obtain ⟨hs, hv⟩ := M7.CompactStorage.support_value_injective N
  simp only [M7.CompactStorage.encode, M7.CompactStorage.Code.mk.injEq,
    hs.eq_iff, hv.eq_iff] at h
  rcases h with ⟨hl₁, hl₂, hr₁, hr₂, hu, hx, ha, hb, hp, hq, ht⟩
  have hl : e.leaf = f.leaf := Prod.ext hl₁ hl₂
  have hr : e.representative = f.representative := Prod.ext hr₁ hr₂
  have hu' : e.action.unit = f.action.unit := Units.ext hu
  have haction : e.action = f.action := by
    cases e.action
    cases f.action
    simp_all
  have hel : e.leafSignature.natDegree ≤ N := by
    have hbound := (M7.CompactStorage.field_bounds N e.leaf).1
    unfold M7.CompactStorage.Valid at he
    aesop
  have hfl : f.leafSignature.natDegree ≤ N := by
    have hbound := (M7.CompactStorage.field_bounds N f.leaf).1
    unfold M7.CompactStorage.Valid at hf
    aesop
  have her : e.representativeSignature.natDegree ≤ N := by
    have hbound := (M7.CompactStorage.field_bounds N e.representative).1
    unfold M7.CompactStorage.Valid at he
    aesop
  have hfr : f.representativeSignature.natDegree ≤ N := by
    have hbound := (M7.CompactStorage.field_bounds N f.representative).1
    unfold M7.CompactStorage.Valid at hf
    aesop
  have hsigl : e.leafSignature = f.leafSignature :=
    M7.CompactStorage.polynomial_injective N _ _ hel hfl hp
  have hsigr : e.representativeSignature = f.representativeSignature :=
    M7.CompactStorage.polynomial_injective N _ _ her hfr hq
  have hbe : e.stabilizer < 2 ^ (1 + 3 * N) := by
    have hbound := (M7.CompactStorage.field_bounds N e.representative).2
    unfold M7.CompactStorage.Valid at he
    aesop
  have hbf : f.stabilizer < 2 ^ (1 + 3 * N) := by
    have hbound := (M7.CompactStorage.field_bounds N f.representative).2
    unfold M7.CompactStorage.Valid at hf
    aesop
  have hstab : e.stabilizer = f.stabilizer := by
    have hnat := congrArg BitVec.toNat ht
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbe,
      Nat.mod_eq_of_lt hbf] using hnat
  simp only [M7.CompactStorage.coreView, hl, hr, haction, hsigl, hsigr, hstab]
