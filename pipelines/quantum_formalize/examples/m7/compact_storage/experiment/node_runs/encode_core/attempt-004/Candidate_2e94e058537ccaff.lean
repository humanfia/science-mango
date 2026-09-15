import FrozenTarget_2e94e058537ccaff
theorem M7.CompactStorage.encode_core : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (e f : M7.CompactGeneration.Emission N), _
  intro N inst e f he hf h
  classical
  obtain ⟨hs, hv⟩ := M7.CompactStorage.support_value_injective N
  simp only [M7.CompactStorage.encode, M7.CompactStorage.Code.mk.injEq] at h
  have hl : e.leaf = f.leaf := by
    apply Prod.ext <;> apply hs <;> tauto
  have hr : e.representative = f.representative := by
    apply Prod.ext <;> apply hs <;> tauto
  have hu : e.action.unit = f.action.unit := by
    apply Units.ext
    apply hv
    tauto
  have hx : e.action.exchange = f.action.exchange := by tauto
  have ha : e.action.leftShift = f.action.leftShift := by
    apply hv
    tauto
  have hb : e.action.rightShift = f.action.rightShift := by
    apply hv
    tauto
  have hg : e.action = f.action := by
    cases hea : e.action
    cases hfa : f.action
    simp_all
  unfold M7.CompactStorage.Valid at he hf
  simp_all [M7.CompactStorage.coreView]
