import FrozenTarget_d69a705014fefb21
theorem M7.CompactStorage.encode_core : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (e f : M7.CompactGeneration.Emission N), M7.CompactStorage.Valid e → M7.CompactStorage.Valid f → M7.CompactStorage.encode e = M7.CompactStorage.encode f → M7.CompactStorage.coreView e = M7.CompactStorage.coreView f
  intro N inst e f he hf h
  classical
  have hs := (M7.CompactStorage.support_value_injective N).1
  have hv := (M7.CompactStorage.support_value_injective N).2
  unfold M7.CompactStorage.encode at h
  simp only [M7.CompactStorage.Code.mk.injEq, hs.eq_iff, hv.eq_iff] at h
  repeat' match goal with
  | h' : _ ∧ _ ⊢ _ => rcases h' with ⟨h1, h2⟩
  have hl : e.leaf = f.leaf := by
    apply Prod.ext <;> assumption
  have hr : e.representative = f.representative := by
    apply Prod.ext <;> assumption
  have ha : e.action = f.action := by
    cases ea : e.action
    cases fa : f.action
    simp only [ea, fa] at *
    congr 1 <;> first | assumption | exact Units.ext (by assumption)
  unfold M7.CompactStorage.Valid at he hf
  simp_all [M7.CompactStorage.coreView]
