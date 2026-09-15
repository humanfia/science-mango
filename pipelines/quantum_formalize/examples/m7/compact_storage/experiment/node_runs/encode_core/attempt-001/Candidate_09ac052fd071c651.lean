import FrozenTarget_09ac052fd071c651
theorem M7.CompactStorage.encode_core : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (e f : M7.CompactGeneration.Emission N), M7.CompactStorage.Valid e → M7.CompactStorage.Valid f → M7.CompactStorage.encode e = M7.CompactStorage.encode f → M7.CompactStorage.coreView e = M7.CompactStorage.coreView f
  intro N inst e f he hf h
  classical
  obtain ⟨hs, hv⟩ := M7.CompactStorage.support_value_injective N
  have hu : Function.Injective (fun u : (ZMod N)ˣ => M7.CompactStorage.valueBits (u : ZMod N)) := by
    intro u v huv
    exact Units.ext (hv huv)
  cases e
  cases f
  cases_type M7.Action.Record
   dsimp only [M7.CompactStorage.encode] at h
  injection h
  simp_all [M7.CompactStorage.Valid, M7.CompactStorage.coreView, hs.eq_iff, hv.eq_iff, hu.eq_iff]
