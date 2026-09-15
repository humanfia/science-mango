import FrozenTarget_a6fa39beb5abd3f6
theorem M7.GeneratedFamily.family_anchored : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E hw hwN hE i
  obtain ⟨hv, hn⟩ := M7.GeneratedFamily.family_good N w E hw hwN hE i
  have hl : (M7.GeneratedFamily.family N w E i).1.card = w := by
    unfold M7.PrefixOrbit.ClassValid at hv
    tauto
  have hr : (M7.GeneratedFamily.family N w E i).2.card = w := by
    unfold M7.PrefixOrbit.ClassValid at hv
    tauto
  have hln : (M7.GeneratedFamily.family N w E i).1.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hrn : (M7.GeneratedFamily.family N w E i).2.Nonempty :=
    Finset.card_pos.mp (by omega)
  rw [← hn]
  apply M7.CanonicalOuter.canonical_anchored <;> first | assumption | omega
