import M7PrefixBitsAccepted
import M7PrefixOrbitAccepted
import M7RawCoverage

theorem M7.RawCoverage.root_within : ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)), M7.PrefixOrbit.Within (M7.PrefixBits.A N []) (M7.PrefixBits.WA N []) S ↔ (0 : ZMod N) ∈ S := by
  classical
  intro N inst S
  have hr := M7.PrefixBits.root N (NeZero.pos N)
  rw [hr.1, hr.2.2.1]
  change ({0} ⊆ S.image ZMod.val ∧
    S.image ZMod.val ⊆ {0} ∪ (Finset.range N \ {0})) ↔ (0 : ZMod N) ∈ S
  constructor
  · intro h
    have hz : 0 ∈ S.image ZMod.val := h.1 (Finset.mem_singleton_self 0)
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hz
    have ha0 : a = (0 : ZMod N) :=
      (ZMod.val_injective N) (by simpa only [ZMod.val_zero] using hav)
    simpa only [ha0] using ha
  · intro h
    constructor
    · apply Finset.singleton_subset_iff.mpr
      exact Finset.mem_image.mpr ⟨0, h, ZMod.val_zero⟩
    · intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      by_cases hz : a.val = 0
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_singleton.mpr hz)
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_range.mpr (ZMod.val_lt a), by simpa using hz⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) (c : M7.Action.Recipe N), c ∈ M7.RawCoverage.rootCompleted N w E ↔ M7.RawCoverage.Queried w E c ∧ (0 : ZMod N) ∈ c.1 ∧ (0 : ZMod N) ∈ c.2
