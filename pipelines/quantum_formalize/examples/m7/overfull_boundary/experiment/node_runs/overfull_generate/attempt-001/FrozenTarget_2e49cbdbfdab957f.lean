import M7OverfullBoundary

theorem M7.OverfullBoundary.class_impossible : ∀ (N w : ℕ) [NeZero N], N < w → ∀ c : M7.Action.Recipe N, ¬ M7.PrefixOrbit.ClassValid w c := by
  change ∀ (N w : ℕ) [NeZero N], N < w → ∀ c : M7.Action.Recipe N, ¬ M7.PrefixOrbit.ClassValid w c
  intro N w inst hN c hc
  have hcard : c.1.card = w := by
    unfold M7.PrefixOrbit.ClassValid at hc
    aesop
  have hbound := Finset.card_le_univ c.1
  have hle : c.1.card ≤ N := by
    simpa only [ZMod.card] using hbound
  omega
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N], ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w E).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w E).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w E).fuelExhausted = false
