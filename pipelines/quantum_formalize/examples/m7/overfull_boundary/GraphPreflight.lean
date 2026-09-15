import M7OverfullBoundary
def target_0 : Prop := (∀ (N w : ℕ) [NeZero N], N < w → ∀ c : M7.Action.Recipe N, ¬ M7.PrefixOrbit.ClassValid w c)
def target_1 : Prop := (∀ (N w : ℕ) [NeZero N], ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w E).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w E).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w E).fuelExhausted = false)
def target_2 : Prop := (∀ (N w : ℕ) [NeZero N], 0 < w → M7.CompactGeneration.residual (N := N) w ∅ ∅ [] = 0)
def target_3 : Prop := (∀ (N w : ℕ) [NeZero N], 0 < w → (M7.CompactGeneration.generate (N := N) w ∅).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w ∅).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w ∅).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w ∅).fuelExhausted = false)
