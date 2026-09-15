import M7GenerationCalls

theorem M7.GenerationCalls.trace_count : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).2 = 2*n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).2 = 2 * n
  intro c p n
  induction n generalizing p with
  | zero => simp [M7.GenerationCalls.traceMeasured]
  | succ n ih =>
      simp [M7.GenerationCalls.traceMeasured, ih, Nat.mul_succ, Nat.add_comm]

theorem M7.GenerationCalls.emission_count : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.GenerationCalls.emissionMeasured w E bases).2 = 2 * M7.PrefixBits.depth N := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), (M7.GenerationCalls.emissionMeasured w E bases).2 = 2 * M7.PrefixBits.depth N
  intro N inst w E bases
  change (M7.GenerationCalls.traceMeasured (M7.CompactGeneration.residual w E bases) [] (M7.PrefixBits.depth N)).2 = 2 * M7.PrefixBits.depth N
  exact M7.GenerationCalls.trace_count _ _ _
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).2.root = (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length + 1 ∧ (M7.GenerationCalls.runMeasured w E fuel bases root).2.children = 2 * M7.PrefixBits.depth N * (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length
