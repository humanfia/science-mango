import M7GenerationCalls

theorem M7.GenerationCalls.trace_projection : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).1 = M7.DescentTrace.trace c p n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).1 = M7.DescentTrace.trace c p n
  intro c p n
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      simp [M7.GenerationCalls.traceMeasured, M7.DescentTrace.trace, ih]

theorem M7.GenerationCalls.emission_projection : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.GenerationCalls.emissionMeasured w E bases).1 = M7.CompactGeneration.emission w E bases := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), (M7.GenerationCalls.emissionMeasured w E bases).1 = M7.CompactGeneration.emission w E bases
  intro N inst w E bases
  simp [M7.GenerationCalls.emissionMeasured, M7.CompactGeneration.emission, M7.GenerationCalls.trace_projection, M7.DescentTrace.endpoint_recover]

theorem M7.GenerationCalls.run_projection : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).1 = M7.CompactGeneration.run w E fuel bases root := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).1 = M7.CompactGeneration.run w E fuel bases root
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero => rfl
  | succ fuel ih =>
      by_cases h : 0 < root
      · simp [M7.GenerationCalls.runMeasured, M7.CompactGeneration.run, h,
          M7.GenerationCalls.emission_projection, ih]
      · simp [M7.GenerationCalls.runMeasured, M7.CompactGeneration.run, h]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).2.orbitCounts ≤ (M7.GenerationCalls.runMeasured w E fuel bases root).1.finalBases.card * ((M7.GenerationCalls.runMeasured w E fuel bases root).2.root + (M7.GenerationCalls.runMeasured w E fuel bases root).2.children)
