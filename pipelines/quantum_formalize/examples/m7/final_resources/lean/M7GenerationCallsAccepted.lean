import M7GenerationCalls

theorem M7.GenerationCalls.trace_count : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).2 = 2*n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).2 = 2 * n
  intro c p n
  induction n generalizing p with
  | zero => simp [M7.GenerationCalls.traceMeasured]
  | succ n ih =>
      simp [M7.GenerationCalls.traceMeasured, ih, Nat.mul_succ, Nat.add_comm]

theorem M7.GenerationCalls.trace_projection : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).1 = M7.DescentTrace.trace c p n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).1 = M7.DescentTrace.trace c p n
  intro c p n
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      simp [M7.GenerationCalls.traceMeasured, M7.DescentTrace.trace, ih]

theorem M7.GenerationCalls.emission_count : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.GenerationCalls.emissionMeasured w E bases).2 = 2 * M7.PrefixBits.depth N := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), (M7.GenerationCalls.emissionMeasured w E bases).2 = 2 * M7.PrefixBits.depth N
  intro N inst w E bases
  change (M7.GenerationCalls.traceMeasured (M7.CompactGeneration.residual w E bases) [] (M7.PrefixBits.depth N)).2 = 2 * M7.PrefixBits.depth N
  exact M7.GenerationCalls.trace_count _ _ _

theorem M7.GenerationCalls.emission_projection : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.GenerationCalls.emissionMeasured w E bases).1 = M7.CompactGeneration.emission w E bases := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), (M7.GenerationCalls.emissionMeasured w E bases).1 = M7.CompactGeneration.emission w E bases
  intro N inst w E bases
  simp [M7.GenerationCalls.emissionMeasured, M7.CompactGeneration.emission, M7.GenerationCalls.trace_projection, M7.DescentTrace.endpoint_recover]

theorem M7.GenerationCalls.run_count : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).2.root = (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length + 1 ∧ (M7.GenerationCalls.runMeasured w E fuel bases root).2.children = 2 * M7.PrefixBits.depth N * (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).2.root = (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length + 1 ∧ (M7.GenerationCalls.runMeasured w E fuel bases root).2.children = 2 * M7.PrefixBits.depth N * (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero => simp [M7.GenerationCalls.runMeasured]
  | succ fuel ih =>
      by_cases h : 0 < root
      · obtain ⟨hr, hc⟩ := ih
          (insert (M7.GenerationCalls.emissionMeasured w E bases).1.representative bases)
          (M7.CompactGeneration.residual w E
            (insert (M7.GenerationCalls.emissionMeasured w E bases).1.representative bases) [])
        simp only [M7.GenerationCalls.runMeasured, if_pos h, List.length_cons]
        simp [hr, hc, M7.GenerationCalls.emission_count, Nat.mul_add,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · simp [M7.GenerationCalls.runMeasured, h]

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

theorem M7.GenerationCalls.run_orbit_bound : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).2.orbitCounts ≤ (M7.GenerationCalls.runMeasured w E fuel bases root).1.finalBases.card * ((M7.GenerationCalls.runMeasured w E fuel bases root).2.root + (M7.GenerationCalls.runMeasured w E fuel bases root).2.children) := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).2.orbitCounts ≤ (M7.GenerationCalls.runMeasured w E fuel bases root).1.finalBases.card * ((M7.GenerationCalls.runMeasured w E fuel bases root).2.root + (M7.GenerationCalls.runMeasured w E fuel bases root).2.children)
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero => simp [M7.GenerationCalls.runMeasured]
  | succ fuel ih =>
      by_cases h : 0 < root
      · let measured := M7.GenerationCalls.emissionMeasured w E bases
        let nextBases := insert measured.1.representative bases
        let nextRoot := M7.CompactGeneration.residual w E nextBases []
        let tail := M7.GenerationCalls.runMeasured w E fuel nextBases nextRoot
        have htail : tail.2.orbitCounts ≤ tail.1.finalBases.card * (tail.2.root + tail.2.children) :=
          ih nextBases nextRoot
        have hcontains : nextBases ⊆ tail.1.finalBases := by
          change nextBases ⊆ (M7.GenerationCalls.runMeasured w E fuel nextBases nextRoot).1.finalBases
          rw [M7.GenerationCalls.run_projection]
          exact M7.CompactGeneration.run_contains N w E nextBases fuel nextRoot
        have hcard : bases.card ≤ tail.1.finalBases.card := by
          apply Finset.card_le_card
          exact (Finset.subset_insert _ _).trans hcontains
        simp only [M7.GenerationCalls.runMeasured, if_pos h]
        change bases.card * (1 + measured.2) + tail.2.orbitCounts ≤ tail.1.finalBases.card * ((1 + tail.2.root) + (measured.2 + tail.2.children))
        calc
          bases.card * (1 + measured.2) + tail.2.orbitCounts ≤
              tail.1.finalBases.card * (1 + measured.2) + tail.1.finalBases.card * (tail.2.root + tail.2.children) :=
            Nat.add_le_add (Nat.mul_le_mul_right _ hcard) htail
          _ = tail.1.finalBases.card * ((1 + tail.2.root) + (measured.2 + tail.2.children)) := by ring
      · simp [M7.GenerationCalls.runMeasured, h]

theorem M7.GenerationCalls.generate_count : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), (M7.GenerationCalls.generateMeasured (N := N) w E).1 = (M7.CompactGeneration.generate (N := N) w E) ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.root + (M7.GenerationCalls.generateMeasured (N := N) w E).2.children = (1 + (M7.CompactGeneration.generate (N := N) w E).emitted.length * (2 * M7.PrefixBits.depth N + 1)) ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.orbitCounts ≤ (M7.CompactGeneration.generate (N := N) w E).finalBases.card * (1 + (M7.CompactGeneration.generate (N := N) w E).emitted.length * (2 * M7.PrefixBits.depth N + 1)) := by
  intro N inst w E
  classical
  let root := M7.CompactGeneration.residual w E (∅ : Finset (M7.Action.Recipe N)) []
  have hp : (M7.GenerationCalls.generateMeasured (N := N) w E).1 = M7.CompactGeneration.generate (N := N) w E := by
    unfold M7.GenerationCalls.generateMeasured M7.CompactGeneration.generate
    exact M7.GenerationCalls.run_projection N w E _ _ _
  have hcount := M7.GenerationCalls.run_count N w E ∅ root.toNat root
  change (M7.GenerationCalls.generateMeasured (N := N) w E).2.root = (M7.GenerationCalls.generateMeasured (N := N) w E).1.emitted.length + 1 ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.children = 2 * M7.PrefixBits.depth N * (M7.GenerationCalls.generateMeasured (N := N) w E).1.emitted.length at hcount
  have hs : (M7.GenerationCalls.generateMeasured (N := N) w E).2.root + (M7.GenerationCalls.generateMeasured (N := N) w E).2.children = 1 + (M7.CompactGeneration.generate (N := N) w E).emitted.length * (2 * M7.PrefixBits.depth N + 1) := by
    rw [hcount.1, hcount.2, hp]
    ring
  have hb := M7.GenerationCalls.run_orbit_bound N w E ∅ root.toNat root
  change (M7.GenerationCalls.generateMeasured (N := N) w E).2.orbitCounts ≤ (M7.GenerationCalls.generateMeasured (N := N) w E).1.finalBases.card * ((M7.GenerationCalls.generateMeasured (N := N) w E).2.root + (M7.GenerationCalls.generateMeasured (N := N) w E).2.children) at hb
  rw [hp, hs] at hb
  exact ⟨hp, hs, hb⟩
#print axioms M7.GenerationCalls.trace_count
#print axioms M7.GenerationCalls.emission_count
#print axioms M7.GenerationCalls.run_count
#print axioms M7.GenerationCalls.trace_projection
#print axioms M7.GenerationCalls.emission_projection
#print axioms M7.GenerationCalls.run_projection
#print axioms M7.GenerationCalls.run_orbit_bound
#print axioms M7.GenerationCalls.generate_count
