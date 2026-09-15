import M7CompactGeneration

theorem M7.CompactGeneration.emission_action : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.Action.act (M7.CompactGeneration.emission w E bases).action (M7.CompactGeneration.emission w E bases).leaf = (M7.CompactGeneration.emission w E bases).representative ∧ M7.Action.act (M7.Action.inverse (M7.CompactGeneration.emission w E bases).action) (M7.CompactGeneration.emission w E bases).representative = (M7.CompactGeneration.emission w E bases).leaf := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.Action.act (M7.CompactGeneration.emission w E bases).action (M7.CompactGeneration.emission w E bases).leaf = (M7.CompactGeneration.emission w E bases).representative ∧ M7.Action.act (M7.Action.inverse (M7.CompactGeneration.emission w E bases).action) (M7.CompactGeneration.emission w E bases).representative = (M7.CompactGeneration.emission w E bases).leaf
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N hN w E bases
  dsimp only [M7.CompactGeneration.emission]
  constructor <;> exact?

theorem M7.CompactGeneration.emission_signature : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), (M7.CompactGeneration.emission w E bases).leafSignature = M7.RecipeSignature.signature (M7.CompactGeneration.emission w E bases).leaf ∧ (M7.CompactGeneration.emission w E bases).representativeSignature = M7.SignatureTau.sourceTau (M7.CompactGeneration.emission w E bases).action.unit (M7.CompactGeneration.emission w E bases).leafSignature := by
  intro N inst w E bases
  constructor
  · rfl
  · let c := (M7.CompactGeneration.emission w E bases).leaf
    change M7.RecipeSignature.signature (M7.CanonicalOuter.canonical c) =
      M7.SignatureTau.sourceTau (M7.CanonicalOuter.realizer c).unit
        (M7.RecipeSignature.signature c)
    have h : M7.Action.act (M7.CanonicalOuter.realizer c) c =
        M7.CanonicalOuter.canonical c := by
      first
      | exact M7.CanonicalOuter.realizer_spec N c
      | exact M7.CanonicalOuter.realizer_spec c
      | exact M7.CanonicalOuter.realizer_correct N c
      | exact M7.CanonicalOuter.realizer_correct c
      | exact M7.CanonicalOuter.realizer_action N c
      | exact M7.CanonicalOuter.realizer_action c
      | exact M7.CanonicalOuter.realizes N c
      | exact M7.CanonicalOuter.realizes c
      | unfold M7.CanonicalOuter.realizer
        exact Classical.choose_spec _
    rw [← h]
    exact M7.RecipeSignature.action_signature N c (M7.CanonicalOuter.realizer c)

theorem M7.CompactGeneration.emission_stabilizer : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), 0 < (M7.CompactGeneration.emission w E bases).stabilizer ∧ (M7.CompactGeneration.emission w E bases).stabilizer = M7.ActualOrbit.stabilizerCount (M7.CompactGeneration.emission w E bases).representative := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), 0 < (M7.CompactGeneration.emission w E bases).stabilizer ∧ (M7.CompactGeneration.emission w E bases).stabilizer = M7.ActualOrbit.stabilizerCount (M7.CompactGeneration.emission w E bases).representative
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases
  change 0 < M7.ActualFactorized.stabilizerNumerator (M7.CompactGeneration.emission w E bases).representative ∧ M7.ActualFactorized.stabilizerNumerator (M7.CompactGeneration.emission w E bases).representative = M7.ActualOrbit.stabilizerCount (M7.CompactGeneration.emission w E bases).representative
  constructor
  · rw [M7.ActualFactorized.stabilizer_numerator N]
    exact?
  · exact M7.ActualFactorized.stabilizer_numerator N _

theorem M7.CompactGeneration.emission_trace : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.DescentTrace.check (M7.CompactGeneration.residual w E bases) [] (M7.CompactGeneration.emission w E bases).path = (true, 2 * M7.PrefixBits.depth N) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.DescentTrace.check (M7.CompactGeneration.residual w E bases) [] (M7.CompactGeneration.emission w E bases).path = (true, 2 * M7.PrefixBits.depth N)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases
  change M7.DescentTrace.check (M7.CompactGeneration.residual w E bases) [] (M7.DescentTrace.trace (M7.CompactGeneration.residual w E bases) [] (M7.PrefixBits.depth N)) = (true, 2 * M7.PrefixBits.depth N)
  exact M7.DescentTrace.check_trace (M7.CompactGeneration.residual w E bases) [] (M7.PrefixBits.depth N)

theorem M7.CompactGeneration.run_contains : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), bases ⊆ (M7.CompactGeneration.run w E fuel bases root).finalBases := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), bases ⊆ (M7.CompactGeneration.run w E fuel bases root).finalBases
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero =>
      simpa only [M7.CompactGeneration.run] using (Finset.Subset.refl bases)
  | succ fuel ih =>
      by_cases h : 0 < root
      · simp only [M7.CompactGeneration.run, if_pos h]
        intro x hx
        apply ih (insert (M7.CompactGeneration.emission w E bases).representative bases)
          (M7.CompactGeneration.residual w E
            (insert (M7.CompactGeneration.emission w E bases).representative bases) [])
        exact Finset.mem_insert_of_mem hx
      · simpa only [M7.CompactGeneration.run, if_neg h] using (Finset.Subset.refl bases)

theorem M7.CompactGeneration.run_fold : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), (M7.CompactGeneration.run w E fuel bases root).finalBases = (M7.CompactGeneration.run w E fuel bases root).emitted.foldl (fun acc e => insert e.representative acc) bases := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), (M7.CompactGeneration.run w E fuel bases root).finalBases = (M7.CompactGeneration.run w E fuel bases root).emitted.foldl (fun acc e => insert e.representative acc) bases
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases h : 0 < root
      · simp only [M7.CompactGeneration.run, if_pos h, List.foldl_cons]
        exact ih _ _
      · simp only [M7.CompactGeneration.run, if_neg h, List.foldl_nil]

theorem M7.CompactGeneration.run_length : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), (M7.CompactGeneration.run w E fuel bases root).emitted.length ≤ fuel := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), (M7.CompactGeneration.run w E fuel bases root).emitted.length ≤ fuel
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases fuel root
  classical
  induction fuel generalizing bases root with
  | zero =>
      simp [M7.CompactGeneration.run]
  | succ fuel ih =>
      by_cases h : 0 < root
      · simp only [M7.CompactGeneration.run, if_pos h, List.length_cons]
        exact Nat.succ_le_succ (ih _ _)
      · simp [M7.CompactGeneration.run, h]

theorem M7.CompactGeneration.stop : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), root ≤ 0 → (M7.CompactGeneration.run w E fuel bases root).emitted = [] ∧ (M7.CompactGeneration.run w E fuel bases root).finalBases = bases ∧ (M7.CompactGeneration.run w E fuel bases root).finalResidual = root ∧ (M7.CompactGeneration.run w E fuel bases root).fuelExhausted = false := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), root ≤ 0 → (M7.CompactGeneration.run w E fuel bases root).emitted = [] ∧ (M7.CompactGeneration.run w E fuel bases root).finalBases = bases ∧ (M7.CompactGeneration.run w E fuel bases root).finalResidual = root ∧ (M7.CompactGeneration.run w E fuel bases root).fuelExhausted = false
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases fuel root hroot
  have hnonpos : ¬ (0 < root) := not_lt_of_ge hroot
  cases fuel <;> simp [M7.CompactGeneration.run, hnonpos]
#print axioms M7.CompactGeneration.emission_action
#print axioms M7.CompactGeneration.emission_signature
#print axioms M7.CompactGeneration.emission_stabilizer
#print axioms M7.CompactGeneration.emission_trace
#print axioms M7.CompactGeneration.run_contains
#print axioms M7.CompactGeneration.run_fold
#print axioms M7.CompactGeneration.run_length
#print axioms M7.CompactGeneration.stop
