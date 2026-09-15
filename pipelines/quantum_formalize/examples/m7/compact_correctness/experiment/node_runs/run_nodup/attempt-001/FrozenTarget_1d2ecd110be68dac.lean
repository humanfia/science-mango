import M7CompactCorrectness

theorem M7.CompactCorrectness.residual_eq : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (p : List Bool), M7.CompactGeneration.residual w E bases p = M7.RecoveryInstance.count w E bases p := by
  intro N inst w E bases p
  rfl

theorem M7.CompactCorrectness.emission_eq : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.CompactGeneration.emission w E bases).leaf = M7.RecoveryInstance.recoverLeaf w E bases ∧ insert (M7.CompactGeneration.emission w E bases).representative bases = M7.RecoveryInstance.insertedBases w E bases := by
  intro N inst w E bases
  constructor <;> rfl

theorem M7.CompactCorrectness.run_disjoint : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), M7.RecoveryInstance.GoodBases w bases → root = M7.CompactGeneration.residual w E bases [] → ∀ e ∈ (M7.CompactGeneration.run w E fuel bases root).emitted, e.representative ∉ bases := by
  classical
  intro N inst w E hE bases fuel
  induction fuel generalizing bases with
  | zero =>
      intro root hb hr e he
      simpa [M7.CompactGeneration.run] using he
  | succ fuel ih =>
      intro root hb hr e he
      by_cases hp : 0 < root
      · have hc : 0 < M7.RecoveryInstance.count w E bases [] := by
          rw [hr, M7.CompactCorrectness.residual_eq] at hp
          exact hp
        have hg := M7.RecoveryInstance.insert_good N w E bases hE hb hc
        have hb' : M7.RecoveryInstance.GoodBases w
            (insert (M7.CompactGeneration.emission w E bases).representative bases) := by
          rw [(M7.CompactCorrectness.emission_eq N w E bases).2]
          exact hg.1
        simp only [M7.CompactGeneration.run, if_pos hp, List.mem_cons] at he
        rcases he with he | he
        · subst e
          exact hg.2
        · have hf := ih
              (insert (M7.CompactGeneration.emission w E bases).representative bases)
              (M7.CompactGeneration.residual w E
                (insert (M7.CompactGeneration.emission w E bases).representative bases) [])
              hb' rfl e he
          intro hm
          exact hf (Finset.mem_insert_of_mem hm)
      · simp [M7.CompactGeneration.run, hp] at he
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), M7.RecoveryInstance.GoodBases w bases → root = M7.CompactGeneration.residual w E bases [] → ((M7.CompactGeneration.run w E fuel bases root).emitted.map (fun e => e.representative)).Nodup
