import M7CompactCorrectness

theorem M7.CompactCorrectness.residual_eq : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (p : List Bool), M7.CompactGeneration.residual w E bases p = M7.RecoveryInstance.count w E bases p := by
  intro N inst w E bases p
  rfl

theorem M7.CompactCorrectness.run_cache : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), root = M7.CompactGeneration.residual w E bases [] → (M7.CompactGeneration.run w E fuel bases root).finalResidual = M7.CompactGeneration.residual w E (M7.CompactGeneration.run w E fuel bases root).finalBases [] := by
  intro N inst w E bases fuel root hroot
  induction fuel generalizing bases root with
  | zero =>
      simpa [M7.CompactGeneration.run] using hroot
  | succ fuel ih =>
      simp only [M7.CompactGeneration.run]
      split <;> dsimp only
      · first | exact hroot | exact ih _ _ rfl
      · first | exact hroot | exact ih _ _ rfl

theorem M7.CompactCorrectness.run_records : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), ∀ e ∈ (M7.CompactGeneration.run w E fuel bases root).emitted, M7.Action.act e.action e.leaf = e.representative ∧ M7.Action.act (M7.Action.inverse e.action) e.representative = e.leaf ∧ e.leafSignature = M7.RecipeSignature.signature e.leaf ∧ e.representativeSignature = M7.RecipeSignature.signature e.representative ∧ e.stabilizer = M7.ActualFactorized.stabilizerNumerator e.representative ∧ 0 < e.stabilizer := by
  classical
  intro N inst w E bases fuel root e he
  induction fuel generalizing bases root with
  | zero =>
      simpa [M7.CompactGeneration.run] using he
  | succ fuel ih =>
      simp only [M7.CompactGeneration.run] at he
      split at he <;> simp only [List.mem_cons, List.not_mem_nil] at he
      all_goals first | contradiction | skip
      all_goals rcases he with rfl | he
      · exact ⟨(M7.CompactGeneration.emission_action N w E bases).1,
          (M7.CompactGeneration.emission_action N w E bases).2,
          rfl, rfl, rfl,
          (M7.CompactGeneration.emission_stabilizer N w E bases).1⟩
      · exact ih _ _ he

theorem M7.CompactCorrectness.emission_eq : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.CompactGeneration.emission w E bases).leaf = M7.RecoveryInstance.recoverLeaf w E bases ∧ insert (M7.CompactGeneration.emission w E bases).representative bases = M7.RecoveryInstance.insertedBases w E bases := by
  intro N inst w E bases
  constructor <;> rfl

theorem M7.CompactCorrectness.initial : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w (∅ : Finset (M7.Action.Recipe N)) ∧ 0 ≤ M7.CompactGeneration.residual w E (∅ : Finset (M7.Action.Recipe N)) [] := by
  intro N inst w E hE
  have hgood : M7.RecoveryInstance.GoodBases w (∅ : Finset (M7.Action.Recipe N)) := by
    simp [M7.RecoveryInstance.GoodBases, M7.CanonicalClasses.Normalized]
  refine ⟨hgood, ?_⟩
  rw [M7.CompactCorrectness.residual_eq]
  exact (M7.RecoveryInstance.count_card N w E ∅ hE hgood []).2.2

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

theorem M7.CompactCorrectness.run_good : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), M7.RecoveryInstance.GoodBases w bases → root = M7.CompactGeneration.residual w E bases [] → M7.RecoveryInstance.GoodBases w (M7.CompactGeneration.run w E fuel bases root).finalBases := by
  intro N inst w E hE bases fuel root hgood hroot
  induction fuel generalizing bases root with
  | zero =>
      simpa [M7.CompactGeneration.run] using hgood
  | succ fuel ih =>
      simp only [M7.CompactGeneration.run]
      split
      all_goals first
      | exact hgood
      | have hpos : 0 < M7.RecoveryInstance.count w E bases [] := by
          change 0 < M7.CompactGeneration.residual w E bases []
          omega
        have hins := (M7.RecoveryInstance.insert_good N w E bases hE hgood hpos).1
        apply ih
        · change M7.RecoveryInstance.GoodBases w (M7.RecoveryInstance.insertedBases w E bases)
          exact hins
        · rfl

theorem M7.CompactCorrectness.run_leaves : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), M7.RecoveryInstance.GoodBases w bases → root = M7.CompactGeneration.residual w E bases [] → ∀ e ∈ (M7.CompactGeneration.run w E fuel bases root).emitted, e.leaf ∈ M7.RecoveryPrefix.completed N w E [] := by
  intro N inst w E hE bases fuel root hgood hroot
  induction fuel generalizing bases root with
  | zero =>
      intro e he
      simpa [M7.CompactGeneration.run] using he
  | succ fuel ih =>
      intro e he
      by_cases hp : 0 < root
      · have hc : 0 < M7.RecoveryInstance.count w E bases [] := by
          simpa only [hroot, M7.CompactCorrectness.residual_eq] using hp
        simp only [M7.CompactGeneration.run, if_pos hp,
          if_neg (not_le.mpr hp), List.mem_cons] at he
        rcases he with he | he
        · subst e
          rw [(M7.CompactCorrectness.emission_eq N w E bases).1]
          exact M7.RecoveryPrefix.completed_subroot N w E _
            (M7.RecoveryInstance.fresh_leaf N w E bases hE hgood hc).2
        · apply ih _ _ ?_ rfl e he
          rw [(M7.CompactCorrectness.emission_eq N w E bases).2]
          exact (M7.RecoveryInstance.insert_good N w E bases hE hgood hc).1
      · simpa [M7.CompactGeneration.run, hp, le_of_not_gt hp] using he

theorem M7.CompactCorrectness.run_zero : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), M7.RecoveryInstance.GoodBases w bases → root = M7.CompactGeneration.residual w E bases [] → root.toNat ≤ fuel → (M7.CompactGeneration.run w E fuel bases root).finalResidual = 0 ∧ (M7.CompactGeneration.run w E fuel bases root).fuelExhausted = false := by
  intro N inst w E hE bases fuel root hb hr hf
  classical
  induction fuel generalizing bases root with
  | zero =>
      have hn := (M7.RecoveryInstance.count_card N w E bases hE hb []).2.2
      have hc : root = M7.RecoveryInstance.count w E bases [] :=
        hr.trans (M7.CompactCorrectness.residual_eq N w E bases [])
      have hz : root = 0 := by omega
      have hs := M7.CompactGeneration.stop N w E bases 0 root (by omega)
      exact ⟨hs.2.2.1.trans hz, hs.2.2.2⟩
  | succ fuel ih =>
      have hc : root = M7.RecoveryInstance.count w E bases [] :=
        hr.trans (M7.CompactCorrectness.residual_eq N w E bases [])
      by_cases hp : 0 < root
      · have hpos : 0 < M7.RecoveryInstance.count w E bases [] := by omega
        have hg := (M7.RecoveryInstance.insert_good N w E bases hE hb hpos).1
        have hd := (M7.RecoveryInstance.strict_decrease N w E bases hE hb hpos).2
        have hbound :
            (M7.CompactGeneration.residual w E
              (M7.RecoveryInstance.insertedBases w E bases) []).toNat ≤ fuel := by
          rw [M7.CompactCorrectness.residual_eq N w E]
          omega
        have hi := ih (M7.RecoveryInstance.insertedBases w E bases)
          (M7.CompactGeneration.residual w E
            (M7.RecoveryInstance.insertedBases w E bases) []) hg rfl hbound
        simpa only [M7.CompactGeneration.run, if_pos hp,
          (M7.CompactCorrectness.emission_eq N w E bases).2] using hi
      · have hn := (M7.RecoveryInstance.count_card N w E bases hE hb []).2.2
        have hz : root = 0 := by omega
        have hs := M7.CompactGeneration.stop N w E bases (fuel + 1) root (by omega)
        exact ⟨hs.2.2.1.trans hz, hs.2.2.2⟩

theorem M7.CompactCorrectness.run_nodup : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), M7.RecoveryInstance.GoodBases w bases → root = M7.CompactGeneration.residual w E bases [] → ((M7.CompactGeneration.run w E fuel bases root).emitted.map (fun e => e.representative)).Nodup := by
  classical
  intro N inst w E hE bases fuel
  induction fuel generalizing bases with
  | zero =>
      intro root hb hr
      simp [M7.CompactGeneration.run]
  | succ fuel ih =>
      intro root hb hr
      by_cases hp : 0 < root
      · have hc : 0 < M7.RecoveryInstance.count w E bases [] := by
          rw [hr, M7.CompactCorrectness.residual_eq] at hp
          exact hp
        have hg := M7.RecoveryInstance.insert_good N w E bases hE hb hc
        have hb' : M7.RecoveryInstance.GoodBases w
            (insert (M7.CompactGeneration.emission w E bases).representative bases) := by
          rw [(M7.CompactCorrectness.emission_eq N w E bases).2]
          exact hg.1
        simp only [M7.CompactGeneration.run, if_pos hp, List.map_cons, List.nodup_cons]
        constructor
        · intro hm
          rcases List.mem_map.mp hm with ⟨e, he, heq⟩
          have hf := M7.CompactCorrectness.run_disjoint N w E hE
            (insert (M7.CompactGeneration.emission w E bases).representative bases)
            fuel
            (M7.CompactGeneration.residual w E
              (insert (M7.CompactGeneration.emission w E bases).representative bases) [])
            hb' rfl e he
          apply hf
          rw [heq]
          exact Finset.mem_insert_self _ _
        · exact ih _ _ hb' rfl
      · simp [M7.CompactGeneration.run, hp]

theorem M7.CompactCorrectness.generate_exact : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w (M7.CompactGeneration.generate (N := N) w E).finalBases ∧ (M7.CompactGeneration.generate (N := N) w E).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w E).fuelExhausted = false ∧ ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).Nodup := by
  intro N inst w E hE
  have hb := (M7.CompactCorrectness.initial N w E hE).1
  let root := M7.CompactGeneration.residual (N := N) w E ∅ []
  have hg := M7.CompactCorrectness.run_good N w E hE ∅ root.toNat root hb rfl
  have hz := M7.CompactCorrectness.run_zero N w E hE ∅ root.toNat root hb rfl (le_refl _)
  have hn := M7.CompactCorrectness.run_nodup N w E hE ∅ root.toNat root hb rfl
  simpa only [M7.CompactGeneration.generate, root] using
    And.intro hg (And.intro hz.1 (And.intro hz.2 hn))

theorem M7.CompactCorrectness.generate_card : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → (M7.CompactGeneration.generate (N := N) w E).finalBases.card = (M7.CompactGeneration.generate (N := N) w E).emitted.length := by
  classical
  intro N inst w E hE
  have hcard : ∀ (fuel : ℕ) (bases : Finset (M7.Action.Recipe N)) (root : ℤ),
      M7.RecoveryInstance.GoodBases w bases →
      root = M7.CompactGeneration.residual w E bases [] →
      (M7.CompactGeneration.run w E fuel bases root).finalBases.card =
        bases.card + (M7.CompactGeneration.run w E fuel bases root).emitted.length := by
    intro fuel
    induction fuel with
    | zero =>
        intro bases root hb hr
        simp [M7.CompactGeneration.run]
    | succ fuel ih =>
        intro bases root hb hr
        by_cases hp : 0 < root
        · have hc : 0 < M7.RecoveryInstance.count w E bases [] := by
            rw [hr, M7.CompactCorrectness.residual_eq] at hp
            exact hp
          have hg := M7.RecoveryInstance.insert_good N w E bases hE hb hc
          have hb' : M7.RecoveryInstance.GoodBases w
              (insert (M7.CompactGeneration.emission w E bases).representative bases) := by
            rw [(M7.CompactCorrectness.emission_eq N w E bases).2]
            exact hg.1
          have hf : (M7.CompactGeneration.emission w E bases).representative ∉ bases := hg.2
          simp only [M7.CompactGeneration.run, if_pos hp, List.length_cons]
          rw [ih _ _ hb' rfl, Finset.card_insert_of_notMem hf]
          omega
        · simp [M7.CompactGeneration.run, hp]
  let root := M7.CompactGeneration.residual (N := N) w E ∅ []
  have h := hcard root.toNat ∅ root (M7.CompactCorrectness.initial N w E hE).1 rfl
  simpa only [M7.CompactGeneration.generate, root, Finset.card_empty, Nat.zero_add] using h

theorem M7.CompactCorrectness.generate_coverage : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ y ∈ M7.RecoveryPrefix.completed N w E [], y ∈ M7.OrbitResidual.covered (M7.CompactGeneration.generate (N := N) w E).finalBases := by
  intro N inst w E hE
  have hx := M7.CompactCorrectness.generate_exact N w E hE
  have hc : (M7.CompactGeneration.generate (N := N) w E).finalResidual =
      M7.CompactGeneration.residual w E
        (M7.CompactGeneration.generate (N := N) w E).finalBases [] := by
    simpa only [M7.CompactGeneration.generate] using
      (M7.CompactCorrectness.run_cache N w E ∅
        (M7.CompactGeneration.residual (N := N) w E ∅ []).toNat
        (M7.CompactGeneration.residual (N := N) w E ∅ []) rfl)
  apply (M7.RecoveryInstance.root_zero N w E
    (M7.CompactGeneration.generate (N := N) w E).finalBases hE hx.1).mp
  rw [M7.CompactCorrectness.residual_eq] at hc
  exact hc.symm.trans hx.2.1
#print axioms M7.CompactCorrectness.residual_eq
#print axioms M7.CompactCorrectness.emission_eq
#print axioms M7.CompactCorrectness.initial
#print axioms M7.CompactCorrectness.run_cache
#print axioms M7.CompactCorrectness.run_disjoint
#print axioms M7.CompactCorrectness.run_good
#print axioms M7.CompactCorrectness.run_leaves
#print axioms M7.CompactCorrectness.run_nodup
#print axioms M7.CompactCorrectness.run_records
#print axioms M7.CompactCorrectness.run_zero
#print axioms M7.CompactCorrectness.generate_exact
#print axioms M7.CompactCorrectness.generate_card
#print axioms M7.CompactCorrectness.generate_coverage
