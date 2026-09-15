import M7GeneratedFamily

theorem M7.GeneratedFamily.family_meets : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ i : Fin (M7.GeneratedFamily.size N w E), ∃ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g (M7.GeneratedFamily.family N w E i)) ∈ E := by
  classical
  intro N w inst E hw hwN hE i
  let e := (M7.CompactGeneration.generate (N := N) w E).emitted.get i
  have he : e ∈ (M7.CompactGeneration.generate (N := N) w E).emitted := List.get_mem _ _
  have hl : e.leaf ∈ M7.RecoveryPrefix.completed N w E [] := by
    apply M7.CompactCorrectness.run_leaves N w E hE ∅ _ _
      (M7.CompactCorrectness.initial N w E hE).1 rfl e
    exact he
  have hr := M7.CompactCorrectness.run_records N w E ∅ _ _ e he
  refine ⟨M7.Action.inverse e.action, ?_⟩
  change M7.RecipeSignature.signature (M7.Action.act (M7.Action.inverse e.action) e.representative) ∈ E
  rw [hr.2.1]
  have hq := ((M7.RawCoverage.root_membership N w E e.leaf).mp hl).1
  exact hq.2

theorem M7.GeneratedFamily.family_range : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ b : M7.Action.Recipe N, b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases ↔ ∃ i : Fin (M7.GeneratedFamily.size N w E), M7.GeneratedFamily.family N w E i = b := by
  classical
  intro N w inst E hw hwN hE b
  have hfold : ∀ {α : Type} (f : α → M7.Action.Recipe N) (l : List α)
      (s : Finset (M7.Action.Recipe N)),
      b ∈ l.foldl (fun t e => insert (f e) t) s ↔
        b ∈ s ∨ ∃ e ∈ l, f e = b := by
    intro α f l
    induction l with
    | nil => intro s; simp
    | cons a l ih =>
      intro s
      simp only [List.foldl_cons, ih, Finset.mem_insert, List.mem_cons]
      aesop
  have hf : (M7.CompactGeneration.generate (N := N) w E).finalBases =
      (M7.CompactGeneration.generate (N := N) w E).emitted.foldl
        (fun t e => insert e.representative t) ∅ := by
    dsimp only [M7.CompactGeneration.generate]
    first
    | apply M7.CompactGeneration.run_fold
    | symm; apply M7.CompactGeneration.run_fold
  change b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases ↔
    ∃ i : Fin (M7.CompactGeneration.generate (N := N) w E).emitted.length,
      ((M7.CompactGeneration.generate (N := N) w E).emitted.get i).representative = b
  rw [hf, hfold]
  simp only [Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨e, he, hb⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    exact ⟨i, by simpa only [hi] using hb⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, List.get_mem _ i, hi⟩

theorem M7.GeneratedFamily.family_good : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ i : Fin (M7.GeneratedFamily.size N w E), M7.PrefixOrbit.ClassValid w (M7.GeneratedFamily.family N w E i) ∧ M7.CanonicalOuter.canonical (M7.GeneratedFamily.family N w E i) = M7.GeneratedFamily.family N w E i := by
  classical
  intro N w inst E hw hwN hE i
  have hm : M7.GeneratedFamily.family N w E i ∈
      (M7.CompactGeneration.generate (N := N) w E).finalBases :=
    (M7.GeneratedFamily.family_range N w E hw hwN hE _).mpr ⟨i, rfl⟩
  have hg : M7.RecoveryInstance.GoodBases w
      (M7.CompactGeneration.generate (N := N) w E).finalBases := by
    have h := M7.CompactCorrectness.generate_exact N w E hE
    tauto
  simp only [M7.RecoveryInstance.GoodBases, M7.CanonicalClasses.Normalized] at hg
  aesop
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ c : M7.Action.Recipe N, (∃ (i : Fin (M7.GeneratedFamily.size N w E)) (g : M7.Action.Record N), M7.Action.act g (M7.GeneratedFamily.family N w E i) = c) ↔ M7.PrefixOrbit.ClassValid w c ∧ ∃ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g c) ∈ E
