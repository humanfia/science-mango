import M7GeneratedFamily

theorem M7.GeneratedFamily.family_injective : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → Function.Injective (M7.GeneratedFamily.family N w E) := by
  intro N w inst E hw hwN hE
  classical
  have hn := (M7.CompactCorrectness.generate_exact N w E hE).2.2.2
  have hl := List.Nodup.of_map (fun e : M7.CompactGeneration.Emission N => e.representative) hn
  intro i j hij
  apply hl.injective_get
  exact List.inj_on_of_nodup_map hn
    (List.get_mem (M7.CompactGeneration.generate (N := N) w E).emitted i)
    (List.get_mem (M7.CompactGeneration.generate (N := N) w E).emitted j) hij

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
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → M7.GlobalQuery.separated (M7.GeneratedFamily.family N w E)
