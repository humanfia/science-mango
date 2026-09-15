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

theorem M7.GeneratedFamily.family_anchored : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ i : Fin (M7.GeneratedFamily.size N w E), (0 : ZMod N) ∈ (M7.GeneratedFamily.family N w E i).1 ∧ (0 : ZMod N) ∈ (M7.GeneratedFamily.family N w E i).2 := by
  classical
  intro N w inst E hw hwN hE i
  obtain ⟨hv, hn⟩ := M7.GeneratedFamily.family_good N w E hw hwN hE i
  have hl : (M7.GeneratedFamily.family N w E i).1.card = w := by
    unfold M7.PrefixOrbit.ClassValid at hv
    tauto
  have hr : (M7.GeneratedFamily.family N w E i).2.card = w := by
    unfold M7.PrefixOrbit.ClassValid at hv
    tauto
  have hln : (M7.GeneratedFamily.family N w E i).1.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hrn : (M7.GeneratedFamily.family N w E i).2.Nonempty :=
    Finset.card_pos.mp (by omega)
  rw [← hn]
  apply M7.CanonicalOuter.canonical_anchored <;> first | assumption | omega

theorem M7.GeneratedFamily.family_complete : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ c : M7.Action.Recipe N, (∃ (i : Fin (M7.GeneratedFamily.size N w E)) (g : M7.Action.Record N), M7.Action.act g (M7.GeneratedFamily.family N w E i) = c) ↔ M7.PrefixOrbit.ClassValid w c ∧ ∃ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g c) ∈ E := by
  classical
  intro N w inst E hw hwN hE c
  have hcomp : ∀ (g h : M7.Action.Record N) (b : M7.Action.Recipe N),
      M7.Action.act (M7.Action.compose g h) b = M7.Action.act g (M7.Action.act h b) := by
    intro g h b
    exact?
  have hinv : ∀ (g : M7.Action.Record N) (b : M7.Action.Recipe N),
      M7.Action.act (M7.Action.inverse g) (M7.Action.act g b) = b := by
    intro g b
    exact?
  constructor
  · rintro ⟨i, g, rfl⟩
    refine ⟨M7.PrefixOrbit.class_action N w _ g
      (M7.GeneratedFamily.family_good N w E hw hwN hE i).1, ?_⟩
    obtain ⟨h, hh⟩ := M7.GeneratedFamily.family_meets N w E hw hwN hE i
    refine ⟨M7.Action.compose h (M7.Action.inverse g), ?_⟩
    simpa only [hcomp, hinv] using hh
  · rintro ⟨hc, g, hg⟩
    have hex := M7.CompactCorrectness.generate_exact N w E hE
    have hgood : M7.RecoveryInstance.GoodBases w
        (M7.CompactGeneration.generate (N := N) w E).finalBases := hex.1
    have hnorm : M7.CanonicalClasses.Normalized
        (M7.CompactGeneration.generate (N := N) w E).finalBases := by
      unfold M7.RecoveryInstance.GoodBases at hgood
      tauto
    have hvalid : ∀ b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases,
        M7.PrefixOrbit.ClassValid w b := by
      unfold M7.RecoveryInstance.GoodBases at hgood
      tauto
    have hsub : M7.RawCoverage.rootCompleted N w E ⊆
        M7.OrbitResidual.covered (M7.CompactGeneration.generate (N := N) w E).finalBases := by
      intro y hy
      exact M7.CompactCorrectness.generate_coverage N w E hE y hy
    have hempty : M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E)
        (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ := by
      simpa only [M7.OrbitResidual.remaining] using
        (Finset.sdiff_eq_empty_iff_subset.mpr hsub)
    have hq : M7.RawCoverage.Queried w E (M7.Action.act g c) :=
      ⟨M7.PrefixOrbit.class_action N w c g hc, hg⟩
    obtain ⟨b, hb, h, hh⟩ :=
      (M7.RawCoverage.remaining_coverage N w E _ hw hnorm hvalid hempty
        (M7.Action.act g c) hq).2
    obtain ⟨i, hi⟩ := (M7.GeneratedFamily.family_range N w E hw hwN hE b).mp hb
    refine ⟨i, M7.Action.compose (M7.Action.inverse g) h, ?_⟩
    rw [hi, hcomp, hh, hinv]

theorem M7.GeneratedFamily.family_separated : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → M7.GlobalQuery.separated (M7.GeneratedFamily.family N w E) := by
  intro N w inst E hw hwN hE
  classical
  have hnorm := fun i => (M7.GeneratedFamily.family_good N w E hw hwN hE i).2
  have hsep : ∀ (i j : Fin (M7.GeneratedFamily.size N w E))
      (g h : M7.Action.Record N),
      M7.Action.act g (M7.GeneratedFamily.family N w E i) =
        M7.Action.act h (M7.GeneratedFamily.family N w E j) → i = j := by
    intro i j g h heq
    apply M7.GeneratedFamily.family_injective N w E hw hwN hE
    have hc := congrArg (fun c : M7.Action.Recipe N => M7.CanonicalOuter.canonical c) heq
    simpa only [M7.CanonicalOuter.canonical_invariant, hnorm] using hc
  unfold M7.GlobalQuery.separated
  simp only [M7.GlobalQuery.realize]
  aesop
#print axioms M7.GeneratedFamily.family_injective
#print axioms M7.GeneratedFamily.family_meets
#print axioms M7.GeneratedFamily.family_range
#print axioms M7.GeneratedFamily.family_good
#print axioms M7.GeneratedFamily.family_anchored
#print axioms M7.GeneratedFamily.family_complete
#print axioms M7.GeneratedFamily.family_separated
