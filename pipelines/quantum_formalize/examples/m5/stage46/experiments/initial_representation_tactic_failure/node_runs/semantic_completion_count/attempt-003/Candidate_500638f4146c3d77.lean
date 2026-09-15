import FrozenTarget_500638f4146c3d77
theorem M5.PhysicalRecovery.semantic_completion_count : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length ≤ M5.PhysicalRecovery.decisionCount N → (M5.PhysicalRecovery.selectedA N p).card ≤ w → (M5.PhysicalRecovery.selectedB N p).card ≤ w → M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p = (M5.PhysicalRecovery.completionSet N w F p).card
  intro N w F hN hw hF hFN p hp hpa hpb
  let A := M5.PhysicalRecovery.selectedA N p
  let B := M5.PhysicalRecovery.selectedB N p
  let WA := M5.PhysicalRecovery.availableA N p
  let WB := M5.PhysicalRecovery.availableB N p
  let R := fun X Y : Finset ℕ => M5.Connectivity.supportGcd N X Y = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport X) (M5.SupportPolynomial.ofSupport Y) N = F
  have hs := M5.PhysicalRecovery.state_domains N p hN hp
  simp only [M5.PhysicalRecovery.StateOK, Finset.singleton_subset_iff] at hs
  have hA : A ⊆ Finset.range N := by tauto
  have hB : B ⊆ Finset.range N := by tauto
  have hWA : WA ⊆ Finset.range N := by tauto
  have hWB : WB ⊆ Finset.range N := by tauto
  have hA0 : 0 ∈ A := by tauto
  have hB0 : 0 ∈ B := by tauto
  have hdA : Disjoint A WA := by tauto
  have hdB : Disjoint B WB := by tauto
  have union_diff (X S : Finset ℕ) (h : S ⊆ X) : S ∪ (X \ S) = X := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact h hx
      · exact hx
    · intro hx
      by_cases hxS : x ∈ S
      · exact Or.inl hxS
      · exact Or.inr ⟨hx, hxS⟩
  have diff_union (S T U : Finset ℕ) (hd : Disjoint S T) (hu : U ⊆ T) : (S ∪ U) \ S = U := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have hn : x ∈ U → x ∉ S := fun hx hs => Finset.disjoint_left.mp hd hs (hu hx)
    tauto
  have words (q : List Bool) : q ∈ M5.PhysicalRecovery.validWords N w F ↔ q.length = M5.PhysicalRecovery.decisionCount N ∧ M5.PhysicalRecovery.ValidSupports N w F (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) := by
    constructor
    · intro hq
      have hh := (Finset.mem_filter.mp hq).2
      exact hh
    · rintro ⟨hl, hv⟩
      have hex : ∃ a : Fin (M5.PhysicalRecovery.decisionCount N) → Bool, List.ofFn a = q := by
        rw [← hl]
        exact ⟨fun i => q[i], by simp⟩
      simpa [M5.PhysicalRecovery.validWords, M5.PhysicalRecovery.wordValid] using And.intro hex (And.intro hl hv)
  have completions (U V : Finset ℕ) : (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p ↔ U ⊆ WA ∧ U.card = w - A.card ∧ V ⊆ WB ∧ V.card = w - B.card ∧ (A ∪ U).card = w ∧ (B ∪ V).card = w ∧ R (A ∪ U) (B ∪ V) := by
    simp [M5.PhysicalRecovery.completionSet, M5.ConditionalCount.validCompletions, Finset.product_eq_sprod, Finset.mem_powersetCard, A, B, WA, WB, R, and_assoc]
  let W := (M5.PhysicalRecovery.validWords N w F).filter (fun q => p.IsPrefix q)
  have wm (q : List Bool) : q ∈ W ↔ q.length = M5.PhysicalRecovery.decisionCount N ∧ M5.PhysicalRecovery.ValidSupports N w F (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) ∧ p.IsPrefix q := by
    simp only [W, Finset.mem_filter, words, and_assoc]
  let f := fun q : List Bool => (M5.PhysicalRecovery.selectedA N q \ A, M5.PhysicalRecovery.selectedB N q \ B)
  let g := fun t : Finset ℕ × Finset ℕ => M5.PhysicalRecovery.encode N (A ∪ t.1) (B ∪ t.2)
  have forward : ∀ q ∈ W, f q ∈ M5.PhysicalRecovery.completionSet N w F p := by
    intro q hq
    obtain ⟨hl, hv, hpr⟩ := (wm q).mp hq
    obtain ⟨ha, hau, hb, hbu⟩ := (M5.PhysicalRecovery.prefix_extension N p q hN hp hl).mp hpr
    have ea := union_diff (M5.PhysicalRecovery.selectedA N q) A ha
    have eb := union_diff (M5.PhysicalRecovery.selectedB N q) B hb
    have hca : (M5.PhysicalRecovery.selectedA N q).card = w := by
      simpa only [M5.PhysicalRecovery.ValidSupports] using hv |>.2.2.2.2.1
    have hcb : (M5.PhysicalRecovery.selectedB N q).card = w := by
      simp only [M5.PhysicalRecovery.ValidSupports] at hv
      tauto
    have hr : R (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) := by
      simp only [M5.PhysicalRecovery.ValidSupports] at hv
      exact ⟨by tauto, by tauto⟩
    apply (completions _ _).mpr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
      exact (Finset.mem_union.mp (hau hx)).resolve_left hn
    · rw [Finset.card_sdiff_of_subset ha, hca]
    · intro x hx
      obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
      exact (Finset.mem_union.mp (hbu hx)).resolve_left hn
    · rw [Finset.card_sdiff_of_subset hb, hcb]
    · simpa only [ea] using hca
    · simpa only [eb] using hcb
    · simpa only [ea, eb] using hr
  have backward : ∀ t ∈ M5.PhysicalRecovery.completionSet N w F p, g t ∈ W := by
    rintro ⟨U, V⟩ ht
    obtain ⟨hu, huc, hv, hvc, hcu, hcv, hr⟩ := (completions U V).mp ht
    have hau : A ∪ U ⊆ Finset.range N := Finset.union_subset hA (hu.trans hWA)
    have hbv : B ∪ V ⊆ Finset.range N := Finset.union_subset hB (hv.trans hWB)
    have ha0 : 0 ∈ A ∪ U := Finset.mem_union_left U hA0
    have hb0 : 0 ∈ B ∪ V := Finset.mem_union_left V hB0
    have hd := M5.PhysicalRecovery.decode_encode N (A ∪ U) (B ∪ V) hN hau hbv ha0 hb0
    have hl : (g (U, V)).length = M5.PhysicalRecovery.decisionCount N := by
      simp [g, M5.PhysicalRecovery.encode]
    apply (wm _).mpr
    refine ⟨hl, ?_, ?_⟩
    · change M5.PhysicalRecovery.ValidSupports N w F (M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V))) (M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)))
      rw [hd.1, hd.2]
      exact ⟨hau, hbv, ha0, hb0, hcu, hcv, hr⟩
    · apply (M5.PhysicalRecovery.prefix_extension N p (g (U, V)) hN hp hl).mpr
      change A ⊆ M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ∧ M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ⊆ A ∪ WA ∧ B ⊆ M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ∧ M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ⊆ B ∪ WB
      rw [hd.1, hd.2]
      exact ⟨Finset.subset_union_left, Finset.union_subset_union_right hu, Finset.subset_union_left, Finset.union_subset_union_right hv⟩
  have left_inv : ∀ q ∈ W, g (f q) = q := by
    intro q hq
    obtain ⟨hl, hv, hpr⟩ := (wm q).mp hq
    obtain ⟨ha, hau, hb, hbu⟩ := (M5.PhysicalRecovery.prefix_extension N p q hN hp hl).mp hpr
    change M5.PhysicalRecovery.encode N (A ∪ (M5.PhysicalRecovery.selectedA N q \ A)) (B ∪ (M5.PhysicalRecovery.selectedB N q \ B)) = q
    rw [union_diff _ _ ha, union_diff _ _ hb]
    exact M5.PhysicalRecovery.encode_decode N q hN hl
  have right_inv : ∀ t ∈ M5.PhysicalRecovery.completionSet N w F p, f (g t) = t := by
    rintro ⟨U, V⟩ ht
    obtain ⟨hu, huc, hv, hvc, hcu, hcv, hr⟩ := (completions U V).mp ht
    have hd := M5.PhysicalRecovery.decode_encode N (A ∪ U) (B ∪ V) hN (Finset.union_subset hA (hu.trans hWA)) (Finset.union_subset hB (hv.trans hWB)) (Finset.mem_union_left U hA0) (Finset.mem_union_left V hB0)
    change (M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) \ A, M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) \ B) = (U, V)
    rw [hd.1, hd.2, diff_union A WA U hdA hu, diff_union B WB V hdB hv]
  have hc : W.card = (M5.PhysicalRecovery.completionSet N w F p).card := by
    apply Finset.card_bij (fun q _ => f q)
    · exact forward
    · intro q hq r hr he
      calc
        q = g (f q) := (left_inv q hq).symm
        _ = g (f r) := congrArg g he
        _ = r := left_inv r hr
    · intro t ht
      exact ⟨g t, backward t ht, right_inv t ht⟩
  simpa [M5.PrefixPartition.count, W] using congrArg (fun n : ℕ => (n : ℤ)) hc
