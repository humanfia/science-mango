import FrozenTarget_34a04dfa1fd070a3
theorem M5.PhysicalRecovery.semantic_completion_count : QuantumHarnessFrozenTarget := by
  classical
  intro N w F hN hw hF hFN p hp hpa hpb
  let A := M5.PhysicalRecovery.selectedA N p
  let B := M5.PhysicalRecovery.selectedB N p
  let WA := M5.PhysicalRecovery.availableA N p
  let WB := M5.PhysicalRecovery.availableB N p
  let R := fun X Y : Finset ℕ =>
    M5.Connectivity.supportGcd N X Y = 1 ∧
    M5.completeSignature (M5.SupportPolynomial.ofSupport X)
      (M5.SupportPolynomial.ofSupport Y) N = F
  have hs := M5.PhysicalRecovery.state_domains N p hN hp
  have hA : A ⊆ Finset.range N := by
    unfold M5.PhysicalRecovery.StateOK at hs
    tauto
  have hB : B ⊆ Finset.range N := by
    unfold M5.PhysicalRecovery.StateOK at hs
    tauto
  have hWA : WA ⊆ Finset.range N := by
    unfold M5.PhysicalRecovery.StateOK at hs
    tauto
  have hWB : WB ⊆ Finset.range N := by
    unfold M5.PhysicalRecovery.StateOK at hs
    tauto
  have hA0 : 0 ∈ A := by
    simp [A, M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selected]
  have hB0 : 0 ∈ B := by
    simp [B, M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.selected]
  have hdA : Disjoint A WA := by
    unfold M5.PhysicalRecovery.StateOK at hs
    tauto
  have hdB : Disjoint B WB := by
    unfold M5.PhysicalRecovery.StateOK at hs
    tauto
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
  have diff_union (S T U : Finset ℕ) (hd : Disjoint S T) (hu : U ⊆ T) :
      (S ∪ U) \ S = U := by
    ext x
    have hdis := Finset.disjoint_left.mp hd
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact False.elim (hn hx)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun hxS => hdis hxS (hu hx)⟩
  have words (q : List Bool) :
      q ∈ M5.PhysicalRecovery.validWords N w F ↔
        q.length = M5.PhysicalRecovery.decisionCount N ∧
        M5.PhysicalRecovery.ValidSupports N w F
          (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) := by
    constructor
    · intro hq
      simpa [M5.PhysicalRecovery.validWords, M5.PhysicalRecovery.wordValid] using hq
    · intro hq
      have he : List.ofFn (fun i : Fin (M5.PhysicalRecovery.decisionCount N) =>
          q[i.val]'(by omega)) = q := by
        apply List.ext_getElem
        · simpa using hq.1.symm
        · intro i hi hj
          simp
      simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, he⟩
      · exact hq
  have completions (U V : Finset ℕ) :
      (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p ↔
        U ⊆ WA ∧ U.card = w - A.card ∧
        V ⊆ WB ∧ V.card = w - B.card ∧
        (A ∪ U).card = w ∧ (B ∪ V).card = w ∧ R (A ∪ U) (B ∪ V) := by
    simp [M5.PhysicalRecovery.completionSet,
      M5.ConditionalCount.validCompletions, Finset.product_eq_sprod,
      Finset.mem_powersetCard, A, B, WA, WB, R, and_assoc]
  let W := (M5.PhysicalRecovery.validWords N w F).filter (fun q => p.IsPrefix q)
  have wm (q : List Bool) : q ∈ W ↔
      q.length = M5.PhysicalRecovery.decisionCount N ∧
      M5.PhysicalRecovery.ValidSupports N w F
        (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) ∧
      p.IsPrefix q := by
    simp only [W, Finset.mem_filter, words, and_assoc]
  let f := fun q : List Bool =>
    (M5.PhysicalRecovery.selectedA N q \ A,
     M5.PhysicalRecovery.selectedB N q \ B)
  let g := fun t : Finset ℕ × Finset ℕ =>
    M5.PhysicalRecovery.encode N (A ∪ t.1) (B ∪ t.2)
  have forward (q : List Bool) (hq : q ∈ W) :
      f q ∈ M5.PhysicalRecovery.completionSet N w F p := by
    obtain ⟨hl, hv, hpre⟩ := (wm q).mp hq
    have he := (M5.PhysicalRecovery.prefix_extension N p q hN hp hl).mp hpre
    obtain ⟨ha, hau, hb, hbu⟩ := he
    have ea := union_diff (M5.PhysicalRecovery.selectedA N q) A ha
    have eb := union_diff (M5.PhysicalRecovery.selectedB N q) B hb
    have hca : (M5.PhysicalRecovery.selectedA N q).card = w := by
      unfold M5.PhysicalRecovery.ValidSupports at hv
      tauto
    have hcb : (M5.PhysicalRecovery.selectedB N q).card = w := by
      unfold M5.PhysicalRecovery.ValidSupports at hv
      tauto
    apply (completions _ _).mpr
    dsimp only [f]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxq, hxp⟩ := Finset.mem_sdiff.mp hx
      exact (Finset.mem_union.mp (hau hxq)).resolve_left hxp
    · rw [Finset.card_sdiff_of_subset ha, hca]
    · intro x hx
      obtain ⟨hxq, hxp⟩ := Finset.mem_sdiff.mp hx
      exact (Finset.mem_union.mp (hbu hxq)).resolve_left hxp
    · rw [Finset.card_sdiff_of_subset hb, hcb]
    · rw [ea, hca]
    · rw [eb, hcb]
    · rw [ea, eb]
      unfold M5.PhysicalRecovery.ValidSupports at hv
      dsimp only [R]
      tauto
  have backward (t : Finset ℕ × Finset ℕ)
      (ht : t ∈ M5.PhysicalRecovery.completionSet N w F p) : g t ∈ W := by
    obtain ⟨U, V⟩ := t
    obtain ⟨hu, hcu, hv, hcv, hca, hcb, hr⟩ := (completions U V).mp ht
    have hau : A ∪ U ⊆ Finset.range N := Finset.union_subset hA (hu.trans hWA)
    have hbv : B ∪ V ⊆ Finset.range N := Finset.union_subset hB (hv.trans hWB)
    have ha0 : 0 ∈ A ∪ U := Finset.mem_union_left _ hA0
    have hb0 : 0 ∈ B ∪ V := Finset.mem_union_left _ hB0
    have hd := M5.PhysicalRecovery.decode_encode N (A ∪ U) (B ∪ V)
      hN hau hbv ha0 hb0
    have hl : (g (U, V)).length = M5.PhysicalRecovery.decisionCount N := by
      simp only [g, M5.PhysicalRecovery.encode, List.length_ofFn]
    apply (wm _).mpr
    refine ⟨hl, ?_, ?_⟩
    · change M5.PhysicalRecovery.ValidSupports N w F
        (M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)))
        (M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)))
      rw [hd.1, hd.2]
      unfold M5.PhysicalRecovery.ValidSupports
      exact ⟨hau, hbv, ha0, hb0, hca, hcb, hr⟩
    · apply (M5.PhysicalRecovery.prefix_extension N p _ hN hp hl).mpr
      change A ⊆ M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ∧
        M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ⊆ A ∪ WA ∧
        B ⊆ M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ∧
        M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) ⊆ B ∪ WB
      rw [hd.1, hd.2]
      exact ⟨Finset.subset_union_left, Finset.union_subset_union (Finset.Subset.refl _) hu,
        Finset.subset_union_left, Finset.union_subset_union (Finset.Subset.refl _) hv⟩
  have left_inv (q : List Bool) (hq : q ∈ W) : g (f q) = q := by
    obtain ⟨hl, hv, hpre⟩ := (wm q).mp hq
    have he := (M5.PhysicalRecovery.prefix_extension N p q hN hp hl).mp hpre
    dsimp only [g, f]
    rw [union_diff _ A he.1, union_diff _ B he.2.2.1]
    exact M5.PhysicalRecovery.encode_decode N q hN hl
  have right_inv (t : Finset ℕ × Finset ℕ)
      (ht : t ∈ M5.PhysicalRecovery.completionSet N w F p) : f (g t) = t := by
    obtain ⟨U, V⟩ := t
    obtain ⟨hu, hcu, hv, hcv, hca, hcb, hr⟩ := (completions U V).mp ht
    have hd := M5.PhysicalRecovery.decode_encode N (A ∪ U) (B ∪ V) hN
      (Finset.union_subset hA (hu.trans hWA))
      (Finset.union_subset hB (hv.trans hWB))
      (Finset.mem_union_left _ hA0) (Finset.mem_union_left _ hB0)
    dsimp only [f, g]
    rw [hd.1, hd.2, diff_union A WA U hdA hu, diff_union B WB V hdB hv]
  have hc : W.card = (M5.PhysicalRecovery.completionSet N w F p).card := by
    apply Finset.card_bij (fun q _ => f q) forward
    · intro q hq r hr he
      calc
        q = g (f q) := (left_inv q hq).symm
        _ = g (f r) := congrArg g he
        _ = r := left_inv r hr
    · intro t ht
      exact ⟨g t, backward t ht, right_inv t ht⟩
  have hcount : M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p =
      (W.card : ℤ) := by
    simp [M5.PrefixPartition.count, W]
  rw [hcount, hc]
