import FrozenTarget_a821cd37e1dc3184
theorem M5.PhysicalRecovery.semantic_completion_count : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length ≤ M5.PhysicalRecovery.decisionCount N → (M5.PhysicalRecovery.selectedA N p).card ≤ w → (M5.PhysicalRecovery.selectedB N p).card ≤ w → M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p = (M5.PhysicalRecovery.completionSet N w F p).card
  intro N w F hN hw hF hFN p hp hAw hBw
  let A := M5.PhysicalRecovery.selectedA N p
  let B := M5.PhysicalRecovery.selectedB N p
  let WA := M5.PhysicalRecovery.availableA N p
  let WB := M5.PhysicalRecovery.availableB N p
  have hs := M5.PhysicalRecovery.state_domains N p hN hp
  unfold M5.PhysicalRecovery.StateOK at hs
  have hAr : A ⊆ Finset.range N := by dsimp [A]; tauto
  have hBr : B ⊆ Finset.range N := by dsimp [B]; tauto
  have hWAr : WA ⊆ Finset.range N := by dsimp [WA]; tauto
  have hWBr : WB ⊆ Finset.range N := by dsimp [WB]; tauto
  have hA0 : 0 ∈ A := by simp [A, M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selected]
  have hB0 : 0 ∈ B := by simp [B, M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.selected]
  have hdA : Disjoint A WA := by dsimp [A, WA]; tauto
  have hdB : Disjoint B WB := by dsimp [B, WB]; tauto
  have memWords (q : List Bool) :
      q ∈ M5.PhysicalRecovery.validWords N w F ↔
        q.length = M5.PhysicalRecovery.decisionCount N ∧
        M5.PhysicalRecovery.ValidSupports N w F
          (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) := by
    constructor
    · intro h
      simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter,
        Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨⟨f, rfl⟩, hv⟩
      simp only [M5.PhysicalRecovery.wordValid] at hv
      simpa using hv
    · rintro ⟨hl, hv⟩
      let f : Fin (M5.PhysicalRecovery.decisionCount N) → Bool :=
        fun i => q[i.val]'(by omega)
      have hf : List.ofFn f = q := by
        apply List.ext_getElem
        · simpa using hl.symm
        · intro i hi hiq
          simp [f]
      have hv' : M5.PhysicalRecovery.wordValid N w F (List.ofFn f) := by
        simp only [M5.PhysicalRecovery.wordValid, hf]
        aesop
      rw [← hf]
      simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter,
        Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨f, rfl⟩, hv'⟩
  have memCompletion (U V : Finset ℕ) :
      (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p ↔
        (U ⊆ WA ∧ U.card = w - A.card) ∧
        (V ⊆ WB ∧ V.card = w - B.card) ∧
        M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) = 1 ∧
        M5.completeSignature (M5.SupportPolynomial.ofSupport (A ∪ U))
          (M5.SupportPolynomial.ofSupport (B ∪ V)) N = F := by
    simp [M5.PhysicalRecovery.completionSet, M5.ConditionalCount.validCompletions,
      Finset.product_eq_sprod, A, B, WA, WB, and_assoc]
  let S := (M5.PhysicalRecovery.validWords N w F).filter (fun q => p.IsPrefix q)
  have reverse (U V : Finset ℕ)
      (huv : (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p) :
      M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V) ∈ S ∧
      M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) = A ∪ U ∧
      M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)) = B ∪ V := by
    obtain ⟨⟨hU, hcU⟩, ⟨hV, hcV⟩, hg, hf⟩ := (memCompletion U V).mp huv
    have hAU : Disjoint A U := hdA.mono_right hU
    have hBV : Disjoint B V := hdB.mono_right hV
    have hrA : A ∪ U ⊆ Finset.range N := Finset.union_subset hAr (hU.trans hWAr)
    have hrB : B ∪ V ⊆ Finset.range N := Finset.union_subset hBr (hV.trans hWBr)
    have hzA : 0 ∈ A ∪ U := Finset.mem_union_left U hA0
    have hzB : 0 ∈ B ∪ V := Finset.mem_union_left V hB0
    have hcA : (A ∪ U).card = w := by
      rw [Finset.card_union_of_disjoint hAU, hcU]
      change A.card ≤ w at hAw
      omega
    have hcB : (B ∪ V).card = w := by
      rw [Finset.card_union_of_disjoint hBV, hcV]
      change B.card ≤ w at hBw
      omega
    have hd := M5.PhysicalRecovery.decode_encode N (A ∪ U) (B ∪ V) hN hrA hrB hzA hzB
    have hl : (M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)).length =
        M5.PhysicalRecovery.decisionCount N := by simp [M5.PhysicalRecovery.encode]
    refine ⟨?_, hd⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (memWords _).mpr
      refine ⟨hl, ?_⟩
      rw [hd.1, hd.2]
      unfold M5.PhysicalRecovery.ValidSupports
      exact ⟨hrA, hrB, hzA, hzB, hcA, hcB, hg, hf⟩
    · apply (M5.PhysicalRecovery.prefix_extension N p _ hN hp hl).mpr
      rw [hd.1, hd.2]
      change A ⊆ A ∪ U ∧ A ∪ U ⊆ A ∪ WA ∧ B ⊆ B ∪ V ∧ B ∪ V ⊆ B ∪ WB
      exact ⟨Finset.subset_union_left, Finset.union_subset_union (Finset.Subset.refl A) hU,
        Finset.subset_union_left, Finset.union_subset_union (Finset.Subset.refl B) hV⟩
  have forward (q : List Bool) (hq : q ∈ S) :
      ∃ uv ∈ M5.PhysicalRecovery.completionSet N w F p,
        M5.PhysicalRecovery.encode N (A ∪ uv.1) (B ∪ uv.2) = q := by
    obtain ⟨hqv, hpq⟩ := Finset.mem_filter.mp hq
    obtain ⟨hl, hv⟩ := (memWords q).mp hqv
    obtain ⟨hrA, hrB, hzA, hzB, hcA, hcB, hg, hf⟩ := hv
    have he := (M5.PhysicalRecovery.prefix_extension N p q hN hp hl).mp hpq
    change A ⊆ M5.PhysicalRecovery.selectedA N q ∧
      M5.PhysicalRecovery.selectedA N q ⊆ A ∪ WA ∧
      B ⊆ M5.PhysicalRecovery.selectedB N q ∧
      M5.PhysicalRecovery.selectedB N q ⊆ B ∪ WB at he
    let U := M5.PhysicalRecovery.selectedA N q \ A
    let V := M5.PhysicalRecovery.selectedB N q \ B
    have hU : U ⊆ WA := by
      intro x hx
      obtain ⟨hxq, hxa⟩ := Finset.mem_sdiff.mp hx
      have hx' := Finset.mem_union.mp (he.2.1 hxq)
      exact hx'.resolve_left hxa
    have hV : V ⊆ WB := by
      intro x hx
      obtain ⟨hxq, hxb⟩ := Finset.mem_sdiff.mp hx
      have hx' := Finset.mem_union.mp (he.2.2.2 hxq)
      exact hx'.resolve_left hxb
    have eqA : A ∪ U = M5.PhysicalRecovery.selectedA N q := by
      ext x
      simp only [U, Finset.mem_union, Finset.mem_sdiff]
      have hx := @he.1 x
      tauto
    have eqB : B ∪ V = M5.PhysicalRecovery.selectedB N q := by
      ext x
      simp only [V, Finset.mem_union, Finset.mem_sdiff]
      have hx := @he.2.2.1 x
      tauto
    have hcU : U.card = w - A.card := by
      dsimp [U]
      rw [Finset.card_sdiff_of_subset he.1, hcA]
    have hcV : V.card = w - B.card := by
      dsimp [V]
      rw [Finset.card_sdiff_of_subset he.2.2.1, hcB]
    refine ⟨(U, V), (memCompletion U V).mpr ?_, ?_⟩
    · refine ⟨⟨hU, hcU⟩, ⟨hV, hcV⟩, ?_⟩
      simpa only [eqA, eqB] using And.intro hg hf
    · change M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V) = q
      rw [eqA, eqB]
      exact M5.PhysicalRecovery.encode_decode N q hN hl
  change (S.card : ℤ) = ((M5.PhysicalRecovery.completionSet N w F p).card : ℤ)
  apply congrArg (fun n : ℕ => (n : ℤ))
  symm
  refine Finset.card_bij (fun uv _ => M5.PhysicalRecovery.encode N (A ∪ uv.1) (B ∪ uv.2)) ?_ ?_ ?_
  · intro uv huv
    exact (reverse uv.1 uv.2 huv).1
  · intro uv huv uv' huv' he
    have hd := (reverse uv.1 uv.2 huv).2
    have hd' := (reverse uv'.1 uv'.2 huv').2
    have heA : A ∪ uv.1 = A ∪ uv'.1 := by
      rw [← hd.1, ← hd'.1, he]
    have heB : B ∪ uv.2 = B ∪ uv'.2 := by
      rw [← hd.2, ← hd'.2, he]
    have hm := (memCompletion uv.1 uv.2).mp huv
    have hm' := (memCompletion uv'.1 uv'.2).mp huv'
    have hdu := Finset.disjoint_left.mp (hdA.mono_right hm.1.1)
    have hdu' := Finset.disjoint_left.mp (hdA.mono_right hm'.1.1)
    have hdv := Finset.disjoint_left.mp (hdB.mono_right hm.2.1.1)
    have hdv' := Finset.disjoint_left.mp (hdB.mono_right hm'.2.1.1)
    apply Prod.ext
    · ext x
      have hx := Finset.ext_iff.mp heA x
      simp only [Finset.mem_union] at hx
      aesop
    · ext x
      have hx := Finset.ext_iff.mp heB x
      simp only [Finset.mem_union] at hx
      aesop
  · intro q hq
    exact forward q hq
