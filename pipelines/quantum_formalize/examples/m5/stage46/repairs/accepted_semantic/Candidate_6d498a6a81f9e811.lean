import FrozenTarget_6d498a6a81f9e811
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
    dsimp [A]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have hB : B ⊆ Finset.range N := by
    dsimp [B]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have hWA : WA ⊆ Finset.range N := by
    dsimp [WA]
    unfold M5.PhysicalRecovery.StateOK at hs
    simp_all only [Finset.subset_iff, Finset.mem_sdiff]
    aesop
  have hWB : WB ⊆ Finset.range N := by
    dsimp [WB]
    unfold M5.PhysicalRecovery.StateOK at hs
    simp_all only [Finset.subset_iff, Finset.mem_sdiff]
    aesop
  have hA0 : 0 ∈ A := by
    simp [A, M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selected]
  have hB0 : 0 ∈ B := by
    simp [B, M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.selected]
  have hdA : Disjoint A WA := by
    dsimp [A, WA]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have hdB : Disjoint B WB := by
    dsimp [B, WB]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have words (q : List Bool) :
      q ∈ M5.PhysicalRecovery.validWords N w F ↔
        q.length = M5.PhysicalRecovery.decisionCount N ∧
        M5.PhysicalRecovery.ValidSupports N w F
          (M5.PhysicalRecovery.selectedA N q)
          (M5.PhysicalRecovery.selectedB N q) := by
    constructor
    · intro hq
      simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter,
        Finset.mem_image, Finset.mem_univ, true_and] at hq
      aesop (add simp [M5.PhysicalRecovery.wordValid])
    · intro hq
      let f : Fin (M5.PhysicalRecovery.decisionCount N) → Bool :=
        fun i => q[i.val]'(by omega)
      have hf : List.ofFn f = q := by
        apply List.ext_getElem
        · simpa using hq.1.symm
        · intro i hi hj
          simp [f]
      have hv : M5.PhysicalRecovery.wordValid N w F q := by
        simpa [M5.PhysicalRecovery.wordValid] using hq
      simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter,
        Finset.mem_image, Finset.mem_univ, true_and]
      aesop
  have completions (U V : Finset ℕ) :
      (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p ↔
        (U ⊆ WA ∧ U.card = w - A.card) ∧
        (V ⊆ WB ∧ V.card = w - B.card) ∧ R (A ∪ U) (B ∪ V) := by
    simp only [M5.PhysicalRecovery.completionSet,
      M5.ConditionalCount.validCompletions, Finset.product_eq_sprod,
      Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
    change (((U ⊆ WA ∧ U.card = w - A.card) ∧ (V ⊆ WB ∧ V.card = w - B.card)) ∧
      (A ∪ U).card = w ∧ (B ∪ V).card = w ∧ R (A ∪ U) (B ∪ V)) ↔
      (U ⊆ WA ∧ U.card = w - A.card) ∧ (V ⊆ WB ∧ V.card = w - B.card) ∧ R (A ∪ U) (B ∪ V)
    constructor
    · rintro ⟨⟨hu, hv⟩, _, _, hr⟩
      exact ⟨hu, hv, hr⟩
    · rintro ⟨hu, hv, hr⟩
      have hauc : (A ∪ U).card = w := by
        rw [Finset.card_union_of_disjoint (hdA.mono_right hu.1), hu.2]
        exact Nat.add_sub_of_le hpa
      have hbvc : (B ∪ V).card = w := by
        rw [Finset.card_union_of_disjoint (hdB.mono_right hv.1), hv.2]
        exact Nat.add_sub_of_le hpb
      exact ⟨⟨hu, hv⟩, hauc, hbvc, hr⟩
  have restore {S T : Finset ℕ} (h : S ⊆ T) : S ∪ (T \ S) = T := by
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
  have tail_subset {S T W : Finset ℕ} (h : T ⊆ S ∪ W) : T \ S ⊆ W := by
    intro x hx
    obtain ⟨hxT, hxS⟩ := Finset.mem_sdiff.mp hx
    exact (Finset.mem_union.mp (h hxT)).resolve_left hxS
  have remove {S U W : Finset ℕ} (hd : Disjoint S W) (hu : U ⊆ W) :
      (S ∪ U) \ S = U := by
    ext x
    have hh := Finset.disjoint_left.mp hd
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact False.elim (hn hx)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun hxS => hh hxS (hu hx)⟩
  let W := (M5.PhysicalRecovery.validWords N w F).filter (fun q => p.IsPrefix q)
  have member (q : List Bool) : q ∈ W ↔
      q.length = M5.PhysicalRecovery.decisionCount N ∧
      M5.PhysicalRecovery.ValidSupports N w F
        (M5.PhysicalRecovery.selectedA N q)
        (M5.PhysicalRecovery.selectedB N q) ∧ p.IsPrefix q := by
    simp only [W, Finset.mem_filter, words, and_assoc]
  let toTail := fun q : List Bool =>
    (M5.PhysicalRecovery.selectedA N q \ A,
     M5.PhysicalRecovery.selectedB N q \ B)
  have forward (q : List Bool) (hq : q ∈ W) :
      toTail q ∈ M5.PhysicalRecovery.completionSet N w F p := by
    obtain ⟨hql, hqv, hpre⟩ := (member q).mp hq
    obtain ⟨ha, hau, hb, hbu⟩ :=
      (M5.PhysicalRecovery.prefix_extension N p q hN hp hql).mp hpre
    change A ⊆ M5.PhysicalRecovery.selectedA N q at ha
    change B ⊆ M5.PhysicalRecovery.selectedB N q at hb
    have hca : (M5.PhysicalRecovery.selectedA N q).card = w := by
      unfold M5.PhysicalRecovery.ValidSupports at hqv
      aesop
    have hcb : (M5.PhysicalRecovery.selectedB N q).card = w := by
      unfold M5.PhysicalRecovery.ValidSupports at hqv
      aesop
    have hr : R (M5.PhysicalRecovery.selectedA N q)
        (M5.PhysicalRecovery.selectedB N q) := by
      dsimp [R]
      unfold M5.PhysicalRecovery.ValidSupports at hqv
      aesop
    apply (completions _ _).mpr
    refine ⟨⟨tail_subset hau, ?_⟩, ⟨tail_subset hbu, ?_⟩, ?_⟩
    · rw [Finset.card_sdiff_of_subset ha, hca]
    · rw [Finset.card_sdiff_of_subset hb, hcb]
    · simpa only [restore ha, restore hb] using hr
  have inverse (U V : Finset ℕ)
      (huv : (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p) :
      let q := M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)
      q ∈ W ∧ toTail q = (U, V) := by
    obtain ⟨⟨hu, huc⟩, ⟨hv, hvc⟩, hr⟩ := (completions U V).mp huv
    have hAU : A ∪ U ⊆ Finset.range N :=
      Finset.union_subset hA (Finset.Subset.trans hu hWA)
    have hBV : B ∪ V ⊆ Finset.range N :=
      Finset.union_subset hB (Finset.Subset.trans hv hWB)
    have hAU0 : 0 ∈ A ∪ U := Finset.mem_union_left _ hA0
    have hBV0 : 0 ∈ B ∪ V := Finset.mem_union_left _ hB0
    have hdu : Disjoint A U := hdA.mono_right hu
    have hdv : Disjoint B V := hdB.mono_right hv
    have hauc : (A ∪ U).card = w := by
      rw [Finset.card_union_of_disjoint hdu, huc]
      exact Nat.add_sub_of_le hpa
    have hbvc : (B ∪ V).card = w := by
      rw [Finset.card_union_of_disjoint hdv, hvc]
      exact Nat.add_sub_of_le hpb
    let q := M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)
    have hdecode := M5.PhysicalRecovery.decode_encode N (A ∪ U) (B ∪ V)
      hN hAU hBV hAU0 hBV0
    have hqa : M5.PhysicalRecovery.selectedA N q = A ∪ U := hdecode.1
    have hqb : M5.PhysicalRecovery.selectedB N q = B ∪ V := hdecode.2
    have hql : q.length = M5.PhysicalRecovery.decisionCount N := by
      simp only [q, M5.PhysicalRecovery.encode, List.length_ofFn]
    have hqv : M5.PhysicalRecovery.ValidSupports N w F
        (M5.PhysicalRecovery.selectedA N q)
        (M5.PhysicalRecovery.selectedB N q) := by
      rw [hqa, hqb]
      unfold M5.PhysicalRecovery.ValidSupports
      dsimp [R] at hr
      exact ⟨hAU, hBV, hAU0, hBV0, hauc, hbvc, hr⟩
    have hpre : p.IsPrefix q := by
      apply (M5.PhysicalRecovery.prefix_extension N p q hN hp hql).mpr
      rw [hqa, hqb]
      change A ⊆ A ∪ U ∧ A ∪ U ⊆ A ∪ WA ∧
        B ⊆ B ∪ V ∧ B ∪ V ⊆ B ∪ WB
      refine ⟨Finset.subset_union_left, ?_, Finset.subset_union_left, ?_⟩
      · exact Finset.union_subset_union (Finset.Subset.refl _) hu
      · exact Finset.union_subset_union (Finset.Subset.refl _) hv
    refine ⟨(member q).mpr ⟨hql, hqv, hpre⟩, ?_⟩
    change (M5.PhysicalRecovery.selectedA N q \ A,
      M5.PhysicalRecovery.selectedB N q \ B) = (U, V)
    rw [hqa, hqb, remove hdA hu, remove hdB hv]
  have hc : W.card = (M5.PhysicalRecovery.completionSet N w F p).card := by
    apply Finset.card_bij (fun q _ => toTail q)
    · exact forward
    · intro q hq r hr he
      obtain ⟨hql, hqv, hqp⟩ := (member q).mp hq
      obtain ⟨hrl, hrv, hrp⟩ := (member r).mp hr
      have hqe := (M5.PhysicalRecovery.prefix_extension N p q hN hp hql).mp hqp
      have hre := (M5.PhysicalRecovery.prefix_extension N p r hN hp hrl).mp hrp
      have hea := congrArg Prod.fst he
      have heb := congrArg Prod.snd he
      change M5.PhysicalRecovery.selectedA N q \ A =
        M5.PhysicalRecovery.selectedA N r \ A at hea
      change M5.PhysicalRecovery.selectedB N q \ B =
        M5.PhysicalRecovery.selectedB N r \ B at heb
      have ha : M5.PhysicalRecovery.selectedA N q =
          M5.PhysicalRecovery.selectedA N r := by
        calc
          _ = A ∪ (M5.PhysicalRecovery.selectedA N q \ A) := (restore hqe.1).symm
          _ = A ∪ (M5.PhysicalRecovery.selectedA N r \ A) := by rw [hea]
          _ = _ := restore hre.1
      have hb : M5.PhysicalRecovery.selectedB N q =
          M5.PhysicalRecovery.selectedB N r := by
        calc
          _ = B ∪ (M5.PhysicalRecovery.selectedB N q \ B) := (restore hqe.2.2.1).symm
          _ = B ∪ (M5.PhysicalRecovery.selectedB N r \ B) := by rw [heb]
          _ = _ := restore hre.2.2.1
      calc
        q = M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q)
          (M5.PhysicalRecovery.selectedB N q) :=
            (M5.PhysicalRecovery.encode_decode N q hN hql).symm
        _ = M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N r)
          (M5.PhysicalRecovery.selectedB N r) := by rw [ha, hb]
        _ = r := M5.PhysicalRecovery.encode_decode N r hN hrl
    · rintro ⟨U, V⟩ huv
      obtain ⟨hq, he⟩ := inverse U V huv
      exact ⟨M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V), hq, he⟩
  have hcount : M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p = (W.card : ℤ) := by
    unfold M5.PrefixPartition.count
    apply congrArg (fun s : Finset (List Bool) => (s.card : ℤ))
    ext q
    simp only [W, Finset.mem_filter]
  rw [hcount]
  exact congrArg (fun n : ℕ => (n : ℤ)) hc
