import FrozenTarget_17951d5259a58aee
theorem M5.Translation.anchored_normalization : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (S U : Finset (ZMod N)), _
  intro N inst S U hS hU
  classical
  rcases hS with ⟨c, hc⟩
  rcases hU with ⟨d, hd⟩
  have hs := M5.Translation.shift_card_anchor N S c hc
  have hu := M5.Translation.shift_card_anchor N U d hd
  have hcard (T : Finset (ZMod N)) :
      (M5.Translation.natSupport T).card = T.card := by
    change (T.image ZMod.val).card = T.card
    apply Finset.card_image_iff.mpr
    intro x hx y hy h
    exact ZMod.val_injective N h
  have hzero (T : Finset (ZMod N)) (hT : 0 ∈ T) :
      0 ∈ M5.Translation.natSupport T := by
    change 0 ∈ T.image ZMod.val
    exact Finset.mem_image.mpr ⟨0, hT, by simp⟩
  have hbound (T : Finset (ZMod N)) :
      ∀ a ∈ M5.Translation.natSupport T, a < N := by
    intro a ha
    change a ∈ T.image ZMod.val at ha
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    exact ZMod.val_lt x
  refine ⟨M5.Translation.natSupport (M5.Translation.shift S (-c)),
    M5.Translation.natSupport (M5.Translation.shift U (-d)),
    (hcard _).trans hs.1, (hcard _).trans hu.1,
    hzero _ hs.2, hzero _ hu.2, hbound _, hbound _, ?_, ?_⟩
  · rw [← M5.Translation.anchored_difference_gcd N
      (M5.Translation.shift S (-c)) (M5.Translation.shift U (-d)) hs.2 hu.2]
    unfold M5.Translation.differenceGcd
    rw [M5.Translation.difference_translation N S (-c),
      M5.Translation.difference_translation N U (-d)]
  · exact M5.Translation.signature_translation N S U (-c) (-d)
