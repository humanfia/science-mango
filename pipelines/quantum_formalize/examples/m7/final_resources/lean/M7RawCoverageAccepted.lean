import M7PrefixBitsAccepted
import M7PrefixOrbitAccepted
import M7RawCoverage

theorem M7.RawCoverage.root_within : ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)), M7.PrefixOrbit.Within (M7.PrefixBits.A N []) (M7.PrefixBits.WA N []) S ↔ (0 : ZMod N) ∈ S := by
  classical
  intro N inst S
  have hr := M7.PrefixBits.root N (NeZero.pos N)
  rw [hr.1, hr.2.2.1]
  change ({0} ⊆ S.image ZMod.val ∧
    S.image ZMod.val ⊆ {0} ∪ (Finset.range N \ {0})) ↔ (0 : ZMod N) ∈ S
  constructor
  · intro h
    have hz : 0 ∈ S.image ZMod.val := h.1 (Finset.mem_singleton_self 0)
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hz
    have ha0 : a = (0 : ZMod N) :=
      (ZMod.val_injective N) (by simpa only [ZMod.val_zero] using hav)
    simpa only [ha0] using ha
  · intro h
    constructor
    · apply Finset.singleton_subset_iff.mpr
      exact Finset.mem_image.mpr ⟨0, h, ZMod.val_zero⟩
    · intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      by_cases hz : a.val = 0
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_singleton.mpr hz)
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_range.mpr (ZMod.val_lt a), by simpa using hz⟩

theorem M7.RawCoverage.translate_signature : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (s t : ZMod N), M7.RecipeSignature.signature (M7.Action.act (M7.Action.translate s t) c) = M7.RecipeSignature.signature c := by
  intro N inst c s t
  exact (M7.RecipeSignature.translation_invariant N (fun F => F = M7.RecipeSignature.signature c) _ _ _).mpr rfl

theorem M7.RawCoverage.translate_supports : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (s t : ZMod N), M7.Action.act (M7.Action.translate s t) c = (M7.Domain.shift c.1 s, M7.Domain.shift c.2 t) := by
  intro N hN c s t
  apply Prod.ext <;> ext x
  all_goals
    simp [M7.Action.act, M7.Action.translate, M7.Action.affine, M7.Domain.shift, Finset.mem_image]
  all_goals
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [add_assoc] using ha
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp [add_assoc]

theorem M7.RawCoverage.root_membership : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) (c : M7.Action.Recipe N), c ∈ M7.RawCoverage.rootCompleted N w E ↔ M7.RawCoverage.Queried w E c ∧ (0 : ZMod N) ∈ c.1 ∧ (0 : ZMod N) ∈ c.2 := by
  classical
  intro N w inst E c
  change c ∈ M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N []) (M7.PrefixBits.B N []) (M7.PrefixBits.WA N []) (M7.PrefixBits.WB N []) ↔ _
  rw [M7.PrefixOrbit.membership N w E _ _ _ _ (M7.PrefixBits.base N (NeZero.pos N) []) c]
  have hr := M7.PrefixBits.root N (NeZero.pos N)
  have hB : M7.PrefixBits.B N [] = M7.PrefixBits.A N [] := hr.2.1.trans hr.1.symm
  have hWB : M7.PrefixBits.WB N [] = M7.PrefixBits.WA N [] := hr.2.2.2.trans hr.2.2.1.symm
  rw [hB, hWB, M7.RawCoverage.root_within N c.1, M7.RawCoverage.root_within N c.2]
  simp only [M7.RawCoverage.Queried, and_assoc]

theorem M7.RawCoverage.raw_anchor : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) (c : M7.Action.Recipe N), 0 < w → M7.RawCoverage.Queried w E c → ∃ q ∈ c.1, ∃ r ∈ c.2, M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.RawCoverage.rootCompleted N w E := by
  classical
  intro N w inst E c hw h
  change M7.PrefixOrbit.ClassValid w c ∧ M7.RecipeSignature.signature c ∈ E at h
  have hA : c.1.card = w := by
    have hc := h.1
    unfold M7.PrefixOrbit.ClassValid at hc
    tauto
  have hB : c.2.card = w := by
    have hc := h.1
    unfold M7.PrefixOrbit.ClassValid at hc
    tauto
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < c.1.card by omega)
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < c.2.card by omega)
  refine ⟨q, hq, r, hr, ?_⟩
  apply (M7.RawCoverage.root_membership N w E _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change M7.PrefixOrbit.ClassValid w (M7.Action.act (M7.Action.translate (-q) (-r)) c) ∧ _
    constructor
    · exact M7.PrefixOrbit.class_action N w c _ h.1
    · rw [M7.RawCoverage.translate_signature]
      exact h.2
  · rw [M7.RawCoverage.translate_supports]
    change 0 ∈ M7.Domain.shift c.1 (-q)
    unfold M7.Domain.shift
    apply Finset.mem_image.mpr
    exact ⟨q, hq, by simp⟩
  · rw [M7.RawCoverage.translate_supports]
    change 0 ∈ M7.Domain.shift c.2 (-r)
    unfold M7.Domain.shift
    apply Finset.mem_image.mpr
    exact ⟨r, hr, by simp⟩

theorem M7.RawCoverage.remaining_coverage : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), 0 < w → M7.CanonicalClasses.Normalized bases → (∀ b ∈ bases, M7.PrefixOrbit.ClassValid w b) → M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) bases = ∅ → ∀ c : M7.Action.Recipe N, M7.RawCoverage.Queried w E c → M7.CanonicalOuter.canonical c ∈ bases ∧ ∃ b ∈ bases, ∃ g : M7.Action.Record N, M7.Action.act g b = c := by
  classical
  intro N w inst E bases hw hnorm hvalid hempty c hc
  obtain ⟨q, hq, r, hr, hy⟩ := M7.RawCoverage.raw_anchor N w E c hw hc
  have hcovered : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.covered bases := by
    by_contra hn
    have hmem : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) bases := by
      exact Finset.mem_sdiff.mpr ⟨hy, hn⟩
    rw [hempty] at hmem
    simp at hmem
  have hcanon := (M7.CanonicalClasses.coverage_iff N bases _ hnorm).mp hcovered
  have hb : M7.CanonicalOuter.canonical c ∈ bases := by
    simpa only [M7.CanonicalOuter.canonical_invariant] using hcanon
  refine ⟨hb, M7.CanonicalOuter.canonical c, hb, ?_⟩
  first
  | exact ⟨_, M7.CanonicalOuter.realizer_inverse N c⟩
  | exact ⟨_, M7.CanonicalOuter.realizer_inverse c⟩
#print axioms M7.RawCoverage.root_within
#print axioms M7.RawCoverage.root_membership
#print axioms M7.RawCoverage.translate_signature
#print axioms M7.RawCoverage.translate_supports
#print axioms M7.RawCoverage.raw_anchor
#print axioms M7.RawCoverage.remaining_coverage
