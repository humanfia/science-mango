import M7Transport

theorem M7.Transport.affine_indicator : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N) (u : (ZMod N)ˣ) (s : ZMod N), M7.Supports.indicator (A.image (M7.Action.affine u s)) = M6.RecipeIsometries.shift N s (M6.RecipeIsometries.multiply N u (M7.Supports.indicator A)) := by
  intro N inst A u s
  classical
  funext i
  have h : i ∈ A.image (M7.Action.affine u s) ↔
      (↑(u⁻¹) : ZMod N) * (i - s) ∈ A := by
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa [M7.Action.affine, ← mul_assoc] using hj
    · intro hi
      apply Finset.mem_image.mpr
      refine ⟨(↑(u⁻¹) : ZMod N) * (i - s), hi, ?_⟩
      simp [M7.Action.affine, ← mul_assoc]
  simp only [M7.Supports.indicator, M6.RecipeIsometries.shift,
    M6.RecipeIsometries.multiply, h]

theorem M7.Transport.action_isometry : ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), Function.Bijective (M7.Transport.Xmap g) ∧ ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Xmap g v ∈ M7.Transport.BX (M7.Action.act g c) ↔ v ∈ M7.Transport.BX c) ∧ (M7.Transport.Xmap g v ∈ M7.Transport.CX (M7.Action.act g c) ↔ v ∈ M7.Transport.CX c) ∧ M6.Pinned.weight (M7.Transport.Xmap g v) = M6.Pinned.weight v := by
  intro N inst g c
  classical
  rcases g with ⟨u, e, s, t⟩
  cases e
  · have hm := M6.RecipeIsometries.multiplier_isometry N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2) u
    have ht := M6.RecipeIsometries.translation_isometry N
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.1))
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.2)) s t
    simp only [M7.Transport.Xmap, M7.Transport.BX, M7.Transport.CX, M7.Action.act,
      Bool.false_eq_true, Bool.true_eq_false, reduceIte, M7.Transport.affine_indicator]
    refine ⟨ht.1.comp hm.1, ?_⟩
    intro v
    have htV := ht.2 (M6.RecipeIsometries.multiplier N u v)
    have hmV := hm.2 v
    exact ⟨htV.1.trans hmV.1, htV.2.1.trans hmV.2.1, htV.2.2.trans hmV.2.2⟩
  · have hm := M6.RecipeIsometries.multiplier_isometry N (M7.Supports.indicator c.2) (M7.Supports.indicator c.1) u
    have ht := M6.RecipeIsometries.translation_isometry N
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.2))
      (M6.RecipeIsometries.multiply N u (M7.Supports.indicator c.1)) s t
    have he := M6.RecipeIsometries.exchange_isometry N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2)
    simp only [M7.Transport.Xmap, M7.Transport.BX, M7.Transport.CX, M7.Action.act,
      Bool.false_eq_true, Bool.true_eq_false, reduceIte, M7.Transport.affine_indicator]
    refine ⟨ht.1.comp (hm.1.comp he.1), ?_⟩
    intro v
    have htV := ht.2 (M6.RecipeIsometries.multiplier N u (M6.RecipeIsometries.blockExchange N v))
    have hmV := hm.2 (M6.RecipeIsometries.blockExchange N v)
    have heV := he.2 v
    exact ⟨htV.1.trans (hmV.1.trans heV.1), htV.2.1.trans (hmV.2.1.trans heV.2.1), htV.2.2.trans (hmV.2.2.trans heV.2.2)⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g c) ↔ v ∈ M7.Transport.LX c)
