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

theorem M7.Transport.x_logical : ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g c) ↔ v ∈ M7.Transport.LX c) := by
  intro N inst g c v
  classical
  have h := (M7.Transport.action_isometry N g c).2 v
  change (M7.Transport.Xmap g v ∈ M7.Transport.CX (M7.Action.act g c) \ M7.Transport.BX (M7.Action.act g c) ↔ v ∈ M7.Transport.CX c \ M7.Transport.BX c)
  simp only [Finset.mem_sdiff, h.1, h.2.1]

theorem M7.Transport.weight_sets : ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), (M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight = (M7.Transport.LX c).image M6.Pinned.weight := by
  intro N inst g c
  classical
  change (M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight =
    (M7.Transport.LX c).image M6.Pinned.weight
  have h := M7.Transport.action_isometry N g c
  apply Finset.ext
  intro d
  constructor
  · intro hd
    obtain ⟨v, hv, hw⟩ := Finset.mem_image.mp hd
    obtain ⟨u, rfl⟩ := h.1.2 v
    apply Finset.mem_image.mpr
    refine ⟨u, (M7.Transport.x_logical N g c u).mp hv, ?_⟩
    exact (h.2 u).2.2.symm.trans hw
  · intro hd
    obtain ⟨v, hv, hw⟩ := Finset.mem_image.mp hd
    apply Finset.mem_image.mpr
    refine ⟨M7.Transport.Xmap g v, (M7.Transport.x_logical N g c v).mpr hv, ?_⟩
    exact (h.2 v).2.2.trans hw

theorem M7.Transport.z_logical : ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), Function.Bijective (M7.Transport.Zmap g) ∧ ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Zmap g v ∈ M7.Transport.LZ (M7.Action.act g c) ↔ v ∈ M7.Transport.LZ c) ∧ M6.Pinned.weight (M7.Transport.Zmap g v) = M6.Pinned.weight v ∧ M7.Transport.Zmap g (M6.Flatten.J N v) = M6.Flatten.J N (M7.Transport.Xmap g v) := by
  intro N inst g c
  classical
  have hJ : Function.Involutive (M6.Flatten.J N) := M6.Flatten.J_involution N
  have hJL : ∀ (d : M7.Transport.Recipe N) (w : M6.Pinned.Vector (2*N)),
      w ∈ M7.Transport.LX d ↔ M6.Flatten.J N w ∈ M7.Transport.LZ d := by
    intro d w
    exact M6.ActualCSS.J_logical_iff N (M7.Supports.indicator d.1) (M7.Supports.indicator d.2) w
  constructor
  · change Function.Bijective (M6.Flatten.J N ∘ M7.Transport.Xmap g ∘ M6.Flatten.J N)
    exact hJ.bijective.comp ((M7.Transport.action_isometry N g c).1.comp hJ.bijective)
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · change M6.Flatten.J N (M7.Transport.Xmap g (M6.Flatten.J N v)) ∈ M7.Transport.LZ (M7.Action.act g c) ↔ v ∈ M7.Transport.LZ c
      calc
        _ ↔ M7.Transport.Xmap g (M6.Flatten.J N v) ∈ M7.Transport.LX (M7.Action.act g c) := (hJL _ _).symm
        _ ↔ M6.Flatten.J N v ∈ M7.Transport.LX c := M7.Transport.x_logical N g c _
        _ ↔ v ∈ M7.Transport.LZ c := by
          simpa only [M6.Flatten.J_involution] using hJL c (M6.Flatten.J N v)
    · change M6.Pinned.weight (M6.Flatten.J N (M7.Transport.Xmap g (M6.Flatten.J N v))) = M6.Pinned.weight v
      rw [M6.Flatten.J_weight, (M7.Transport.action_isometry N g c).2 (M6.Flatten.J N v) |>.2.2, M6.Flatten.J_weight]
    · change M6.Flatten.J N (M7.Transport.Xmap g (M6.Flatten.J N (M6.Flatten.J N v))) = M6.Flatten.J N (M7.Transport.Xmap g v)
      rw [M6.Flatten.J_involution]
#print axioms M7.Transport.affine_indicator
#print axioms M7.Transport.action_isometry
#print axioms M7.Transport.x_logical
#print axioms M7.Transport.weight_sets
#print axioms M7.Transport.z_logical
