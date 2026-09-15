import FrozenTarget_9c0ff93cf5b8d4fd
theorem M6.ActualCounts.finite_image_weighted_sum : QuantumHarnessFrozenTarget := by
  classical
  intro α β _ L k h w
  let γ : Type := ↥(M6.ActualCounts.imageWords L)
  let L' : α → γ := fun a => ⟨L a, by simp [M6.ActualCounts.imageWords]⟩
  have hU : M6.FiberSum.UniformFibers L' k := by
    intro b
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, L a₀ = b.val := by
      simpa [M6.ActualCounts.imageWords] using b.property
    have hp : (fun a => L' a = b) = (fun a => L a = L a₀) := by
      funext a
      apply propext
      constructor
      · intro ha
        exact (congrArg Subtype.val ha).trans ha₀.symm
      · intro ha
        apply Subtype.ext
        exact ha.trans ha₀
    change (Finset.univ.filter (fun a => L' a = b)).card = k
    rw [hp]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h a₀
  have hs := M6.FiberSum.uniform_weighted_sum α γ L' k hU (fun b => w b.val)
  change (∑ a, w (L a)) = Polynomial.C (k : ℤ) * (∑ b : γ, w b.val) at hs
  rw [hs]
  congr 1
  apply Finset.sum_bij (fun (b : γ) _ => b.val)
  · intro b hb
    exact b.property
  · intro b₁ hb₁ b₂ hb₂ he
    exact Subtype.ext he
  · intro b hb
    exact ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩
  · intro b hb
    rfl
