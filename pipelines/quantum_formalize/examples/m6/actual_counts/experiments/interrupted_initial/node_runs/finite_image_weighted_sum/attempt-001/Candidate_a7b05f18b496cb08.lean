import FrozenTarget_a7b05f18b496cb08
theorem M6.ActualCounts.finite_image_weighted_sum : QuantumHarnessFrozenTarget := by
  classical
  intro α β inst L k h w
  let γ := {b : β // b ∈ M6.ActualCounts.imageWords L}
  let L' : α → γ := fun a => ⟨L a, by simp [M6.ActualCounts.imageWords]⟩
  have hu : M6.FiberSum.UniformFibers L' k := by
    intro b
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : α, L a₀ = b.val := by
      simpa [M6.ActualCounts.imageWords] using b.property
    have heq : ∀ a : α, L' a = b ↔ L a = L a₀ := by
      intro a
      simp [L', Subtype.ext_iff, ha₀]
    simpa [M6.FiberSum.fiber, Nat.card_eq_fintype_card,
      Fintype.card_subtype, heq] using h a₀
  have hs : (∑ b : γ, w b.val) = ∑ b ∈ M6.ActualCounts.imageWords L, w b := by
    apply Finset.sum_bij (fun b _ => b.val)
    · intro b hb
      exact b.property
    · intro b₁ hb₁ b₂ hb₂ he
      exact Subtype.ext he
    · intro b hb
      exact ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩
    · intro b hb
      rfl
  have ht := M6.FiberSum.uniform_weighted_sum α γ L' k hu (fun b => w b.val)
  change (∑ a, w (L a)) = Polynomial.C (k : ℤ) * (∑ b : γ, w b.val) at ht
  rw [hs] at ht
  exact ht
