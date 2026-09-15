import FrozenTarget_d84fa9ea4f4849b8
theorem M6.ActualCounts.finite_image_weighted_sum : QuantumHarnessFrozenTarget := by
  classical
  intro α β _ L k hk w
  let B := {b : β // b ∈ M6.ActualCounts.imageWords L}
  let L' : α → B := fun a => ⟨L a, by simp [M6.ActualCounts.imageWords]⟩
  have hu : M6.FiberSum.UniformFibers L' k := by
    intro b
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, L a₀ = b.val := by
      simpa [M6.ActualCounts.imageWords] using b.property
    have hb : Nat.card {a : α // L a = b.val} = k := by
      rw [← ha₀]
      exact hk a₀
    have hc : Fintype.card {a : α // L a = b.val} =
        (Finset.univ.filter (fun a : α => L a = b.val)).card := by
      apply Fintype.subtype_card
      intro a
      simp
    rw [Nat.card_eq_fintype_card, hc] at hb
    simpa [M6.FiberSum.fiber, L', Subtype.ext_iff] using hb
  have hs := M6.FiberSum.uniform_weighted_sum α B L' k hu (fun b => w b.val)
  simpa [M6.FiberSum.pullbackSum, L', B, Finset.sum_coe_sort] using hs
