import FrozenTarget_dee0167e6380577f
theorem M7.PrefixCompleted.union_injective : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N w E A B WA WB hA hB
    have bounds : ∀ z ∈ M7.PrefixSector.completions N w E A B WA WB,
        z.1 ⊆ WA ∧ z.2 ⊆ WB := by
      intro z hz
      obtain ⟨F, hF, hz⟩ :=
        (M7.PrefixSector.completion_membership N w E A B WA WB z).mp hz
      simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter,
        Finset.mem_product, Finset.mem_powersetCard] at hz
      aesop
    have cancel : ∀ (S W U V : Finset ℕ), Disjoint S W →
        U ⊆ W → V ⊆ W → S ∪ U = S ∪ V → U = V := by
      intro S W U V hd hU hV he
      have hd' := Finset.disjoint_left.mp hd
      apply Finset.ext
      intro i
      constructor
      · intro hi
        have hm : i ∈ S ∪ V := he ▸ Finset.mem_union_right S hi
        rcases Finset.mem_union.mp hm with hs | hv
        · exact False.elim (hd' hs (hU hi))
        · exact hv
      · intro hi
        have hm : i ∈ S ∪ U := he.symm ▸ Finset.mem_union_right S hi
        rcases Finset.mem_union.mp hm with hs | hu
        · exact False.elim (hd' hs (hV hi))
        · exact hu
    intro x hx y hy hxy
    obtain ⟨hxA, hxB⟩ := bounds x hx
    obtain ⟨hyA, hyB⟩ := bounds y hy
    apply Prod.ext
    · exact cancel A WA x.1 y.1 hA hxA hyA (congrArg Prod.fst hxy)
    · exact cancel B WB x.2 y.2 hB hxB hyB (congrArg Prod.snd hxy)
