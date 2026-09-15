import FrozenTarget_2595bcbaf8508999
theorem M7.PrefixBits.left_step : QuantumHarnessFrozenTarget := by
  intro N hN p bit hp
   dsimp only
   classical
   have hg : ∀ (q : List Bool) (k : ℕ),
       (q ++ [bit]).getD k false =
         if k < q.length then q.getD k false else if k = q.length then bit else false := by
     intro q
     induction q with
     | nil =>
         intro k
         cases k <;> simp [List.getD]
     | cons a q ih =>
         intro k
         cases k with
         | zero => simp [List.getD]
         | succ k => simpa [List.getD] using ih k
   have hs : ∀ (q : List Bool) (off k : ℕ),
       k + 1 ∈ M7.PrefixBits.selected N off q ↔
         k < N - 1 ∧ off + k < q.length ∧ q.getD (off + k) false = true := by
     intros q off k
     simp [M7.PrefixBits.selected, Finset.mem_image]
   have hu : ∀ (q : List Bool) (off k : ℕ),
       k + 1 ∈ M7.PrefixBits.undecided N off q ↔
         k < N - 1 ∧ q.length ≤ off + k := by
     intros q off k
     simp [M7.PrefixBits.undecided, Finset.mem_image]
   have hs0 : ∀ (q : List Bool) (off : ℕ),
       0 ∈ M7.PrefixBits.selected N off q := by
     intros q off
     simp [M7.PrefixBits.selected]
   have hu0 : ∀ (q : List Bool) (off : ℕ),
       0 ∉ M7.PrefixBits.undecided N off q := by
     intros q off
     simp [M7.PrefixBits.undecided, Finset.mem_image]
   refine ⟨?_, ?_, ?_, ?_, ?_⟩
   · simpa [M7.PrefixBits.WA, hu] using hp
   · apply Finset.ext
     intro x
     cases x with
     | zero => cases bit <;> simp [M7.PrefixBits.A, hs0]
     | succ k =>
         change (k + 1 ∈ M7.PrefixBits.A N (p ++ [bit])) ↔ _
         by_cases hk : k < p.length
         · have he : k ≠ p.length := by omega
           have he' : k + 1 ≠ p.length + 1 := by omega
           have hl : k < p.length + 1 := by omega
           cases bit <;>
             simp [M7.PrefixBits.A, hs, hg, hk, he, he', hl]
         · by_cases he : k = p.length
           · subst k
             cases bit <;> simp [M7.PrefixBits.A, hs, hg, hp]
           · have he' : k + 1 ≠ p.length + 1 := by omega
             have hl : ¬ k < p.length + 1 := by omega
             cases bit <;>
               simp [M7.PrefixBits.A, hs, hg, hk, he, he', hl]
   · apply Finset.ext
     intro x
     cases x with
     | zero => simp [M7.PrefixBits.B, hs0]
     | succ k =>
         change (k + 1 ∈ M7.PrefixBits.B N (p ++ [bit])) ↔ _
         have h0 : ¬ N - 1 + k < p.length := by omega
         have h1 : ¬ N - 1 + k < p.length + 1 := by omega
         simp [M7.PrefixBits.B, hs, h0, h1]
   · apply Finset.ext
     intro x
     cases x with
     | zero => simp [M7.PrefixBits.WA, hu0]
     | succ k =>
         change (k + 1 ∈ M7.PrefixBits.WA N (p ++ [bit])) ↔ _
         simp only [M7.PrefixBits.WA, Finset.mem_erase, hu,
           List.length_append, List.length_singleton, zero_add]
         omega
   · apply Finset.ext
     intro x
     cases x with
     | zero => simp [M7.PrefixBits.WB, hu0]
     | succ k =>
         change (k + 1 ∈ M7.PrefixBits.WB N (p ++ [bit])) ↔ _
         simp only [M7.PrefixBits.WB, hu, List.length_append, List.length_singleton]
         omega
