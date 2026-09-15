import FrozenTarget_125b3a7d7b923d3e
theorem M6.Pinned.recover_properties : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (xs : List (Fin m)), M6.Pinned.refines P (M6.Pinned.recover c P xs).1 ∧ (∀ i ∈ xs, (M6.Pinned.recover c P xs).1 i ≠ none) ∧ (M6.Pinned.recover c P xs).2 ≤ xs.length
  intro m c P xs
  have trans_refines (A B C : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (hBC : M6.Pinned.refines B C) :
      M6.Pinned.refines A C := by
    unfold M6.Pinned.refines at *
    intro j
    have h₁ := hAB j
    have h₂ := hBC j
    cases A j <;> cases B j <;> cases C j <;> simp_all
  have preserve (A B : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (j : Fin m) (hj : A j ≠ none) :
      B j ≠ none := by
    unfold M6.Pinned.refines at hAB
    have h := hAB j
    cases A j <;> cases B j <;> simp_all
  induction xs generalizing P with
  | nil =>
      simp [M6.Pinned.recover, M6.Pinned.refines]
  | cons i xs ih =>
      have hcprop := M6.Pinned.choose_properties m c P i
      rcases hc : M6.Pinned.choose c P i with ⟨Q, n⟩
      have hrprop := ih Q
      rcases hr : M6.Pinned.recover c Q xs with ⟨R, k⟩
      simp only [hc, Prod.fst, Prod.snd] at hcprop
      simp only [hr, Prod.fst, Prod.snd] at hrprop
      rcases hcprop with ⟨hPQ, hi, hn⟩
      rcases hrprop with ⟨hQR, hxs, hk⟩
      simp only [M6.Pinned.recover, hc, hr, Prod.fst, Prod.snd]
      refine ⟨trans_refines P Q R hPQ hQR, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact preserve Q R hQR i hi
        · exact hxs j hj
      · simp only [List.length_cons]
        omega
