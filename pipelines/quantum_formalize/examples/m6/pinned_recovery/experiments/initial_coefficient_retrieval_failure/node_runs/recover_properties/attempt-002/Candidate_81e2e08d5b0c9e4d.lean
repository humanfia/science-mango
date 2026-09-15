import FrozenTarget_81e2e08d5b0c9e4d
theorem M6.Pinned.recover_properties : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (xs : List (Fin m)), M6.Pinned.refines P (M6.Pinned.recover c P xs).1 ∧ (∀ i ∈ xs, (M6.Pinned.recover c P xs).1 i ≠ none) ∧ (M6.Pinned.recover c P xs).2 ≤ xs.length
  intro m c P xs
  have trans_refines (A B C : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (hBC : M6.Pinned.refines B C) :
      M6.Pinned.refines A C := by
    unfold M6.Pinned.refines at hAB hBC ⊢
    intro j b hj
    exact hBC j b (hAB j b hj)
  have preserve (A B : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (j : Fin m)
      (hj : A j ≠ none) : B j ≠ none := by
    unfold M6.Pinned.refines at hAB
    cases h : A j with
    | none => exact False.elim (hj h)
    | some b =>
        rw [hAB j b h]
        simp
  induction xs generalizing P with
  | nil =>
      simp [M6.Pinned.recover, M6.Pinned.refines]
  | cons i xs ih =>
      have hcprop := M6.Pinned.choose_properties m c P i
      cases hc : M6.Pinned.choose c P i with
      | mk Q k =>
          have hrprop := ih Q
          cases hr : M6.Pinned.recover c Q xs with
          | mk R n =>
              simp only [hc, Prod.fst, Prod.snd] at hcprop
              simp only [hr, Prod.fst, Prod.snd] at hrprop
              simp only [M6.Pinned.recover, hc, hr, Prod.fst, Prod.snd]
              refine ⟨trans_refines P Q R hcprop.1 hrprop.1, ?_, ?_⟩
              · intro j hj
                rcases List.mem_cons.mp hj with hji | hj
                · rw [hji]
                  exact preserve Q R hrprop.1 i hcprop.2.1
                · exact hrprop.2.1 j hj
              · have hk := hcprop.2.2
                have hn := hrprop.2.2
                simp only [List.length_cons]
                omega
