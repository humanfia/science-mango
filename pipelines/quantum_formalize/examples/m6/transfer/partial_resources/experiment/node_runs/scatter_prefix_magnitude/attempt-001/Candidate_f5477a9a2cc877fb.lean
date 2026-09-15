import FrozenTarget_f5477a9a2cc877fb
theorem M6.Transfer.scatter_prefix_magnitude : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N) (k : ℕ) (addr : M6.Transfer.CoefficientAddress R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → (((M6.Transfer.scatterEventList R N).take k).foldl (M6.Transfer.scatterUpdate W input) (fun _ => 0) addr).natAbs ≤ 8 * M6.Transfer.arrayMass input
  intro R N W input k addr hW
  let f : M6.Transfer.ScatterEvent R N → ℤ := fun e =>
    if M6.Transfer.eventDestination e = some addr then M6.Transfer.eventTerm W input e else 0
  let g : M6.Transfer.ScatterEvent R N → ℕ := fun e =>
    (M6.Transfer.eventTerm W input e).natAbs
  have hf (e : M6.Transfer.ScatterEvent R N) : (f e).natAbs ≤ g e := by
    dsimp [f, g]
    split <;> simp
  have hlist (l : List (M6.Transfer.ScatterEvent R N)) (j : ℕ) :
      (((l.take j).map f).sum).natAbs ≤ (l.map g).sum := by
    induction l generalizing j with
    | nil => simp
    | cons e l ih =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hf e) (ih j))
  rw [M6.Transfer.scatter_prefix_formula, zero_add]
  change ((((M6.Transfer.scatterEventList R N).take k).map f).sum).natAbs ≤ _
  apply (hlist (M6.Transfer.scatterEventList R N) k).trans
  simpa [M6.Transfer.scatterEventList, g, M6.Transfer.eventMass] using
    (M6.Transfer.event_mass_bound R N W input hW)
