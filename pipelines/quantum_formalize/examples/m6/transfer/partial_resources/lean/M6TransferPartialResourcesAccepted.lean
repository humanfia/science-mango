import M6TransferPartialResourcesReady

theorem M6.Transfer.actual_trace_intermediates : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (k : ℕ) (d : Fin (2*N+1)), (∀ j m t, M6.Transfer.polynomialMass (W j m t) ≤ 4) → (∀ j m t, (W j m t).natDegree ≤ 2) → ((((Finset.univ : Finset (M6.Transfer.Memory R)).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) W start N (start,d))).sum).natAbs ≤ 2^R * 8^N := by
  classical
  intro R N W k d hmass hdeg
  have hterm (start : M6.Transfer.Memory R) :
      (M6.Transfer.scalarLayers (N := N) W start N (start, d)).natAbs ≤ 8^N := by
    rw [M6.Transfer.scalar_layers_exact R N W start N hdeg]
    change ((M6.Transfer.layers W start N start).coeff d.val).natAbs ≤ 8^N
    calc
      _ ≤ M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) :=
        M6.Transfer.mass_basic.2.2.2 _ _
      _ ≤ M6.Transfer.rowMass (M6.Transfer.layers W start N) := by
        unfold M6.Transfer.rowMass
        exact Finset.single_le_sum
          (f := fun m => M6.Transfer.polynomialMass (M6.Transfer.layers W start N m))
          (fun m _ => Nat.zero_le _) (Finset.mem_univ start)
      _ ≤ 8^N := M6.Transfer.layers_mass R W start N hmass
  have hlist (l : List (M6.Transfer.Memory R)) :
      ((l.map (fun start => M6.Transfer.scalarLayers (N := N) W start N (start, d))).sum).natAbs
        ≤ l.length * 8^N := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ (M6.Transfer.scalarLayers (N := N) W a N (a, d)).natAbs +
            ((l.map (fun start => M6.Transfer.scalarLayers (N := N) W start N (start, d))).sum).natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ 8^N + l.length * 8^N := Nat.add_le_add (hterm a) ih
        _ = (l.length + 1) * 8^N := by simp [Nat.add_mul, Nat.add_comm]
  have hlen :
      (((Finset.univ : Finset (M6.Transfer.Memory R)).toList).take k).length ≤ 2^R := by
    calc
      _ ≤ (Finset.univ : Finset (M6.Transfer.Memory R)).toList.length := by
        simp only [List.length_take]
        exact Nat.min_le_right _ _
      _ = 2^R := by simp [M6.Transfer.state_count]
  exact (hlist _).trans (Nat.mul_le_mul_right (8^N) hlen)

theorem M6.Transfer.finite_coefficient_mass : ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p := by
  classical
  change ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p
  intro p L
  change (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ ∑ d ∈ p.support, (p.coeff d).natAbs
  have hfin : (∑ d : Fin L, (p.coeff d.val).natAbs) = ∑ d ∈ Finset.range L, (p.coeff d).natAbs :=
    Fin.sum_univ_eq_sum_range (fun d : ℕ => (p.coeff d).natAbs) L
  rw [hfin]
  calc
    (∑ d ∈ Finset.range L, (p.coeff d).natAbs) ≤
        ∑ d ∈ p.support ∪ Finset.range L, (p.coeff d).natAbs := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_union_right
      · intros
        exact Nat.zero_le _
    _ = ∑ d ∈ p.support, (p.coeff d).natAbs := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro d hd hnot
      have hz : p.coeff d = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hnot
      simp [hz]

theorem M6.Transfer.encoded_array_mass : ∀ (R N : ℕ) (v : M6.Transfer.Memory R → Polynomial ℤ), M6.Transfer.arrayMass (M6.Transfer.encodeCoefficients (N:=N) v) ≤ M6.Transfer.rowMass v := by
  classical
  change ∀ (R N : ℕ) (v : M6.Transfer.Memory R → Polynomial ℤ), M6.Transfer.arrayMass (M6.Transfer.encodeCoefficients (N := N) v) ≤ M6.Transfer.rowMass v
  intro R N v
  change (∑ addr : M6.Transfer.Memory R × Fin (2 * N + 1), ((v addr.1).coeff addr.2.val).natAbs) ≤ ∑ m : M6.Transfer.Memory R, M6.Transfer.polynomialMass (v m)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro m hm
  exact M6.Transfer.finite_coefficient_mass (v m) (2 * N + 1)

theorem M6.Transfer.event_mass_bound : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.eventMass W input ≤ 8 * M6.Transfer.arrayMass input := by
  classical
  change ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.eventMass W input ≤ 8 * M6.Transfer.arrayMass input
  intro R N W input hW
  unfold M6.Transfer.eventMass M6.Transfer.arrayMass
  simp only [M6.Transfer.ScatterEvent, M6.Transfer.CoefficientAddress,
    Fintype.sum_prod_type, M6.Transfer.eventTerm, Int.natAbs_mul]
  calc
    _ ≤ ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
        ∑ i : Fin (2 * N + 1), (input (m, i)).natAbs * 4 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _
        ((M6.Transfer.finite_coefficient_mass (W m t) 3).trans (hW m t))
    _ = _ := by
      simp [M6.Transfer.Bit, ← Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] <;> ring

theorem M6.Transfer.scatter_prefix_magnitude : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N) (k : ℕ) (addr : M6.Transfer.CoefficientAddress R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → (((M6.Transfer.scatterEventList R N).take k).foldl (M6.Transfer.scatterUpdate W input) (fun _ => 0) addr).natAbs ≤ 8 * M6.Transfer.arrayMass input := by
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

theorem M6.Transfer.actual_layer_intermediates : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (i k : ℕ) (addr : M6.Transfer.CoefficientAddress R N), (∀ j m t, M6.Transfer.polynomialMass (W j m t) ≤ 4) → (∀ j m t, (W j m t).natDegree ≤ 2) → ((((M6.Transfer.scatterEventList R N).take k).foldl (M6.Transfer.scatterUpdate (W i) (M6.Transfer.scalarLayers (N:=N) W start i)) (fun _ => 0) addr).natAbs ≤ 8^(i+1)) ∧ (∀ e : M6.Transfer.ScatterEvent R N, (M6.Transfer.eventTerm (W i) (M6.Transfer.scalarLayers (N:=N) W start i) e).natAbs ≤ 8^(i+1)) := by
  classical
  intro R N W start i k addr hmass hdegree
  have hinput : M6.Transfer.arrayMass (M6.Transfer.scalarLayers (N := N) W start i) ≤ 8 ^ i := by
    rw [M6.Transfer.scalar_layers_exact R N W start i hdegree]
    exact (M6.Transfer.encoded_array_mass R N (M6.Transfer.layers W start i)).trans
      (M6.Transfer.layers_mass R W start i hmass)
  have hbound : 8 * M6.Transfer.arrayMass (M6.Transfer.scalarLayers (N := N) W start i) ≤ 8 ^ (i + 1) := by
    calc
      _ ≤ 8 * 8 ^ i := Nat.mul_le_mul_left 8 hinput
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  constructor
  · exact (M6.Transfer.scatter_prefix_magnitude R N (W i)
      (M6.Transfer.scalarLayers (N := N) W start i) k addr (hmass i)).trans hbound
  · intro e
    have he : (M6.Transfer.eventTerm (W i)
        (M6.Transfer.scalarLayers (N := N) W start i) e).natAbs ≤
        M6.Transfer.eventMass (W i) (M6.Transfer.scalarLayers (N := N) W start i) := by
      unfold M6.Transfer.eventMass
      exact Finset.single_le_sum
        (f := fun e : M6.Transfer.ScatterEvent R N =>
          (M6.Transfer.eventTerm (W i)
            (M6.Transfer.scalarLayers (N := N) W start i) e).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    exact he.trans ((M6.Transfer.event_mass_bound R N (W i)
      (M6.Transfer.scalarLayers (N := N) W start i) (hmass i)).trans hbound)
#print axioms M6.Transfer.actual_trace_intermediates
#print axioms M6.Transfer.finite_coefficient_mass
#print axioms M6.Transfer.encoded_array_mass
#print axioms M6.Transfer.event_mass_bound
#print axioms M6.Transfer.scatter_prefix_magnitude
#print axioms M6.Transfer.actual_layer_intermediates
