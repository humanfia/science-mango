import FrozenTarget_0921f350d1e49d98
theorem M6.Transfer.actual_trace_intermediates : QuantumHarnessFrozenTarget := by
  classical
  intro R N W k d hmass hdegree
  have hterm (start : M6.Transfer.Memory R) :
      (M6.Transfer.scalarLayers (N := N) W start N (start, d)).natAbs ≤ 8 ^ N := by
    rw [M6.Transfer.scalar_layers_exact R N W start N hdegree]
    change ((M6.Transfer.layers W start N start).coeff d.val).natAbs ≤ 8 ^ N
    calc
      _ ≤ M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) :=
        M6.Transfer.mass_basic.2.2.2 _ _
      _ ≤ M6.Transfer.rowMass (M6.Transfer.layers W start N) := by
        unfold M6.Transfer.rowMass
        exact Finset.single_le_sum
          (f := fun m : M6.Transfer.Memory R =>
            M6.Transfer.polynomialMass (M6.Transfer.layers W start N m))
          (fun m _ => Nat.zero_le _) (Finset.mem_univ start)
      _ ≤ 8 ^ N := M6.Transfer.layers_mass R W start N hmass
  have hlist (l : List (M6.Transfer.Memory R)) :
      ((l.map (fun start => M6.Transfer.scalarLayers (N := N) W start N (start, d))).sum).natAbs ≤
        l.length * 8 ^ N := by
    induction l with
    | nil => simp
    | cons start l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ (M6.Transfer.scalarLayers (N := N) W start N (start, d)).natAbs +
            ((l.map (fun start => M6.Transfer.scalarLayers (N := N) W start N (start, d))).sum).natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ 8 ^ N + l.length * 8 ^ N := Nat.add_le_add (hterm start) ih
        _ = (l.length + 1) * 8 ^ N := by omega
  have hlength :
      (((Finset.univ : Finset (M6.Transfer.Memory R)).toList).take k).length ≤ 2 ^ R := by
    calc
      _ ≤ ((Finset.univ : Finset (M6.Transfer.Memory R)).toList).length := by
        simp only [List.length_take]
        exact Nat.min_le_right _ _
      _ = Fintype.card (M6.Transfer.Memory R) := by simp
      _ = 2 ^ R := M6.Transfer.state_count R
  exact (hlist _).trans (Nat.mul_le_mul_right (8 ^ N) hlength)
