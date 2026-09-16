import M8OptimizerResources

theorem M8.OptimizerResources.distance_work : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualDistanceWork N a b ≤ 50000*(N+1)^5 := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualDistanceWork N a b ≤ 50000 * (N + 1)^5
  intro N inst a b h
  have hspan : M6.ActualTransfer.span a b < N :=
    lt_of_le_of_lt h ((M8.Cutoff.limit_bounds N).2.2 (NeZero.pos N))
  apply le_trans (M6.ActualTransfer.actual_distance_work N a b hspan)
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left 50000 ((M8.Cutoff.indexed_work_envelopes N (M6.ActualTransfer.span a b) h).1)

theorem M8.OptimizerResources.indexed_guarantee : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M8.OptimizerResources.weight N a b pins character) := by
  intro N inst a b pins character hspan
  have hlt : M6.ActualTransfer.span a b < N :=
    lt_of_le_of_lt hspan ((M8.Cutoff.limit_bounds N).2.2 (NeZero.pos N))
  cases character with
  | false =>
      simpa [M8.OptimizerResources.weight] using
        (M6.ActualTransfer.boundary_indexed_resources N a b pins hlt)
  | true =>
      simpa [M8.OptimizerResources.weight] using
        (M6.ActualTransfer.character_indexed_resources N a b pins hlt)

theorem M8.OptimizerResources.solve_storage : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualSolveStorage N a b ≤ 16384*(N+1)^3 := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualSolveStorage N a b ≤ 16384 * (N + 1)^3
  intro N inst a b h
  have hspan : M6.ActualTransfer.span a b < N :=
    lt_of_le_of_lt h ((M8.Cutoff.limit_bounds N).2.2 (NeZero.pos N))
  calc
    M6.ActualTransfer.actualSolveStorage N a b ≤ 16384 * N^2 * 2^(M6.ActualTransfer.span a b) :=
      M6.ActualTransfer.actual_solve_storage N a b hspan
    _ ≤ 16384 * (N + 1)^3 := by
      simpa only [mul_assoc] using
        Nat.mul_le_mul_left 16384 (M8.Cutoff.indexed_storage_envelope N (M6.ActualTransfer.span a b) h)

theorem M8.OptimizerResources.weight_bounds : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), ∀ i m t, M6.Transfer.polynomialMass ((M8.OptimizerResources.weight N a b pins character) i m t) ≤ 4 ∧ ((M8.OptimizerResources.weight N a b pins character) i m t).natDegree ≤ 2 := by
  intro N inst a b pins character i m t
  cases character with
  | false =>
      simp only [M8.OptimizerResources.weight, Bool.false_eq_true, if_false,
        M6.ActualTransfer.boundaryWeight]
      apply M6.Transfer.boundary_edge_bounds
  | true =>
      simp only [M8.OptimizerResources.weight, if_true,
        M6.ActualTransfer.characterWeight]
      apply M6.Transfer.character_edge_bounds

theorem M8.OptimizerResources.witness_work : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.solve N a b = some (d,v,k) → M6.ActualTransfer.actualWitnessWork N a b k ≤ 200000*(N+1)^6 := by
  intro N inst a b d v k hcut hsolve
  have hspan : M6.ActualTransfer.span a b < N :=
    lt_of_le_of_lt hcut ((M8.Cutoff.limit_bounds N).2.2 (NeZero.pos N))
  refine le_trans (M6.ActualTransfer.actual_witness_work N a b d v k hspan hsolve) ?_
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left 200000
      ((M8.Cutoff.indexed_work_envelopes N (M6.ActualTransfer.span a b) hcut).2)

theorem M8.OptimizerResources.scatter_capacity : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → ∀ (start : M6.Transfer.Memory (M6.ActualTransfer.span a b)) (i : ℕ), i < N → ∀ (k : ℕ) (addr : M6.Transfer.CoefficientAddress (M6.ActualTransfer.span a b) N), (((M6.Transfer.scatterEventList (M6.ActualTransfer.span a b) N).take k).foldl (M6.Transfer.scatterUpdate ((M8.OptimizerResources.weight N a b pins character) i) (M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start i)) (fun _ => 0) addr).natAbs < 2^(4*(N+1)) ∧ ∀ e : M6.Transfer.ScatterEvent (M6.ActualTransfer.span a b) N, (M6.Transfer.eventTerm ((M8.OptimizerResources.weight N a b pins character) i) (M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start i) e).natAbs < 2^(4*(N+1)) := by
  intro N inst a b pins character hspan start i hi k addr
  have hbounds := M6.Transfer.actual_layer_intermediates
    (M6.ActualTransfer.span a b) N
    (M8.OptimizerResources.weight N a b pins character) start i k addr
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).1)
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).2)
  have hpow : (8 : ℕ) ^ (i + 1) ≤ 8 ^ N := by
    gcongr <;> omega
  have hpositive : 0 < (2 : ℕ) ^ M6.ActualTransfer.span a b := by
    positivity
  have hone : 1 ≤ (2 : ℕ) ^ M6.ActualTransfer.span a b := hpositive
  have hmul : (8 : ℕ) ^ N ≤ 2 ^ M6.ActualTransfer.span a b * 8 ^ N := by
    calc
      8 ^ N = 1 * 8 ^ N := (one_mul _).symm
      _ ≤ 2 ^ M6.ActualTransfer.span a b * 8 ^ N := Nat.mul_le_mul_right _ hone
  have hcapacity : (8 : ℕ) ^ (i + 1) < 2 ^ (4 * (N + 1)) :=
    lt_of_le_of_lt (le_trans hpow hmul)
      (M8.Cutoff.coefficient_capacity N (M6.ActualTransfer.span a b) hspan)
  constructor
  · exact lt_of_le_of_lt hbounds.1 hcapacity
  · intro e
    exact lt_of_le_of_lt (hbounds.2 e) hcapacity

theorem M8.OptimizerResources.trace_capacity : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → ∀ d : ℕ, ((M6.Transfer.arrayTrace (M8.OptimizerResources.weight N a b pins character) N).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N ∧ ((M6.Transfer.arrayTrace (M8.OptimizerResources.weight N a b pins character) N).coeff d).natAbs < 2^(4*(N+1)) := by
  intro N inst a b pins character hcut d
  have hbound : ((M6.Transfer.arrayTrace (M8.OptimizerResources.weight N a b pins character) N).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    apply M6.Transfer.trace_coefficient_bound
    all_goals
      intros
      first
      | exact (M8.OptimizerResources.weight_bounds N a b pins character _ _ _).1
      | exact (M8.OptimizerResources.weight_bounds N a b pins character _ _ _).2
  exact ⟨hbound, lt_of_le_of_lt hbound (M8.Cutoff.coefficient_capacity N (M6.ActualTransfer.span a b) hcut)⟩

theorem M8.OptimizerResources.trace_prefix_capacity : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → ∀ (k : ℕ) (d : Fin (2*N+1)), (((((Finset.univ : Finset (M6.Transfer.Memory (M6.ActualTransfer.span a b))).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start N (start,d))).sum)).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N ∧ (((((Finset.univ : Finset (M6.Transfer.Memory (M6.ActualTransfer.span a b))).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start N (start,d))).sum)).natAbs < 2^(4*(N+1)) := by
  intro N inst a b pins character hcut k d
  have h := M6.Transfer.actual_trace_intermediates
    (M6.ActualTransfer.span a b) N
    (M8.OptimizerResources.weight N a b pins character) k d
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).1)
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).2)
  exact ⟨h, lt_of_le_of_lt h (M8.Cutoff.coefficient_capacity N (M6.ActualTransfer.span a b) hcut)⟩
#print axioms M8.OptimizerResources.distance_work
#print axioms M8.OptimizerResources.indexed_guarantee
#print axioms M8.OptimizerResources.solve_storage
#print axioms M8.OptimizerResources.weight_bounds
#print axioms M8.OptimizerResources.scatter_capacity
#print axioms M8.OptimizerResources.trace_capacity
#print axioms M8.OptimizerResources.trace_prefix_capacity
#print axioms M8.OptimizerResources.witness_work
