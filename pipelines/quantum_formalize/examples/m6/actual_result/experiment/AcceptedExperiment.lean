import M6ActualResultReady

theorem M6.ActualResult.boundary_normalized : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  have ha : a.natDegree < N :=
    lt_of_le_of_lt (le_max_left a.natDegree b.natDegree) h
  have hb : b.natDegree < N :=
    lt_of_le_of_lt (le_max_right a.natDegree b.natDegree) h
  have ha' : a.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast ha)
  have hb' : b.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hb)
  rw [M6.ActualTransfer.boundary_trace_inputs N a b h P]
  have hs := M6.ActualCounts.boundary_pinned_sum N a b ha' hb' P
  calc
    _ = M6.Normalize.divide ((2 : ℤ) ^ M6.ActualCounts.f N a b)
        (Polynomial.C ((2 : ℤ) ^ M6.ActualCounts.f N a b) *
          M6.Pinned.enumerator (M6.Spaces.boundaryWords N
            (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P) :=
      congrArg (M6.Normalize.divide ((2 : ℤ) ^ M6.ActualCounts.f N a b)) hs
    _ = _ := M6.Normalize.divide_scaled _ _ (pow_ne_zero _ (by norm_num))

theorem M6.ActualResult.cycle_normalized : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  have ha : a.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_left a.natDegree b.natDegree) h : a.natDegree < N)
  have hb : b.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_right a.natDegree b.natDegree) h : b.natDegree < N)
  rw [M6.ActualTransfer.character_trace_inputs N a b h P]
  change M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualCounts.signedInputSum N a b P) = _
  rw [M6.ActualCounts.cycle_pinned_sum N a b ha hb P]
  exact M6.Normalize.divide_scaled _ _ (pow_ne_zero N (by norm_num))

theorem M6.ActualResult.Q_enumerator : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.Q N a b P = M6.Pinned.enumerator (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.Q N a b P = M6.Pinned.enumerator (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  unfold M6.ActualTransfer.Q
  change M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) - M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = _
  rw [M6.ActualResult.cycle_normalized N a b h P, M6.ActualResult.boundary_normalized N a b h P]
  unfold M6.Spaces.logicalWords
  symm
  apply M6.Pinned.enumerator_sdiff <;> exact M6.Spaces.boundaries_are_cycles N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)

theorem M6.ActualResult.Q_coeff : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ (P : M6.Pinned.Pins (2*N)) (d : ℕ), (M6.ActualTransfer.Q N a b P).coeff d = M6.Pinned.count (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P d ∧ 0 ≤ (M6.ActualTransfer.Q N a b P).coeff d := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ (P : M6.Pinned.Pins (2*N)) (d : ℕ), (M6.ActualTransfer.Q N a b P).coeff d = M6.Pinned.count (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P d ∧ 0 ≤ (M6.ActualTransfer.Q N a b P).coeff d
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P d
  rw [M6.ActualResult.Q_enumerator N a b h P, M6.Pinned.enumerator_coeff (2*N)]
  exact ⟨rfl, (M6.Pinned.count_nonnegative_positive (2*N) _ P d).1⟩

theorem M6.ActualResult.Q_total : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → Polynomial.eval 1 (M6.ActualTransfer.Q N a b (M6.Pinned.free (2*N))) = ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card : ℤ) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → Polynomial.eval 1 (M6.ActualTransfer.Q N a b (M6.Pinned.free (2*N))) = ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card : ℤ)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  rw [M6.ActualResult.Q_enumerator N a b h]
  exact M6.Pinned.enumerator_total _ _

theorem M6.ActualResult.Q_zero : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), (M6.ActualTransfer.Q N a b P).coeff 0 = 0 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), (M6.ActualTransfer.Q N a b P).coeff 0 = 0
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  rw [M6.ActualResult.Q_enumerator N a b h P]
  apply M6.Pinned.enumerator_zero_coeff
  exact M6.Spaces.zero_not_logical N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)

theorem M6.ActualResult.solve_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → (M6.ActualTransfer.solve N a b = none ↔ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → v ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)), d ≤ M6.Pinned.weight u) ∧ k ≤ 2*N := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → (M6.ActualTransfer.solve N a b = none ↔ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → v ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)), d ≤ M6.Pinned.weight u) ∧ k ≤ 2*N
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  exact M6.Pinned.solve_exact (2 * N)
    (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a)
      (M6.Coordinates.coefficients N b))
    (M6.ActualTransfer.Q N a b)
    (M6.ActualResult.Q_enumerator N a b h)
#print axioms M6.ActualResult.boundary_normalized
#print axioms M6.ActualResult.cycle_normalized
#print axioms M6.ActualResult.Q_enumerator
#print axioms M6.ActualResult.Q_coeff
#print axioms M6.ActualResult.Q_total
#print axioms M6.ActualResult.Q_zero
#print axioms M6.ActualResult.solve_exact
