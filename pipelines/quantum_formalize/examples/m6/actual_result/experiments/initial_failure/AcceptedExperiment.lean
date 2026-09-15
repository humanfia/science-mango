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
#print axioms M6.ActualResult.boundary_normalized
