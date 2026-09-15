import M5PackingInjective
import M5SupportPolynomial

theorem M5.SupportPolynomial.packed_sum_image : ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) → M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r) = ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ M5.Packing.packedValue r i := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) → M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r) = ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ M5.Packing.packedValue r i
  intro w T r hinj
  classical
  unfold M5.SupportPolynomial.ofSupport M5.Packing.packedSupport
  apply Finset.sum_image
  intro i hi j hj hij
  exact hinj hij

theorem M5.SupportPolynomial.quotient_monomial_period : ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a) := by
  change ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a)
  intro T a j
  let q := AdjoinRoot.mk (M5.cyclicModulus T)
  have htwo : (1 : M5.BinaryPolynomial) + 1 = 0 := by
    have h : (1 : ZMod 2) + 1 = 0 := by decide
    simpa only [map_add, Polynomial.C_1, map_zero] using congrArg (Polynomial.C : ZMod 2 → M5.BinaryPolynomial) h
  have htwoq : (1 : AdjoinRoot (M5.cyclicModulus T)) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg q htwo
  have hmod : q ((Polynomial.X : M5.BinaryPolynomial) ^ T + 1) = 0 := by
    change AdjoinRoot.mk (M5.cyclicModulus T) (M5.cyclicModulus T) = 0
    exact AdjoinRoot.mk_self
  have hsum : q Polynomial.X ^ T + 1 = 0 := by
    simpa only [map_add, map_pow, map_one] using hmod
  have hpow : q Polynomial.X ^ T = 1 := by
    apply add_right_cancel (b := (1 : AdjoinRoot (M5.cyclicModulus T)))
    exact hsum.trans htwoq.symm
  change q (Polynomial.X ^ (a + j * T)) = q (Polynomial.X ^ a)
  rw [map_pow, map_pow, pow_add, Nat.mul_comm j T, pow_mul, hpow, one_pow, mul_one]

theorem M5.SupportPolynomial.support_coeff_zero : ∀ S : Finset ℕ, (M5.SupportPolynomial.ofSupport S).coeff 0 = if 0 ∈ S then 1 else 0 := by
  classical
  intro S
  simp [M5.SupportPolynomial.ofSupport, Polynomial.coeff_X_pow]

theorem M5.SupportPolynomial.support_degree_bound : ∀ (S : Finset ℕ) (K : ℕ), 0 < K → (∀ e ∈ S, e < K) → (M5.SupportPolynomial.ofSupport S).natDegree < K := by
  change ∀ (S : Finset ℕ) (K : ℕ), 0 < K → (∀ e ∈ S, e < K) → (M5.SupportPolynomial.ofSupport S).natDegree < K
  intro S K hK
  induction S using Finset.induction_on with
  | empty =>
      intro hS
      simpa [M5.SupportPolynomial.ofSupport] using hK
  | @insert a S ha ih =>
      intro hS
      rw [M5.SupportPolynomial.ofSupport, Finset.sum_insert ha]
      apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      apply max_lt_iff.mpr
      constructor
      · simpa only [Polynomial.natDegree_X_pow] using hS a (Finset.mem_insert_self a S)
      · simpa only [M5.SupportPolynomial.ofSupport] using
          ih (fun e he => hS e (Finset.mem_insert_of_mem he))

theorem M5.SupportPolynomial.anchored_support_nonzero : ∀ S : Finset ℕ, 0 ∈ S → M5.SupportPolynomial.ofSupport S ≠ 0 := by
  change ∀ S : Finset ℕ, 0 ∈ S → M5.SupportPolynomial.ofSupport S ≠ 0
  intro S hS hzero
  have hcoeff := M5.SupportPolynomial.support_coeff_zero S
  simpa [hzero, hS] using hcoeff

theorem M5.SupportPolynomial.packed_polynomial_residue : ∀ (w T : ℕ) (r : Fin w → Fin T), AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple r) := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple r)
  intro w T r
  classical
  rw [M5.SupportPolynomial.packed_sum_image w T r (by apply M5.Packing.packed_value_injective)]
  unfold M5.SupportPolynomial.ofResidueTuple
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold M5.Packing.packedValue
  apply M5.SupportPolynomial.quotient_monomial_period
#print axioms M5.SupportPolynomial.packed_sum_image
#print axioms M5.SupportPolynomial.quotient_monomial_period
#print axioms M5.SupportPolynomial.packed_polynomial_residue
#print axioms M5.SupportPolynomial.support_coeff_zero
#print axioms M5.SupportPolynomial.anchored_support_nonzero
#print axioms M5.SupportPolynomial.support_degree_bound
