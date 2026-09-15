import M7AffinePolynomial

theorem M7.AffinePolynomial.rho_add_val : ∀ (N : ℕ) [NeZero N], ∀ x y : ZMod N, M7.CyclicSubstitution.rho N ^ (x+y).val = M7.CyclicSubstitution.rho N ^ x.val * M7.CyclicSubstitution.rho N ^ y.val := by
  intro N inst x y
  rw [ZMod.val_add, ← M7.CyclicSubstitution.power_mod N (x.val + y.val), pow_add]

theorem M7.AffinePolynomial.rho_mul_val : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (x : ZMod N), M7.CyclicSubstitution.rho N ^ ((u : ZMod N)*x).val = M7.CyclicSubstitution.point u ^ x.val := by
  intro N inst u x
  change M7.CyclicSubstitution.rho N ^ ((u : ZMod N) * x).val =
    (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) ^ x.val
  rw [← pow_mul, ZMod.val_mul]
  exact (M7.CyclicSubstitution.power_mod N ((u : ZMod N).val * x.val)).symm

theorem M7.AffinePolynomial.support_sum : ∀ (N : ℕ) [NeZero N], ∀ A : M7.Supports.Support N, M7.AffinePolynomial.image A = ∑ i ∈ A, M7.CyclicSubstitution.rho N ^ i.val := by
  intro N inst A
  classical
  simp [M7.AffinePolynomial.image, M7.Supports.polynomial,
    M6.Cyclic.image, M7.CyclicSubstitution.rho, map_sum,
    map_pow, AdjoinRoot.mk_X]

theorem M7.AffinePolynomial.substitution_support_sum : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (A : M7.Supports.Support N), M7.QuotientAuto.substitution u (M7.AffinePolynomial.image A) = ∑ i ∈ A, M7.CyclicSubstitution.point u ^ i.val := by
  intro N inst u A
  classical
  rw [M7.AffinePolynomial.support_sum N A]
  simp only [M7.QuotientAuto.substitution, map_sum, map_pow,
    M7.CyclicSubstitution.hom_root]

theorem M7.AffinePolynomial.image_affine : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (s : ZMod N) (A : M7.Supports.Support N), M7.AffinePolynomial.image (M7.AffinePolynomial.shifted u s A) = M7.CyclicSubstitution.rho N ^ s.val * M7.QuotientAuto.substitution u (M7.AffinePolynomial.image A) := by
  intro N inst u s A
  classical
  rw [M7.AffinePolynomial.support_sum N,
    M7.AffinePolynomial.substitution_support_sum N]
  unfold M7.AffinePolynomial.shifted
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h : M7.Action.affine u s i = s + (u : ZMod N) * i := by
      simp [M7.Action.affine, add_comm, mul_comm]
    rw [h, M7.AffinePolynomial.rho_add_val N,
      M7.AffinePolynomial.rho_mul_val N]
  · intro a ha b hb hab
    exact (M7.Action.affine_bijective N u s).injective hab
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.AffinePolynomial.image (M7.Action.act g c).1 = M7.CyclicSubstitution.rho N ^ g.leftShift.val * M7.QuotientAuto.substitution g.unit (M7.AffinePolynomial.image (if g.exchange then c.2 else c.1)) ∧ M7.AffinePolynomial.image (M7.Action.act g c).2 = M7.CyclicSubstitution.rho N ^ g.rightShift.val * M7.QuotientAuto.substitution g.unit (M7.AffinePolynomial.image (if g.exchange then c.1 else c.2))
