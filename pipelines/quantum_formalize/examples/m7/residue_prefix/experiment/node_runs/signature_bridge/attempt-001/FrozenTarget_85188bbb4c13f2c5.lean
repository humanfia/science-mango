import M7ResiduePrefix

theorem M7.ResiduePrefix.polynomial_bridge : ∀ (N : ℕ) [NeZero N], ∀ A : Finset (ZMod N), M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode A) = M7.Supports.polynomial A := by
  classical
  intro N inst A
  unfold M7.ResiduePrefix.encode M7.Supports.natSupport M5.SupportPolynomial.ofSupport M7.Supports.polynomial
  rw [Finset.sum_image]
  intro a ha b hb hab
  have h := congrArg (fun k : ℕ => (k : ZMod N)) hab
  simpa only [ZMod.natCast_zmod_val] using h
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A B : Finset (ZMod N), M5.completeSignature (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode A)) (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode B)) N = M6.Cyclic.signature (M7.Supports.polynomial A) (M7.Supports.polynomial B) (M6.Cyclic.modulus N)
