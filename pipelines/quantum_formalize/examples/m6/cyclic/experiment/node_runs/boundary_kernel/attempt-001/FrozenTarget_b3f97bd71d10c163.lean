import M6Cyclic

theorem M6.Cyclic.signature_bezout : ∀ a b M : M6.Cyclic.BinaryPolynomial, ∃ p q r : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M = p*a + q*b + r*M := by
  intro a b M
  classical
  unfold M6.Cyclic.signature
  first
  | change ∃ p q r, EuclideanDomain.gcd (EuclideanDomain.gcd a b) M = p*a + q*b + r*M
    refine ⟨EuclideanDomain.gcdA (EuclideanDomain.gcd a b) M * EuclideanDomain.gcdA a b, EuclideanDomain.gcdA (EuclideanDomain.gcd a b) M * EuclideanDomain.gcdB a b, EuclideanDomain.gcdB (EuclideanDomain.gcd a b) M, ?_⟩
    calc
      _ = (EuclideanDomain.gcd a b) * EuclideanDomain.gcdA (EuclideanDomain.gcd a b) M + M * EuclideanDomain.gcdB (EuclideanDomain.gcd a b) M := EuclideanDomain.gcd_eq_gcd_ab _ _
      _ = _ := by
        rw [EuclideanDomain.gcd_eq_gcd_ab a b]
        ring
  | change ∃ p q r, EuclideanDomain.gcd a (EuclideanDomain.gcd b M) = p*a + q*b + r*M
    refine ⟨EuclideanDomain.gcdA a (EuclideanDomain.gcd b M), EuclideanDomain.gcdB a (EuclideanDomain.gcd b M) * EuclideanDomain.gcdA b M, EuclideanDomain.gcdB a (EuclideanDomain.gcd b M) * EuclideanDomain.gcdB b M, ?_⟩
    calc
      _ = a * EuclideanDomain.gcdA a (EuclideanDomain.gcd b M) + (EuclideanDomain.gcd b M) * EuclideanDomain.gcdB a (EuclideanDomain.gcd b M) := EuclideanDomain.gcd_eq_gcd_ab _ _
      _ = _ := by
        rw [EuclideanDomain.gcd_eq_gcd_ab b M]
        ring

theorem M6.Cyclic.signature_divides : ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M := by
  change ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M
  intro a b M
  unfold M6.Cyclic.signature
  exact ⟨dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _), dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _), EuclideanDomain.gcd_dvd_right _ _⟩

theorem M6.Cyclic.kernel_divisibility : ∀ a b M h : M6.Cyclic.BinaryPolynomial, (M ∣ a*h ∧ M ∣ b*h) ↔ M ∣ M6.Cyclic.signature a b M * h := by
  change ∀ a b M h : M6.Cyclic.BinaryPolynomial, (M ∣ a*h ∧ M ∣ b*h) ↔ M ∣ M6.Cyclic.signature a b M * h
  intro a b M h
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨p, q, r, hs⟩ := M6.Cyclic.signature_bezout a b M
    refine ⟨p*x + q*y + r*h, ?_⟩
    calc
      M6.Cyclic.signature a b M * h = (p*a + q*b + r*M)*h := congrArg (fun z => z*h) hs
      _ = p*(a*h) + q*(b*h) + M*(r*h) := by ring
      _ = M*(p*x + q*y + r*h) := by rw [hx, hy]; ring
  · rintro ⟨t, ht⟩
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, _⟩ := M6.Cyclic.signature_divides a b M
    constructor
    · refine ⟨t*u, ?_⟩
      calc
        a*h = (M6.Cyclic.signature a b M * u)*h := congrArg (fun z => z*h) hu
        _ = (M6.Cyclic.signature a b M * h)*u := by ring
        _ = (M*t)*u := congrArg (fun z => z*u) ht
        _ = M*(t*u) := by ring
    · refine ⟨t*v, ?_⟩
      calc
        b*h = (M6.Cyclic.signature a b M * v)*h := congrArg (fun z => z*h) hv
        _ = (M6.Cyclic.signature a b M * h)*v := by ring
        _ = (M*t)*v := congrArg (fun z => z*v) ht
        _ = M*(t*v) := by ring
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (a b h : M6.Cyclic.BinaryPolynomial), M6.Cyclic.boundary N a b (M6.Cyclic.image N h) = (0,0) ↔ M6.Cyclic.modulus N ∣ M6.Cyclic.signature a b (M6.Cyclic.modulus N) * h
