import FrozenTarget_d34a5ab5ad5ed30c
theorem M6.Euclid.normalized_gcd : QuantumHarnessFrozenTarget := by
  change ∀ p q : M6.Euclid.BP, EuclideanDomain.gcd q p = GCDMonoid.gcd p q
  intro p q
  apply dvd_antisymm_of_normalize_eq
    (M6.Euclid.binary_normalization (EuclideanDomain.gcd q p)).2
    (M6.Euclid.binary_normalization (GCDMonoid.gcd p q)).2
  · exact GCDMonoid.dvd_gcd
      (EuclideanDomain.gcd_dvd_right q p)
      (EuclideanDomain.gcd_dvd_left q p)
  · exact EuclideanDomain.dvd_gcd
      (GCDMonoid.gcd_dvd_right p q)
      (GCDMonoid.gcd_dvd_left p q)
