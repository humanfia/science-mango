import FrozenTarget_227a41b9a645825c
theorem M6.Euclid.normalized_gcd : QuantumHarnessFrozenTarget := by
  change ∀ p q : M6.Euclid.BP, EuclideanDomain.gcd q p = GCDMonoid.gcd p q
  intro p q
  classical
  have hab : EuclideanDomain.gcd q p ∣ GCDMonoid.gcd p q := by
    apply _root_.dvd_gcd
    · exact EuclideanDomain.gcd_dvd_right q p
    · exact EuclideanDomain.gcd_dvd_left q p
  have hba : GCDMonoid.gcd p q ∣ EuclideanDomain.gcd q p := by
    apply EuclideanDomain.dvd_gcd
    · exact _root_.gcd_dvd_right p q
    · exact _root_.gcd_dvd_left p q
  apply dvd_antisymm_of_normalize_eq <;>
    first
    | exact (M6.Euclid.binary_normalization _).2
    | exact normalize_gcd p q
    | exact hab
    | exact hba
