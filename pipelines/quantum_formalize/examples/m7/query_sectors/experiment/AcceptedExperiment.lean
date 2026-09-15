import M7QuerySectors

theorem M7.QuerySectors.all_complete : ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → F ∈ M7.QuerySectors.allSectors N := by
  change ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → F ∈ M7.QuerySectors.allSectors N
  intro N inst F hF hdiv
  classical
  have hmod : M6.Cyclic.modulus N ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : M6.Cyclic.BinaryPolynomial => p.coeff 0) hz
    simpa [M6.Cyclic.modulus, NeZero.ne N, (NeZero.ne N).symm] using hc
  have hle : UniqueFactorizationMonoid.normalizedFactors F ≤ UniqueFactorizationMonoid.normalizedFactors (M6.Cyclic.modulus N) :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hF.ne_zero hmod).mp hdiv
  have hprod : (UniqueFactorizationMonoid.normalizedFactors F).prod = F := by
    simpa [hF.leadingCoeff] using Polynomial.leadingCoeff_mul_prod_normalizedFactors F
  simp only [M7.QuerySectors.allSectors, Multiset.mem_toFinset, Finset.mem_image, Multiset.mem_powerset]
  exact ⟨UniqueFactorizationMonoid.normalizedFactors F, hle, hprod⟩

theorem M7.QuerySectors.all_sound : ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N → F.Monic ∧ F ∣ M6.Cyclic.modulus N := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N → F.Monic ∧ F ∣ M6.Cyclic.modulus N
  intro N inst F hF
  simp only [M7.QuerySectors.allSectors, Finset.mem_image, Multiset.mem_toFinset,
    Multiset.mem_map, Multiset.mem_powerset] at hF
  rcases hF with ⟨s, hs, rfl⟩
  have hmod : M6.Cyclic.modulus N ≠ 0 := (M7.SignatureTau.modulus_monic N).ne_zero
  have hd : s.prod ∣ M6.Cyclic.modulus N :=
    (Multiset.prod_dvd_prod_of_le hs).trans
      (UniqueFactorizationMonoid.prod_normalizedFactors hmod).dvd
  refine ⟨?_, hd⟩
  apply M7.SignatureTau.binary_monic
  intro hz
  rw [hz] at hd
  exact hmod (zero_dvd_iff.mp hd)

theorem M7.QuerySectors.all_membership : ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N ↔ F.Monic ∧ F ∣ M6.Cyclic.modulus N := by
  change ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N ↔ F.Monic ∧ F ∣ M6.Cyclic.modulus N
  intro N inst F
  constructor
  · exact M7.QuerySectors.all_sound N F
  · intro h
    exact M7.QuerySectors.all_complete N F h.1 h.2

theorem M7.QuerySectors.effective_valid : ∀ (N : ℕ) [NeZero N], ∀ q : M7.DefaultQuery.Query, M7.DefaultQuery.valid N q → M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q) := by
  change ∀ (N : ℕ) [NeZero N], ∀ q : M7.DefaultQuery.Query, M7.DefaultQuery.valid N q → M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q)
  intro N inst q hq
  change ∀ F ∈ M7.QuerySectors.effective N q, F.Monic ∧ F ∣ M6.Cyclic.modulus N
  cases hs : q.signatures with
  | none =>
      simp only [M7.QuerySectors.effective, hs]
      intro F hF
      exact (M7.QuerySectors.all_membership N F).mp hF
  | some E =>
      simp only [M7.QuerySectors.effective, hs]
      simpa only [M7.DefaultQuery.valid, hs] using hq

theorem M7.QuerySectors.signature_allowed : ∀ (N : ℕ) [NeZero N], ∀ (q : M7.DefaultQuery.Query) (c : M7.Action.Recipe N), M7.DefaultQuery.signature c ∈ M7.QuerySectors.effective N q ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (q : M7.DefaultQuery.Query) (c : M7.Action.Recipe N), M7.DefaultQuery.signature c ∈ M7.QuerySectors.effective N q ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature c)
  intro N inst q c
  classical
  have hp : (M7.DefaultQuery.signature c).Monic ∧ M7.DefaultQuery.signature c ∣ M6.Cyclic.modulus N := by
    simpa [M7.DefaultQuery.signature, M7.Domain.signature, M7.RecipeSignature.signature] using M7.RecipeSignature.signature_properties N c
  have hm := M7.QuerySectors.all_complete N (M7.DefaultQuery.signature c) hp.1 hp.2
  cases hq : q.signatures with
  | none => simp [M7.QuerySectors.effective, M7.DefaultQuery.allows, hq, hm]
  | some s => simp [M7.QuerySectors.effective, M7.DefaultQuery.allows, hq]
#print axioms M7.QuerySectors.all_complete
#print axioms M7.QuerySectors.all_sound
#print axioms M7.QuerySectors.all_membership
#print axioms M7.QuerySectors.effective_valid
#print axioms M7.QuerySectors.signature_allowed
