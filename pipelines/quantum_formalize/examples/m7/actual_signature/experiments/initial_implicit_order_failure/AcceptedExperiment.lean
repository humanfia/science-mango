import M7RecipeSignatureReady

theorem M7.RecipeSignature.pair_ideal_action : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.SignatureIdeal.pairIdeal N (M7.Supports.polynomial (M7.Action.act g c).1) (M7.Supports.polynomial (M7.Action.act g c).2) = (M7.SignatureIdeal.pairIdeal N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)).map (M7.QuotientAuto.substitution g.unit) := by
  intro N inst c g
  change Ideal.span ({M7.AffinePolynomial.image (M7.Action.act g c).1,
      M7.AffinePolynomial.image (M7.Action.act g c).2} : Set (M6.Cyclic.CycleRing N)) =
    (Ideal.span ({M7.AffinePolynomial.image c.1,
      M7.AffinePolynomial.image c.2} : Set (M6.Cyclic.CycleRing N))).map
        (M7.QuotientAuto.substitution g.unit)
  obtain ⟨hleft, hright⟩ := M7.AffinePolynomial.action_images N g c
  have hu := M7.AffinePolynomial.rho_power_unit N g.leftShift
  have hv := M7.AffinePolynomial.rho_power_unit N g.rightShift
  rw [hleft, hright, Ideal.map_span, Set.image_pair]
  cases he : g.exchange <;>
    simp [he, Ideal.span_insert, Ideal.span_singleton_mul_left_unit, hu, hv, sup_comm]

theorem M7.RecipeSignature.signature_properties : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.RecipeSignature.signature c).Monic ∧ M7.RecipeSignature.signature c ∣ (M6.Cyclic.modulus N) := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.RecipeSignature.signature c).Monic ∧ M7.RecipeSignature.signature c ∣ M6.Cyclic.modulus N
  intro N inst c
  have hd : M7.RecipeSignature.signature c ∣ M6.Cyclic.modulus N := by
    unfold M7.RecipeSignature.signature
    first
    | exact M6.Cyclic.signature_divides _ _ _
    | exact (M6.Cyclic.signature_divides _ _ _).2.2
    | exact (M6.Cyclic.signature_divides _ _ _).2
  refine ⟨M7.SignatureTau.binary_monic _ ?_, hd⟩
  intro hz
  have hm := (M7.SignatureTau.modulus_monic N).ne_zero
  apply hm
  simpa only [hz, zero_dvd_iff] using hd

theorem M7.RecipeSignature.tau_degree : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ (M6.Cyclic.modulus N) → (M7.SignatureTau.tau u F).natDegree = F.natDegree := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ (M6.Cyclic.modulus N) → (M7.SignatureTau.tau u F).natDegree = F.natDegree
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst u F hF hdiv
  obtain ⟨hτ, hτdiv⟩ := M7.SignatureTau.tau_properties N u F
  exact (M7.QuotientDegree.degree_invariant N F (M7.SignatureTau.tau u F)
    hF hτ hdiv hτdiv (M7.SignatureTau.equiv u)
    (M7.SignatureTau.tau_principal N u F).symm).symm

theorem M7.RecipeSignature.action_signature : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g c) = M7.SignatureTau.sourceTau g.unit (M7.RecipeSignature.signature c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g c) = M7.SignatureTau.sourceTau g.unit (M7.RecipeSignature.signature c)
  intro N inst c g
  rw [M7.SignatureTau.source_tau_equal N]
  obtain ⟨hm, hd⟩ := M7.RecipeSignature.signature_properties N (M7.Action.act g c)
  obtain ⟨htm, htd⟩ := M7.SignatureTau.tau_properties N g.unit (M7.RecipeSignature.signature c)
  apply (M7.SignatureIdeal.monic_injective N _ _ hm htm hd htd).mp
  rw [M7.SignatureTau.tau_principal N]
  simpa only [M7.SignatureIdeal.full_signature_ideal, M7.RecipeSignature.signature] using M7.RecipeSignature.pair_ideal_action N c g

theorem M7.RecipeSignature.action_signature_degree : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, (M7.RecipeSignature.signature (M7.Action.act g c)).natDegree = (M7.RecipeSignature.signature c).natDegree := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, (M7.RecipeSignature.signature (M7.Action.act g c)).natDegree = (M7.RecipeSignature.signature c).natDegree
  intro N inst c g
  rw [M7.RecipeSignature.action_signature N c g, M7.SignatureTau.source_tau_equal N]
  obtain ⟨hm, hd⟩ := M7.RecipeSignature.signature_properties N c
  exact M7.RecipeSignature.tau_degree N g.unit (M7.RecipeSignature.signature c) hm hd

theorem M7.RecipeSignature.outer_source_signature : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ u : M7.ActualFactorized.Outer N, M7.RecipeSignature.signature (M7.ActualFactorized.outerImage c u) = M7.SignatureTau.sourceTau u.1 (M7.RecipeSignature.signature c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ u : M7.ActualFactorized.Outer N, M7.RecipeSignature.signature (M7.ActualFactorized.outerImage c u) = M7.SignatureTau.sourceTau u.1 (M7.RecipeSignature.signature c)
  intro N inst c u
  simpa only [M7.ActualFactorized.outerImage] using
    (M7.RecipeSignature.action_signature N c
      { unit := u.1, exchange := u.2, leftShift := 0, rightShift := 0 })

theorem M7.RecipeSignature.sector_meets_iff : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ E : M6.Cyclic.BinaryPolynomial → Prop, ((∃ g : M7.Action.Record N, E (M7.RecipeSignature.signature (M7.Action.act g c))) ↔ ∃ u : (ZMod N)ˣ, E (M7.SignatureTau.sourceTau u (M7.RecipeSignature.signature c))) := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ E : M6.Cyclic.BinaryPolynomial → Prop, ((∃ g : M7.Action.Record N, E (M7.RecipeSignature.signature (M7.Action.act g c))) ↔ ∃ u : (ZMod N)ˣ, E (M7.SignatureTau.sourceTau u (M7.RecipeSignature.signature c)))
  intro N inst c E
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.unit, ?_⟩
    rw [M7.RecipeSignature.action_signature N c g] at hg
    exact hg
  · rintro ⟨u, hu⟩
    refine ⟨{ unit := u, exchange := false, leftShift := 0, rightShift := 0 }, ?_⟩
    rw [M7.RecipeSignature.action_signature N c]
    exact hu
#print axioms M7.RecipeSignature.pair_ideal_action
#print axioms M7.RecipeSignature.signature_properties
#print axioms M7.RecipeSignature.action_signature
#print axioms M7.RecipeSignature.outer_source_signature
#print axioms M7.RecipeSignature.sector_meets_iff
#print axioms M7.RecipeSignature.tau_degree
#print axioms M7.RecipeSignature.action_signature_degree
