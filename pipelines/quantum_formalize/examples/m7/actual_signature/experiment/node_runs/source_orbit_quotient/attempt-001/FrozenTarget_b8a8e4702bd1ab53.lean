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

theorem M7.RecipeSignature.action_signature : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g c) = M7.SignatureTau.sourceTau g.unit (M7.RecipeSignature.signature c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g c) = M7.SignatureTau.sourceTau g.unit (M7.RecipeSignature.signature c)
  intro N inst c g
  rw [M7.SignatureTau.source_tau_equal N]
  obtain ⟨hm, hd⟩ := M7.RecipeSignature.signature_properties N (M7.Action.act g c)
  obtain ⟨htm, htd⟩ := M7.SignatureTau.tau_properties N g.unit (M7.RecipeSignature.signature c)
  apply (M7.SignatureIdeal.monic_injective N _ _ hm htm hd htd).mp
  rw [M7.SignatureTau.tau_principal N]
  simpa only [M7.SignatureIdeal.full_signature_ideal, M7.RecipeSignature.signature] using M7.RecipeSignature.pair_ideal_action N c g

theorem M7.RecipeSignature.outer_source_signature : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ u : M7.ActualFactorized.Outer N, M7.RecipeSignature.signature (M7.ActualFactorized.outerImage c u) = M7.SignatureTau.sourceTau u.1 (M7.RecipeSignature.signature c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ u : M7.ActualFactorized.Outer N, M7.RecipeSignature.signature (M7.ActualFactorized.outerImage c u) = M7.SignatureTau.sourceTau u.1 (M7.RecipeSignature.signature c)
  intro N inst c u
  simpa only [M7.ActualFactorized.outerImage] using
    (M7.RecipeSignature.action_signature N c
      { unit := u.1, exchange := u.2, leftShift := 0, rightShift := 0 })

theorem M7.RecipeSignature.translation_invariant : ∀ (N : ℕ) [NeZero N], ∀ E : M6.Cyclic.BinaryPolynomial → Prop, M7.ActualFactorized.TranslationInvariant (N := N) (M7.RecipeSignature.region (N := N) E) := by
  change ∀ (N : ℕ) [NeZero N], ∀ E : M6.Cyclic.BinaryPolynomial → Prop, M7.ActualFactorized.TranslationInvariant (N := N) (M7.RecipeSignature.region E)
  intro N inst E c s t
  obtain ⟨hm, hd⟩ := M7.RecipeSignature.signature_properties N c
  have h := M7.RecipeSignature.action_signature N c (M7.Action.translate s t)
  change M7.RecipeSignature.signature (M7.Action.act (M7.Action.translate s t) c) = M7.SignatureTau.sourceTau (1 : (ZMod N)ˣ) (M7.RecipeSignature.signature c) at h
  rw [M7.SignatureTau.source_tau_equal N, M7.SignatureTau.tau_one N _ hm hd] at h
  simp only [M7.RecipeSignature.region, h]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ (E : M6.Cyclic.BinaryPolynomial → Prop) (L R : Finset (ZMod N) → Prop), M7.RecipeSignature.sourceCount c E L R = M7.ActualOrbit.distinctCount c (fun y => E (M7.RecipeSignature.signature y) ∧ L y.1 ∧ R y.2) ∧ M7.ActualFactorized.stabilizerNumerator c ∣ M7.RecipeSignature.sourceNumerator c E L R
