import M7RecipeSignatureReady
def M7RecipeSignaturePreflight.signature_properties : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.RecipeSignature.signature c).Monic ∧ M7.RecipeSignature.signature c ∣ (M6.Cyclic.modulus N)
)
def M7RecipeSignaturePreflight.pair_ideal_action : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.SignatureIdeal.pairIdeal N (M7.Supports.polynomial (M7.Action.act g c).1) (M7.Supports.polynomial (M7.Action.act g c).2) = (M7.SignatureIdeal.pairIdeal N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)).map (M7.QuotientAuto.substitution g.unit)
)
def M7RecipeSignaturePreflight.action_signature : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.RecipeSignature.signature (M7.Action.act g c) = M7.SignatureTau.sourceTau g.unit (M7.RecipeSignature.signature c)
)
def M7RecipeSignaturePreflight.tau_degree : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ (M6.Cyclic.modulus N) → (M7.SignatureTau.tau u F).natDegree = F.natDegree
)
def M7RecipeSignaturePreflight.action_signature_degree : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, (M7.RecipeSignature.signature (M7.Action.act g c)).natDegree = (M7.RecipeSignature.signature c).natDegree
)
def M7RecipeSignaturePreflight.translation_invariant : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ E : M6.Cyclic.BinaryPolynomial → Prop, M7.ActualFactorized.TranslationInvariant (N := N) (M7.RecipeSignature.region (N := N) E)
)
def M7RecipeSignaturePreflight.outer_source_signature : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ u : M7.ActualFactorized.Outer N, M7.RecipeSignature.signature (M7.ActualFactorized.outerImage c u) = M7.SignatureTau.sourceTau u.1 (M7.RecipeSignature.signature c)
)
def M7RecipeSignaturePreflight.sector_meets_iff : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ E : M6.Cyclic.BinaryPolynomial → Prop, ((∃ g : M7.Action.Record N, E (M7.RecipeSignature.signature (M7.Action.act g c))) ↔ ∃ u : (ZMod N)ˣ, E (M7.SignatureTau.sourceTau u (M7.RecipeSignature.signature c)))
)
def M7RecipeSignaturePreflight.source_orbit_quotient : Prop := (
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ (E : M6.Cyclic.BinaryPolynomial → Prop) (L R : Finset (ZMod N) → Prop), M7.RecipeSignature.sourceCount c E L R = M7.ActualOrbit.distinctCount c (fun y => E (M7.RecipeSignature.signature y) ∧ L y.1 ∧ R y.2) ∧ M7.ActualFactorized.stabilizerNumerator c ∣ M7.RecipeSignature.sourceNumerator c E L R
)
