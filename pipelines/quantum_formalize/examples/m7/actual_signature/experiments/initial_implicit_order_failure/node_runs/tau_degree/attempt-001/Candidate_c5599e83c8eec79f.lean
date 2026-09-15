import FrozenTarget_c5599e83c8eec79f
theorem M7.RecipeSignature.tau_degree : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst u F hF hdiv
  obtain ⟨hτ, hτdiv⟩ := M7.SignatureTau.tau_properties N u F
  exact (M7.QuotientDegree.degree_invariant N F (M7.SignatureTau.tau u F)
    hF hτ hdiv hτdiv (M7.SignatureTau.equiv u)
    (M7.SignatureTau.tau_principal N u F).symm).symm
