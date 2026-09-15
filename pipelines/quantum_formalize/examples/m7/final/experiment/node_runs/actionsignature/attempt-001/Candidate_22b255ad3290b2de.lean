import FrozenTarget_22b255ad3290b2de
theorem M7.Final.actionsignature : QuantumHarnessFrozenTarget := by
  change M7.Final.ActionSignature
  unfold M7.Final.ActionSignature
  exact ⟨M7.Action.record_card,
    M7.Action.order_one_records,
    M7.RecipeSignature.signature_properties,
    M7.RecipeSignature.action_signature,
    M7.RecipeSignature.tau_degree,
    M7.RecipeSignature.source_orbit_quotient,
    M7.ActualFactorized.stabilizer_numerator,
    M7.ActualFactorized.positive_denominator,
    M7.ActualFactorized.exact_orbit_quotient,
    M7.PrefixOrbit.residual_card,
    M7.PrefixOrbit.residual_positive⟩
