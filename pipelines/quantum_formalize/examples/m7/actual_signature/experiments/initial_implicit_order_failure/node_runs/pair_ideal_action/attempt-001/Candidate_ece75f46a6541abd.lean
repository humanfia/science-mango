import FrozenTarget_ece75f46a6541abd
theorem M7.RecipeSignature.pair_ideal_action : QuantumHarnessFrozenTarget := by
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
