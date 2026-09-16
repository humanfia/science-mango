import FrozenTarget_e36a2b2cdd9ce378
theorem M8.PhysicalBridge.minimum_original_witness : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c g w hv ha hsig
  have hne : M8.PhysicalBridge.solve (M7.Action.act g c) ≠ none := by
    intro h
    exact hsig ((M8.PhysicalBridge.noLogical N c g w hv ha).mp h)
  cases hs : M8.PhysicalBridge.solve (M7.Action.act g c) with
  | none => exact False.elim (hne hs)
  | some result =>
    rcases result with ⟨d, v, k⟩
    rcases hv with ⟨hA, hB, hc⟩
    rcases ha with ⟨haA, haB⟩
    have hcards : (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w := by
      first
      | solve_by_elim [M7.Action.support_cards]
      | simpa [hA, hB] using M7.Action.support_cards N g c
      | simpa [hA, hB] using M7.Action.support_cards N c g
    have hconn := (M7.Connectivity.connected_action N g c).mpr hc
    have hgcd := (M7.Connectivity.anchored_gcd N _ _ haA haB).mp hconn
    have hw := M7.Transport.actual_witness N w (M7.Action.inverse g)
      (M7.Action.act g c) d k v hcards.1 hcards.2 haA haB hgcd hs
    simp only [M7.Action.act_inverse] at hw
    rcases hw with ⟨hd, hmem, hweight, hz, hzw, hk⟩
    refine ⟨d, v, k, rfl, hd, hmem, hweight, ?_, hk⟩
    intro u hu
    have hd' := hd
    change M6.Final.quantumDistance N (M7.Supports.polynomial c.1)
      (M7.Supports.polynomial c.2) = some d at hd'
    unfold M6.Final.quantumDistance at hd'
    change u ∈ M6.Spaces.cycleWords N (M7.Supports.indicator c.1)
      (M7.Supports.indicator c.2) \ M6.Spaces.boundaryWords N
      (M7.Supports.indicator c.1) (M7.Supports.indicator c.2) at hu
    first
    | solve
      | simp only [M6.Pinned.distance_spec, M7.Domain.coefficients_indicator] at hd'
        aesop
    | solve
      | simp only [M6.Pinned.common_quantum_distance, M6.Pinned.distance_spec,
          M7.Domain.coefficients_indicator] at hd'
        aesop
    | solve
      | simp only [M6.CSSDistance.common_quantum_distance, M6.Pinned.distance_spec,
          M7.Domain.coefficients_indicator] at hd'
        aesop
    | solve
      | simp only [M6.CSS.common_quantum_distance, M6.Pinned.distance_spec,
          M7.Domain.coefficients_indicator] at hd'
        aesop
    | solve
      | simp only [M6.Final.common_quantum_distance, M6.Pinned.distance_spec,
          M7.Domain.coefficients_indicator] at hd'
        aesop
    | solve
      | simp only [M6.Spaces.common_quantum_distance, M6.Pinned.distance_spec,
          M7.Domain.coefficients_indicator] at hd'
        aesop
