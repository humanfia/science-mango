import FrozenTarget_6a580608622374e1
theorem M8.PhysicalBridge.minimum_original_witness : QuantumHarnessFrozenTarget := by
  intro N inst c g w hv ha hs
  classical
  have hn := M8.PhysicalBridge.noLogical N c g w hv ha
  cases he : M8.PhysicalBridge.solve (M7.Action.act g c) with
  | none => exact False.elim (hs (hn.mp he))
  | some result =>
    rcases result with ⟨d, v, k⟩
    have hcards : (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w := by
      rcases hv with ⟨hA, hB, hc⟩
      first
      | solve_by_elim [M7.Action.support_cards]
      | simpa [hA, hB] using M7.Action.support_cards N g c
      | simpa [hA, hB] using M7.Action.support_cards N c g
    have hc := (M7.Connectivity.connected_action N g c).mpr hv.2.2
    have hgcd := (M7.Connectivity.anchored_gcd N
      (M7.Action.act g c).1 (M7.Action.act g c).2 ha.1 ha.2).mp hc
    have hw := M7.Transport.actual_witness N w (M7.Action.inverse g)
      (M7.Action.act g c) d k v hcards.1 hcards.2 ha.1 ha.2 hgcd he
    simp only [M7.Action.act_inverse] at hw
    refine ⟨d, v, k, he, hw.1, hw.2.1, hw.2.2.1, ?_, hw.2.2.2.2.2⟩
    have hd := hw.1
    have hspec := M6.Pinned.distance_spec (2*N) (M7.Transport.LX c)
    simp only [M7.Transport.distance, M6.Final.quantumDistance,
      M6.Flatten.common_quantum_distance, M7.Domain.coefficients_indicator] at hd
    first
    | rw [M6.Pinned.distance_spec] at hd
      simpa only [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX] at hd ⊢
      aesop
    | simp only [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX] at hspec ⊢
      aesop
