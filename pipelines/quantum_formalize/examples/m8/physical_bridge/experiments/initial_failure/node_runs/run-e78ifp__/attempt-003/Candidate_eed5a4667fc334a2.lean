import FrozenTarget_eed5a4667fc334a2
theorem M8.PhysicalBridge.minimum_original_witness : QuantumHarnessFrozenTarget := by
  intro N inst c g w hv ha hsig
  classical
  have hn := M8.PhysicalBridge.noLogical N c g w hv ha
  cases hs : M8.PhysicalBridge.solve (M7.Action.act g c) with
  | none => exact False.elim (hsig (hn.mp hs))
  | some result =>
    rcases result with ⟨d, v, k⟩
    have hc := (M7.Connectivity.connected_action N g c).mpr hv.2.2
    have hcards : (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w := by
      first
      | solve_by_elim [M7.Action.support_cards, hv.1, hv.2.1]
      | simpa [hv.1, hv.2.1] using M7.Action.support_cards N g c
      | simpa [hv.1, hv.2.1] using M7.Action.support_cards N c g
    have hgcd := (M7.Connectivity.anchored_gcd N
      (M7.Action.act g c).1 (M7.Action.act g c).2 ha.1 ha.2).mp hc
    have ht := M7.Transport.actual_witness N w (M7.Action.inverse g)
      (M7.Action.act g c) d k v hcards.1 hcards.2 ha.1 ha.2 hgcd hs
    simp only [M7.Action.act_inverse] at ht
    refine ⟨d, v, k, hs, ht.1, ht.2.1, ht.2.2.1, ?_, ht.2.2.2.2.2⟩
    have hd := ht.1
    first
    | solve
        simp only [M7.Transport.distance, M6.Flatten.common_quantum_distance] at hd
        rw [M6.Pinned.distance_spec] at hd
        simpa [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX] using hd.2
    | solve
        simp only [M7.Transport.distance, M6.CSSDistance.common_quantum_distance] at hd
        rw [M6.Pinned.distance_spec] at hd
        simpa [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX] using hd.2
    | solve
        simp only [M7.Transport.distance, M6.Final.common_quantum_distance] at hd
        rw [M6.Pinned.distance_spec] at hd
        simpa [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX] using hd.2
    | solve
        simp only [M7.Transport.distance, M6.Pinned.common_quantum_distance] at hd
        rw [M6.Pinned.distance_spec] at hd
        simpa [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX] using hd.2
    | solve
        unfold M7.Transport.distance at hd
        rw [M6.Pinned.distance_spec] at hd
        simpa [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX] using hd.2
