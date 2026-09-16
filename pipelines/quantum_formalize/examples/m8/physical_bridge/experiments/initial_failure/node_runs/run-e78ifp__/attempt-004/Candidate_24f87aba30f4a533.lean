import FrozenTarget_24f87aba30f4a533
theorem M8.PhysicalBridge.minimum_original_witness : QuantumHarnessFrozenTarget := by
  intro N inst c g w hv ha hsig
  have hn := M8.PhysicalBridge.noLogical N c g w hv ha
  cases hs : M8.PhysicalBridge.solve (M7.Action.act g c) with
  | none => exact False.elim (hsig (hn.mp hs))
  | some result =>
    rcases result with ⟨d, v, k⟩
    have hc := (M7.Connectivity.connected_action N g c).mpr hv.2.2
    have hcards : (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w := by
      first
      | solve_by_elim [M7.Action.support_cards]
      | simpa [hv.1, hv.2.1] using M7.Action.support_cards N g c
      | simpa [hv.1, hv.2.1] using M7.Action.support_cards N c g
    have hgcd := (M7.Connectivity.anchored_gcd N
      (M7.Action.act g c).1 (M7.Action.act g c).2 ha.1 ha.2).mp hc
    have ht := M7.Transport.actual_witness N w (M7.Action.inverse g)
      (M7.Action.act g c) d k v hcards.1 hcards.2 ha.1 ha.2 hgcd hs
    simp only [M7.Action.act_inverse] at ht
    refine ⟨d, v, k, rfl, ht.1, ht.2.1, ht.2.2.1, ?_, ht.2.2.2.2.2⟩
    have hd := ht.1
    unfold M7.Transport.distance at hd
    first
    | rw [M6.Flatten.common_quantum_distance] at hd
    | rw [M6.CSSDistance.common_quantum_distance] at hd
    | skip
    intro u hu
    change u ∈ M7.Transport.CX c \ M7.Transport.BX c at hu
    unfold M7.Transport.CX M7.Transport.BX at hu
    first
    | solve_by_elim [M6.Pinned.distance_spec]
    | rw [M6.Pinned.distance_spec] at hd
      aesop
    | have hspec := M6.Pinned.distance_spec _ _ hd
      aesop
    | have hspec := M6.Pinned.distance_spec _ hd
      aesop
