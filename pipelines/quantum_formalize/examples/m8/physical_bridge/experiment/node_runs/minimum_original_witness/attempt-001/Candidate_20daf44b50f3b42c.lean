import FrozenTarget_20daf44b50f3b42c
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
    have hqd : M7.Transport.distance c = M6.Pinned.distance (M7.Transport.LX c) := by
      unfold M7.Transport.distance M6.Final.quantumDistance M6.Final.BX M6.Final.CX M6.Final.BZ M6.Final.CZ
      simp only [M7.Domain.coefficients_indicator]
      exact M6.ActualCSS.common_quantum_distance N _ _
    change M7.Transport.distance c = some d at hd
    rw [hqd] at hd
    exact ((M6.Pinned.distance_spec (2*N) (M7.Transport.LX c)).2 d).mp hd |>.2
