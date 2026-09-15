import FrozenTarget_1d67c880c7fe1f3a
theorem M5.FeasibleSource.bounded_source : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro w T r s F hw hT hr hs hg hF
  obtain ⟨A, hAc, hBc, hA0, hB0, hAr, hBr, hG, hSig⟩ :=
    M5.BoundedConstruction.bounded_connected_construction w T r s hw hT hr hs hg
  refine ⟨A, ?_⟩
  exact M5.PhysicalOrder.bounded_order A (M5.Packing.packedSupport s) w T F
    hw hT hAc hBc hA0 hB0 hAr hBr hG (hSig.trans hF)
