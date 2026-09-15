import FrozenTarget_5f4b2b313cb5fd77
theorem M5.FeasibleSource.same_support_infinite_progression : QuantumHarnessFrozenTarget := by
  intro w T r s F hw hT hr hs hg hF
  obtain ⟨A, hAc, hBc, hA0, hB0, hAr, hBr, hG, hSig⟩ :=
    M5.BoundedConstruction.bounded_connected_construction w T r s hw hT hr hs hg
  obtain ⟨hEpos, hEbound, hEdiv⟩ :=
    M5.PhysicalOrder.period_control A (M5.Packing.packedSupport s) w T hw hT hA0 hB0 hBr
  obtain ⟨j0, hcut, hbirth⟩ :=
    M5.Lift.bounded_source_order w T
      (M5.PhysicalOrder.supportPeriod A (M5.Packing.packedSupport s))
      hw hT hEpos hEbound
  refine ⟨A, T + j0 * M5.PhysicalOrder.supportPeriod A (M5.Packing.packedSupport s),
    M5.PhysicalOrder.supportPeriod A (M5.Packing.packedSupport s), hEpos, hbirth, ?_⟩
  intro j
  have hcut' : M5.packingCutoff w T ≤
      T + (j0 + j) * M5.PhysicalOrder.supportPeriod A (M5.Packing.packedSupport s) := by
    rw [Nat.add_mul, ← Nat.add_assoc]
    exact le_trans hcut (Nat.le_add_right _ _)
  have hreal := M5.PhysicalOrder.literal_progression
    A (M5.Packing.packedSupport s) w T F hw hT hAc hBc hA0 hB0 hAr hBr hG
    (hSig.trans hF) (j0 + j) hcut'
  simpa only [Nat.add_mul, Nat.add_assoc] using hreal
