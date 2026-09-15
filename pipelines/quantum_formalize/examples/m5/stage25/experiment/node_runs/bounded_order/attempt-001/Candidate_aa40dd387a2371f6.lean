import FrozenTarget_aa40dd387a2371f6
theorem M5.PhysicalOrder.bounded_order : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro A B w T F hw hT hAcard hBcard hA hB hAbound hBbound hg hF
  have hp := M5.PhysicalOrder.period_control A B w T hw hT hA hB hBbound
  obtain ⟨j, hjcut, hjbound⟩ := M5.Lift.bounded_source_order w T (M5.PhysicalOrder.supportPeriod A B) hw hT hp.1 hp.2.1
  refine ⟨T + j * M5.PhysicalOrder.supportPeriod A B, hjbound, ?_⟩
  exact M5.PhysicalOrder.literal_progression A B w T F hw hT hAcard hBcard hA hB hAbound hBbound hg hF j hjcut
