import FrozenTarget_1f13f3cba2c3d853
theorem M8.PhysicalBridge.noLogical : QuantumHarnessFrozenTarget := by
  intro N inst c g w hv ha
  have hp := M8.PhysicalBridge.pointwise_optimizer N c g w hv ha
  have hanswer : M6.Final.AnswerCorrect N
      (M7.Supports.polynomial (M7.Action.act g c).1)
      (M7.Supports.polynomial (M7.Action.act g c).2) := by
    unfold M6.Final.PointwiseCorrect at hp
    tauto
  have hnone := hanswer.1
  change (M8.PhysicalBridge.solve (M7.Action.act g c) = none ↔
    (M8.PhysicalBridge.signature (M7.Action.act g c)).natDegree = 0) at hnone
  rw [M8.PhysicalBridge.signature_transport_degree N c g] at hnone
  have hm : (M8.PhysicalBridge.signature c).Monic :=
    (M7.RecipeSignature.signature_properties N c).1
  exact hnone.trans hm.natDegree_eq_zero
