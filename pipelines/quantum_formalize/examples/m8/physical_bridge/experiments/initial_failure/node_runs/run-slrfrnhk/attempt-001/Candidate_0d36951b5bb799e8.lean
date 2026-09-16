import FrozenTarget_0d36951b5bb799e8
theorem M8.PhysicalBridge.signature_transport_degree : QuantumHarnessFrozenTarget := by
  intro N inst c g
  change (M7.RecipeSignature.signature (M7.Action.act g c)).natDegree = (M7.RecipeSignature.signature c).natDegree
  exact M7.RecipeSignature.action_signature_degree N c g
