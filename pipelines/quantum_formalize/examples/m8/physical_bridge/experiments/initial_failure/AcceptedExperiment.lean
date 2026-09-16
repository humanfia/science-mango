import M8PhysicalBridge

theorem M8.PhysicalBridge.pointwise_optimizer : ∀ (N : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N) (g : M7.Action.Record N), ∀ w : ℕ, M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.Anchored (M7.Action.act g c) → M6.Final.PointwiseCorrect N (M7.Supports.polynomial (M7.Action.act g c).1) (M7.Supports.polynomial (M7.Action.act g c).2) := by
  intro N inst c g w hv ha
  rcases hv with ⟨hA, hB, hc⟩
  rcases ha with ⟨haA, haB⟩
  have hcards : (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w := by
    first
    | solve_by_elim [M7.Action.support_cards]
    | simpa [hA, hB] using M7.Action.support_cards N g c
    | simpa [hA, hB] using M7.Action.support_cards N c g
  exact M7.ClosedSolve.closed_pointwise N w (M7.Action.act g c)
    hcards.1 hcards.2 haA haB
    ((M7.Connectivity.connected_action N g c).mpr hc)

theorem M8.PhysicalBridge.signature_transport_degree : ∀ (N : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N) (g : M7.Action.Record N), (M8.PhysicalBridge.signature (M7.Action.act g c)).natDegree = (M8.PhysicalBridge.signature c).natDegree := by
  intro N inst c g
  change (M7.RecipeSignature.signature (M7.Action.act g c)).natDegree = (M7.RecipeSignature.signature c).natDegree
  exact M7.RecipeSignature.action_signature_degree N c g

theorem M8.PhysicalBridge.noLogical : ∀ (N : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N) (g : M7.Action.Record N), ∀ w : ℕ, M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.Anchored (M7.Action.act g c) → (M8.PhysicalBridge.solve (M7.Action.act g c) = none ↔ M8.PhysicalBridge.signature c = 1) := by
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
#print axioms M8.PhysicalBridge.pointwise_optimizer
#print axioms M8.PhysicalBridge.signature_transport_degree
#print axioms M8.PhysicalBridge.noLogical
