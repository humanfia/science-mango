import M6FinalReady

theorem M6.Final.recipe_correct : M6.Final.RecipeCorrect := by
  exact ⟨M6.RecipeIsometries.translation_isometry, M6.RecipeIsometries.multiplier_isometry, M6.RecipeIsometries.exchange_isometry⟩

theorem M6.Final.storage_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.StorageCorrect N a b := by
  intro N inst a b h
  exact M6.ActualTransfer.actual_solve_storage N a b h.2.2.2.2.1

theorem M6.Final.original_m6 : M6.Final.OriginalM6 := by
  change M6.Final.OriginalM6
  refine ⟨?_, M6.Final.fixed_span_correct, M6.Final.recipe_correct, M6.Final.zero_span_correct⟩
  intro N inst a b h
  exact ⟨M6.Final.counting_correct N a b h, M6.Final.parameters_correct N a b h, M6.Final.answer_correct N a b h, M6.Final.execution_correct N a b h, M6.Final.storage_correct N a b h⟩
#print axioms M6.Final.recipe_correct
#print axioms M6.Final.storage_correct
#print axioms M6.Final.original_m6
