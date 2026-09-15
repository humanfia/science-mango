import M6FinalReady

theorem M6.Final.recipe_correct : M6.Final.RecipeCorrect := by
  exact ⟨M6.RecipeIsometries.translation_isometry, M6.RecipeIsometries.multiplier_isometry, M6.RecipeIsometries.exchange_isometry⟩

theorem M6.Final.storage_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.StorageCorrect N a b := by
  intro N inst a b h
  exact M6.ActualTransfer.actual_solve_storage N a b h.2.2.2.2.1
def QuantumHarnessFrozenTarget : Prop :=
  M6.Final.OriginalM6
