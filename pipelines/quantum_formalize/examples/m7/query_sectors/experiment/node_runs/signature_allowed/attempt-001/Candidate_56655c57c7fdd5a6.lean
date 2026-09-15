import FrozenTarget_56655c57c7fdd5a6
theorem M7.QuerySectors.signature_allowed : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (q : M7.DefaultQuery.Query) (c : M7.Action.Recipe N), M7.DefaultQuery.signature c ∈ M7.QuerySectors.effective N q ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature c)
  intro N inst q c
  classical
  have hp : (M7.DefaultQuery.signature c).Monic ∧ M7.DefaultQuery.signature c ∣ M6.Cyclic.modulus N := by
    simpa [M7.DefaultQuery.signature, M7.RecipeSignature.signature] using M7.RecipeSignature.signature_properties N c
  have hm : M7.DefaultQuery.signature c ∈ M7.QuerySectors.allSectors N :=
    M7.QuerySectors.all_complete N _ hp.1 hp.2
  cases hs : q.signatures with
  | none => simp [M7.QuerySectors.effective, M7.DefaultQuery.allows, hs, hm]
  | some E => simp [M7.QuerySectors.effective, M7.DefaultQuery.allows, hs]
