import FrozenTarget_17a24fe6021ac915
theorem M7.CanonicalClasses.insert_normalized : QuantumHarnessFrozenTarget := by
  classical
  intro N inst bases y h
  change ∀ c ∈ insert (M7.CanonicalOuter.canonical y) bases, M7.CanonicalOuter.canonical c = c
  intro c hc
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact M7.CanonicalClasses.idempotent N y
  · exact h c hc
