import M7FinalResources

theorem M7.FinalResources.comparison : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ q : M7.DefaultQuery.Query, M7.FinalResources.comparisonCharge q (M7.GeneratedFamily.family N w E) ≤ 2 * ((M7.GeneratedFamily.size N w E) * (2*Nat.totient N*N^2))^2 * (q.objectives.length+1) * M7.FinalResources.objectiveBits q (M7.GeneratedFamily.family N w E) := by
  intro N w inst E hw hwN hE q
  have h := (M7.StreamingCost.scan_bound (M7.GeneratedFamily.size N w E) N q (M7.GeneratedFamily.family N w E)).2
  rw [(M7.StreamingCost.record_cardinality N).2] at h
  have hcharge := Nat.mul_le_mul_right (M7.FinalResources.objectiveBits q (M7.GeneratedFamily.family N w E)) (Nat.mul_le_mul_right (2 * (q.objectives.length + 1)) h)
  simpa [M7.FinalResources.comparisonCharge, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcharge

theorem M7.FinalResources.generation : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → (M7.CompactGeneration.generate (N := N) w E).finalBases.card = M7.GeneratedFamily.size N w E ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.root + (M7.GenerationCalls.generateMeasured (N := N) w E).2.children = (1 + M7.GeneratedFamily.size N w E * (2*M7.PrefixBits.depth N+1)) ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.orbitCounts ≤ M7.GeneratedFamily.size N w E*(1 + M7.GeneratedFamily.size N w E * (2*M7.PrefixBits.depth N+1)) := by
  intro N w inst E hw hwN hE
  dsimp only [M7.GeneratedFamily.size]
  have hc := M7.CompactCorrectness.generate_card N w E hE
  obtain ⟨_, hcount, horbits⟩ := M7.GenerationCalls.generate_count N w E
  refine ⟨hc, hcount, ?_⟩
  simpa only [hc] using horbits

theorem M7.FinalResources.label_work : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → M7.FinalResources.distanceWork N w E ≤ 50000*N^3 * (∑ i : Fin (M7.GeneratedFamily.size N w E), 4^(M6.ActualTransfer.span (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2))) ∧ ∀ i : Fin (M7.GeneratedFamily.size N w E), M6.ActualTransfer.actualSolveStorage N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) ≤ 16384*N^2*2^(M6.ActualTransfer.span (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2)) := by
  intro N w inst E hw hwN hE
  classical
  have hp := M7.GeneratedLabels.pointwise N w E hw hwN hE
  constructor
  · unfold M7.FinalResources.distanceWork
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := hp i
    simp only [M6.Final.PointwiseCorrect, M6.Final.ExecutionCorrect,
      M6.Final.StorageCorrect] at h
    aesop
  · intro i
    have h := hp i
    simp only [M6.Final.PointwiseCorrect, M6.Final.ExecutionCorrect,
      M6.Final.StorageCorrect] at h
    aesop

theorem M7.FinalResources.storage : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → M7.CompactStorage.storedCoreBits N (M7.GeneratedFamily.size N w E) ≤ 16*(M7.GeneratedFamily.size N w E)*N ∧ M7.CompactStorage.storedWithTablesBits N (M7.GeneratedFamily.size N w E) ≤ 16*(M7.GeneratedFamily.size N w E)*N + 2*(M7.GeneratedFamily.size N w E)*Nat.totient N*N := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → M7.CompactStorage.storedCoreBits N (M7.GeneratedFamily.size N w E) ≤ 16*(M7.GeneratedFamily.size N w E)*N ∧ M7.CompactStorage.storedWithTablesBits N (M7.GeneratedFamily.size N w E) ≤ 16*(M7.GeneratedFamily.size N w E)*N + 2*(M7.GeneratedFamily.size N w E)*Nat.totient N*N
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N w inst E hw hwN hE
  exact (M7.CompactStorage.storage_bounds N (M7.GeneratedFamily.size N w E)).2.2.2

theorem M7.FinalResources.witness_work : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ (d k : Fin (M7.GeneratedFamily.size N w E) → ℕ) (v : Fin (M7.GeneratedFamily.size N w E) → M6.Pinned.Vector (2*N)), (∀ i, M6.ActualTransfer.solve N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) = some (d i,v i,k i)) → (∑ i : Fin (M7.GeneratedFamily.size N w E), M6.ActualTransfer.actualWitnessWork N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) (k i)) ≤ 200000*N^4 * (∑ i : Fin (M7.GeneratedFamily.size N w E), 4^(M6.ActualTransfer.span (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2))) := by
  classical
  intro N w inst E hw hwN hE d k v hsolve
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hp := M7.GeneratedLabels.pointwise N w E hw hwN hE i
  have hs := hsolve i
  simp only [M6.Final.PointwiseCorrect, M6.Final.ExecutionCorrect,
    M6.Final.StorageCorrect] at hp
  aesop

theorem M7.FinalResources.word_width : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∀ (x : M7.GlobalQuery.Index H N) (j : Fin q.objectives.length), 1 + (M7.GlobalQuery.objective q bases x j).natAbs.size ≤ M7.FinalResources.objectiveBits q bases := by
  classical
  intro H N inst q bases x j
  unfold M7.FinalResources.objectiveBits
  apply Nat.add_le_add_left
  exact le_trans
    (Finset.le_sup (f := fun k : Fin q.objectives.length =>
      (M7.GlobalQuery.objective q bases x k).natAbs.size) (Finset.mem_univ j))
    (Finset.le_sup (f := fun y : M7.GlobalQuery.Index H N =>
      Finset.univ.sup (fun k : Fin q.objectives.length =>
        (M7.GlobalQuery.objective q bases y k).natAbs.size)) (Finset.mem_univ x))
#print axioms M7.FinalResources.comparison
#print axioms M7.FinalResources.generation
#print axioms M7.FinalResources.label_work
#print axioms M7.FinalResources.storage
#print axioms M7.FinalResources.witness_work
#print axioms M7.FinalResources.word_width
