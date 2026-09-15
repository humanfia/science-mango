import M7PrefixBits

theorem M7.PrefixBits.base : ∀ (N : ℕ), 0 < N → ∀ p : List Bool, M7.PrefixCompleted.Base N (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p) := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, M7.PrefixCompleted.Base N (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p)
  intro N hN p
  classical
  have hs (o : ℕ) : M7.PrefixBits.selected N o p ⊆ Finset.range N := by
    intro x hx
    simp only [M7.PrefixBits.selected, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
    apply Finset.mem_range.mpr
    rcases hx with rfl | ⟨j, ⟨hj, _⟩, rfl⟩
    · exact hN
    · omega
  have hu (o : ℕ) : M7.PrefixBits.undecided N o p ⊆ Finset.range N := by
    intro x hx
    simp only [M7.PrefixBits.undecided, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hx
    rcases hx with ⟨j, ⟨hj, _⟩, rfl⟩
    apply Finset.mem_range.mpr
    omega
  have hz (o : ℕ) : 0 ∈ M7.PrefixBits.selected N o p := by
    simp [M7.PrefixBits.selected]
  have hd (o : ℕ) : Disjoint (M7.PrefixBits.selected N o p) (M7.PrefixBits.undecided N o p) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [M7.PrefixBits.selected, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
    simp only [M7.PrefixBits.undecided, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hy
    rcases hy with ⟨k, ⟨hk, hku⟩, hke⟩
    rcases hx with hx | ⟨j, ⟨hj, hjd, hjb⟩, hje⟩
    · omega
    · omega
  have hs0 := hs 0
  have hs1 := hs (N - 1)
  have hu0 := hu 0
  have hu1 := hu (N - 1)
  have hz0 := hz 0
  have hz1 := hz (N - 1)
  have hd0 := hd 0
  have hd1 := hd (N - 1)
  unfold M7.PrefixCompleted.Base
  simp only [M7.PrefixBits.A, M7.PrefixBits.B, M7.PrefixBits.WA, M7.PrefixBits.WB]
  aesop

theorem M7.PrefixBits.leaf_undecided : ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅ := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅
  intro N hN p hp
  unfold M7.PrefixBits.depth at hp
  unfold M7.PrefixBits.WA M7.PrefixBits.WB M7.PrefixBits.undecided
  constructor <;>
    (apply Finset.ext
     intro x
     constructor
     · intro hx
       rcases Finset.mem_image.mp hx with ⟨j, hj, heq⟩
       rcases Finset.mem_filter.mp hj with ⟨hj, hlen⟩
       have hj' := Finset.mem_range.mp hj
       omega
     · intro hx
       simp at hx)

theorem M7.PrefixBits.root : ∀ (N : ℕ), 0 < N → M7.PrefixBits.A N [] = {0} ∧ M7.PrefixBits.B N [] = {0} ∧ M7.PrefixBits.WA N [] = Finset.range N \ {0} ∧ M7.PrefixBits.WB N [] = Finset.range N \ {0} := by
  intro N hN
  have hu (offset : ℕ) : M7.PrefixBits.undecided N offset [] = Finset.range N \ {0} := by
    apply Finset.ext
    intro x
    simp only [M7.PrefixBits.undecided, List.length_nil, Nat.zero_le,
      Finset.filter_true, Finset.mem_image, Finset.mem_range,
      Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      constructor <;> omega
    · rintro ⟨hx, hx0⟩
      refine ⟨x - 1, ?_, ?_⟩ <;> omega
  refine ⟨?_, ?_, hu 0, hu (N - 1)⟩
  · simp [M7.PrefixBits.A, M7.PrefixBits.selected]
  · simp [M7.PrefixBits.B, M7.PrefixBits.selected]

theorem M7.PrefixBits.count_card : ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), M7.PrefixSector.ValidSector N E → M7.PrefixBits.count N w E p = (M7.PrefixBits.completed N w E p).card := by
  change ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), M7.PrefixSector.ValidSector N E → M7.PrefixBits.count N w E p = (M7.PrefixBits.completed N w E p).card
  intro N hN w E p hE
  exact M7.PrefixCompleted.count_completed N w E (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p) hN hE (M7.PrefixBits.base N hN p)

theorem M7.PrefixBits.leaf_singleton : ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length = M7.PrefixBits.depth N → M7.PrefixBits.completed N w E p ⊆ {(M7.PrefixBits.A N p, M7.PrefixBits.B N p)} := by
  change ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length = M7.PrefixBits.depth N → M7.PrefixBits.completed N w E p ⊆ {(M7.PrefixBits.A N p, M7.PrefixBits.B N p)}
  intro N hN w E p hp
  classical
  obtain ⟨hWA, hWB⟩ := M7.PrefixBits.leaf_undecided N hN p hp
  intro x hx
  unfold M7.PrefixBits.completed at hx
  rw [hWA, hWB] at hx
  have h := ((M7.PrefixCompleted.completed_membership N w E
    (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) ∅ ∅
    (by simp) (by simp) x).mp hx).1
  simp only [M7.PrefixCompleted.Within, Finset.union_empty] at h
  apply Finset.mem_singleton.mpr
  apply Prod.ext
  · apply Finset.Subset.antisymm <;> tauto
  · apply Finset.Subset.antisymm <;> tauto
#print axioms M7.PrefixBits.base
#print axioms M7.PrefixBits.count_card
#print axioms M7.PrefixBits.leaf_undecided
#print axioms M7.PrefixBits.leaf_singleton
#print axioms M7.PrefixBits.root
