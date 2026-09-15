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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length = M7.PrefixBits.depth N → M7.PrefixBits.completed N w E p ⊆ {(M7.PrefixBits.A N p, M7.PrefixBits.B N p)}
