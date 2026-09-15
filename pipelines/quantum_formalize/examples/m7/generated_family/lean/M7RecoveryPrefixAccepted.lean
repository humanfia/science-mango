import M7PrefixBitsAccepted
import M7RecoveryPrefix
import M7ResiduePrefixAccepted

theorem M7.RecoveryPrefix.completed_partition : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length < M7.PrefixBits.depth N → M7.RecoveryPrefix.completed N w E p = M7.RecoveryPrefix.completed N w E (p ++ [false]) ∪ M7.RecoveryPrefix.completed N w E (p ++ [true]) ∧ Disjoint (M7.RecoveryPrefix.completed N w E (p ++ [false])) (M7.RecoveryPrefix.completed N w E (p ++ [true])) := by
  classical
  intro N inst w E p hp
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hpart, hdisj⟩ := M7.PrefixBits.completed_partition N hN w E p hp
  have bounds (q : List Bool) (x : Finset ℕ × Finset ℕ)
      (hx : x ∈ M7.PrefixBits.completed N w E q) :
      x.1 ⊆ Finset.range N ∧ x.2 ⊆ Finset.range N := by
    exact M7.ResiduePrefix.completed_bounds N w E
      (M7.PrefixBits.A N q) (M7.PrefixBits.B N q)
      (M7.PrefixBits.WA N q) (M7.PrefixBits.WB N q)
      (M7.PrefixBits.base N hN q) x hx
  constructor
  · change (M7.PrefixBits.completed N w E p).image (M7.ResiduePrefix.decodePair N) =
      (M7.PrefixBits.completed N w E (p ++ [false])).image (M7.ResiduePrefix.decodePair N) ∪
      (M7.PrefixBits.completed N w E (p ++ [true])).image (M7.ResiduePrefix.decodePair N)
    rw [hpart, Finset.image_union]
  · change Disjoint
      ((M7.PrefixBits.completed N w E (p ++ [false])).image (M7.ResiduePrefix.decodePair N))
      ((M7.PrefixBits.completed N w E (p ++ [true])).image (M7.ResiduePrefix.decodePair N))
    apply Finset.disjoint_left.mpr
    intro z hz₀ hz₁
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz₀
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz₁
    obtain ⟨hx₁, hx₂⟩ := bounds (p ++ [false]) x hx
    obtain ⟨hy₁, hy₂⟩ := bounds (p ++ [true]) y hy
    have hxy : x = y := M7.ResiduePrefix.decode_injective N x y
      hx₁ hx₂ hy₁ hy₂ (hxz.trans hyz.symm)
    subst y
    exact Finset.disjoint_left.mp hdisj hx hy

theorem M7.RecoveryPrefix.completed_subroot : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), M7.RecoveryPrefix.completed N w E p ⊆ M7.RecoveryPrefix.completed N w E [] := by
  intro N inst w E p
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hp := M7.PrefixBits.base N hN p
  have hr := M7.PrefixBits.base N hN []
  intro x hx
  change x ∈ M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p) at hx
  change x ∈ M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N []) (M7.PrefixBits.B N []) (M7.PrefixBits.WA N []) (M7.PrefixBits.WB N [])
  obtain ⟨hw, hv⟩ := (M7.ResiduePrefix.completed_membership N w E _ _ _ _ hp x).mp hx
  apply (M7.ResiduePrefix.completed_membership N w E _ _ _ _ hr x).mpr
  refine ⟨?_, hv⟩
  obtain ⟨hA, hB, hWA, hWB⟩ := M7.PrefixBits.root N hN
  rw [hA, hB, hWA, hWB]
  simp only [M7.PrefixCompleted.Base, M7.PrefixCompleted.Within, Finset.subset_iff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hp hw ⊢
  grind

theorem M7.RecoveryPrefix.leaf_singleton : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length = M7.PrefixBits.depth N → M7.RecoveryPrefix.completed N w E p ⊆ {M7.RecoveryPrefix.leaf N p} := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length = M7.PrefixBits.depth N → M7.RecoveryPrefix.completed N w E p ⊆ {M7.RecoveryPrefix.leaf N p}
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  classical
  intro N inst w E p hp x hx
  change x ∈ (M7.PrefixBits.completed N w E p).image (M7.ResiduePrefix.decodePair N) at hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  have hyLeaf := M7.PrefixBits.leaf_singleton N (Nat.pos_of_ne_zero (NeZero.ne N)) w E p hp hy
  have hyEq := Finset.mem_singleton.mp hyLeaf
  subst y
  exact Finset.mem_singleton.mpr rfl
#print axioms M7.RecoveryPrefix.completed_partition
#print axioms M7.RecoveryPrefix.completed_subroot
#print axioms M7.RecoveryPrefix.leaf_singleton
