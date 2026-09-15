import M7DescentTraceAccepted
import M7PrefixOrbitAccepted
import M7RecoveryInstance
import M7RecoveryPrefixAccepted

theorem M7.RecoveryInstance.count_card : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → ∀ p : List Bool, M7.RecoveryInstance.count w E bases p = (M7.RecoveryInstance.remaining w E bases p).card ∧ (M7.RecoveryInstance.count w E bases p).toNat = (M7.RecoveryInstance.remaining w E bases p).card ∧ 0 ≤ M7.RecoveryInstance.count w E bases p := by
  intro N inst w E bases hE hB p
  have h : M7.RecoveryInstance.count w E bases p = ((M7.RecoveryInstance.remaining w E bases p).card : ℤ) := by
    simpa only [M7.RecoveryInstance.count, M7.RecoveryInstance.remaining,
      M7.RecoveryPrefix.completed] using
      (M7.PrefixOrbit.residual_card N w E
        (M7.PrefixBits.A N p) (M7.PrefixBits.B N p)
        (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p)
        hE (M7.PrefixBits.base N (Nat.pos_of_ne_zero (NeZero.ne N)) p) bases
        (by first | exact hB.1 | exact hB.2)
        (by first | exact hB.1 | exact hB.2))
  refine ⟨h, ?_, ?_⟩
  · rw [h]
    simp
  · rw [h]
    exact Int.natCast_nonneg _

theorem M7.RecoveryInstance.count_partition : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → ∀ p : List Bool, p.length < M7.PrefixBits.depth N → M7.RecoveryInstance.count w E bases p = M7.RecoveryInstance.count w E bases (p ++ [false]) + M7.RecoveryInstance.count w E bases (p ++ [true]) := by
  intro N inst w E bases hE hB p hp
  classical
  rw [(M7.RecoveryInstance.count_card N w E bases hE hB p).1,
    (M7.RecoveryInstance.count_card N w E bases hE hB (p ++ [false])).1,
    (M7.RecoveryInstance.count_card N w E bases hE hB (p ++ [true])).1]
  change ((M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E p) bases).card : ℤ) =
    ((M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [false])) bases).card : ℤ) +
    ((M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [true])) bases).card : ℤ)
  have hpart := M7.RecoveryPrefix.completed_partition N w E p hp
  have hd : Disjoint
      (M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [false])) bases)
      (M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E (p ++ [true])) bases) := by
    unfold M7.OrbitResidual.remaining
    exact hpart.2.mono Finset.sdiff_subset Finset.sdiff_subset
  rw [hpart.1, M7.OrbitResidual.remaining_partition,
    Finset.card_union_of_disjoint hd, Nat.cast_add]

theorem M7.RecoveryInstance.root_zero : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → (M7.RecoveryInstance.count w E bases [] = 0 ↔ M7.RecoveryPrefix.completed N w E [] ⊆ M7.OrbitResidual.covered bases) := by
  intro N inst w E bases hE hB
  classical
  rw [(M7.RecoveryInstance.count_card N w E bases hE hB []).1]
  simp [M7.RecoveryInstance.remaining, M7.OrbitResidual.remaining,
    Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem M7.RecoveryInstance.positive_path : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → (M7.RecoveryInstance.word w E bases).length = M7.PrefixBits.depth N ∧ 0 < M7.RecoveryInstance.count w E bases (M7.RecoveryInstance.word w E bases) ∧ M7.DescentTrace.check (M7.RecoveryInstance.count w E bases) [] (M7.RecoveryInstance.path w E bases) = (true,2*M7.PrefixBits.depth N) := by
  intro N inst w E bases hE hB hpos
  refine ⟨?_, ?_, ?_⟩
  · unfold M7.RecoveryInstance.word M7.RecoveryInstance.path
    rw [M7.DescentTrace.endpoint_recover, M5.BinaryRecovery.recover_length]
    simp
  · unfold M7.RecoveryInstance.word M7.RecoveryInstance.path
    rw [M7.DescentTrace.endpoint_recover]
    apply M5.BinaryRecovery.recover_positive
    · intro q hq
      apply M7.RecoveryInstance.count_partition N w E bases hE hB q
      simpa only [List.length_nil, Nat.zero_add] using hq
    · exact hpos
  · exact M7.DescentTrace.check_trace (M7.RecoveryInstance.count w E bases) [] (M7.PrefixBits.depth N)

theorem M7.RecoveryInstance.fresh_leaf : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.RecoveryInstance.remaining w E bases [] ∧ M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.RecoveryPrefix.completed N w E (M7.RecoveryInstance.word w E bases) := by
  intro N inst w E bases hE hB hpos
  classical
  have hp := M7.RecoveryInstance.positive_path N w E bases hE hB hpos
  have hc := (M7.RecoveryInstance.count_card N w E bases hE hB (M7.RecoveryInstance.word w E bases)).1
  have hcard : 0 < (M7.RecoveryInstance.remaining w E bases (M7.RecoveryInstance.word w E bases)).card := by
    have hz := hp.2.1
    rw [hc] at hz
    exact_mod_cast hz
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
  change y ∈ M7.RecoveryPrefix.completed N w E (M7.RecoveryInstance.word w E bases) \ M7.OrbitResidual.covered bases at hy
  rcases Finset.mem_sdiff.mp hy with ⟨hyC, hyU⟩
  have hyEq : y = M7.RecoveryInstance.recoverLeaf w E bases := by
    have hs := M7.RecoveryPrefix.leaf_singleton N w E (M7.RecoveryInstance.word w E bases) hp.1 hyC
    simpa only [Finset.mem_singleton, M7.RecoveryInstance.recoverLeaf] using hs
  rw [← hyEq]
  refine ⟨?_, hyC⟩
  change y ∈ M7.RecoveryPrefix.completed N w E [] \ M7.OrbitResidual.covered bases
  exact Finset.mem_sdiff.mpr ⟨M7.RecoveryPrefix.completed_subroot N w E (M7.RecoveryInstance.word w E bases) hyC, hyU⟩

theorem M7.RecoveryInstance.insert_good : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → M7.RecoveryInstance.GoodBases w (M7.RecoveryInstance.insertedBases w E bases) ∧ M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases) ∉ bases := by
  intro N inst w E bases hE hB hpos
  classical
  have hf := (M7.RecoveryInstance.fresh_leaf N w E bases hE hB hpos).1
  change M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.RecoveryPrefix.completed N w E [] \ M7.OrbitResidual.covered bases at hf
  rcases Finset.mem_sdiff.mp hf with ⟨hc, hu⟩
  have hn : M7.CanonicalClasses.Normalized bases := by
    first | exact hB.1 | exact hB.2
  have hv : ∀ c ∈ bases, M7.PrefixOrbit.ClassValid w c := by
    first | exact hB.1 | exact hB.2
  have he : M7.PrefixOrbit.ClassValid w (M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases)) := by
    apply M7.PrefixOrbit.emitted_class_valid N w E
      (M7.PrefixBits.A N []) (M7.PrefixBits.B N [])
      (M7.PrefixBits.WA N []) (M7.PrefixBits.WB N [])
      (M7.PrefixBits.base N (Nat.pos_of_ne_zero (NeZero.ne N)) [])
    exact hc
  have hni := M7.CanonicalClasses.insert_normalized N bases (M7.RecoveryInstance.recoverLeaf w E bases) hn
  have hvi : ∀ c ∈ insert (M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases)) bases, M7.PrefixOrbit.ClassValid w c := by
    intro c hm
    rcases Finset.mem_insert.mp hm with h | h
    · subst c
      exact he
    · exact hv c h
  refine ⟨?_, M7.CanonicalClasses.fresh_representative N bases (M7.RecoveryInstance.recoverLeaf w E bases) hn hu⟩
  unfold M7.RecoveryInstance.GoodBases M7.RecoveryInstance.insertedBases
  constructor <;> first | exact hni | exact hvi

theorem M7.RecoveryInstance.strict_decrease : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → (M7.RecoveryInstance.remaining w E (M7.RecoveryInstance.insertedBases w E bases) []).card < (M7.RecoveryInstance.remaining w E bases []).card ∧ (M7.RecoveryInstance.count w E (M7.RecoveryInstance.insertedBases w E bases) []).toNat < (M7.RecoveryInstance.count w E bases []).toNat := by
  intro N inst w E bases hE hB hpos
  classical
  have hf := (M7.RecoveryInstance.fresh_leaf N w E bases hE hB hpos).1
  have hgood := (M7.RecoveryInstance.insert_good N w E bases hE hB hpos).1
  have ho : M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.ActualOrbit.orbit (M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases)) := by
    apply (M7.CanonicalClasses.orbit_membership N _ _).2
    exact (M7.CanonicalClasses.idempotent N _).symm
  have hlt : (M7.RecoveryInstance.remaining w E (M7.RecoveryInstance.insertedBases w E bases) []).card < (M7.RecoveryInstance.remaining w E bases []).card := by
    unfold M7.RecoveryInstance.remaining M7.RecoveryInstance.insertedBases
    rw [M7.OrbitResidual.insert_remaining]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hm : M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E []) bases \ M7.ActualOrbit.orbit (M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases)) := by
      rw [heq]
      exact hf
    exact (Finset.mem_sdiff.mp hm).2 ho
  refine ⟨hlt, ?_⟩
  rw [(M7.RecoveryInstance.count_card N w E (M7.RecoveryInstance.insertedBases w E bases) hE hgood []).2.1,
    (M7.RecoveryInstance.count_card N w E bases hE hB []).2.1]
  exact hlt
#print axioms M7.RecoveryInstance.count_card
#print axioms M7.RecoveryInstance.count_partition
#print axioms M7.RecoveryInstance.positive_path
#print axioms M7.RecoveryInstance.fresh_leaf
#print axioms M7.RecoveryInstance.insert_good
#print axioms M7.RecoveryInstance.root_zero
#print axioms M7.RecoveryInstance.strict_decrease
