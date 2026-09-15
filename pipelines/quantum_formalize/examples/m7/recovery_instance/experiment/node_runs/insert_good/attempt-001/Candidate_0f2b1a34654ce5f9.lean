import FrozenTarget_0f2b1a34654ce5f9
theorem M7.RecoveryInstance.insert_good : QuantumHarnessFrozenTarget := by
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
