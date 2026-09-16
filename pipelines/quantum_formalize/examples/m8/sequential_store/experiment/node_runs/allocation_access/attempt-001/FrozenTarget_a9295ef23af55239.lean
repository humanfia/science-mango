import M8SequentialStore


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (mem : List Bool), mem.length = M8.SequentialStore.slots N → ∀ (i : Fin (M8.SequentialStore.slots N)) (bit : Bool), (M8.TaggedStore.read (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem)).1 = mem[i.val]? ∧ (M8.TaggedStore.write (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem)).1 = M8.TaggedStore.packFrom 0 (mem.set i.val bit) ∧ (M8.TaggedStore.read (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem)).2 ≤ M8.SequentialStore.accessCharge N ∧ (M8.TaggedStore.write (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem)).2 ≤ M8.SequentialStore.accessCharge N
