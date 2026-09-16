import M8SequentialResources
def M8.SequentialTarget.actual_prefix_charge : Prop := ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M8.SequentialStore.prefixCharge (M8.SequentialResources.primitiveCharge N) (M8.WholeResources.run c).charges = M8.WholeResources.indexedWork c * M8.SequentialResources.primitiveCharge N
def M8.SequentialTarget.sequential_bound : Prop := ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (w : ℕ), 0 < w → M8.PhysicalBridge.Valid w c → M8.SequentialResources.sequentialCharge c ≤ 6000000000000*(N+1)^12
