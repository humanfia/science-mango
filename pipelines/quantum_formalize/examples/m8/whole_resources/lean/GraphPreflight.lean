import M8WholeResources
def M8.WholeTarget.elementary_bounds : Prop := ∀ (N : ℕ) [NeZero N], M8.WholeResources.setupWork N ≤ 21000*(N+1)^3 ∧ M8.WholeResources.transformWork N ≤ 96*(N+1)^3 ∧ M8.WholeResources.undoWork N ≤ 160*(N+1)^3
def M8.WholeTarget.original_preprocess_bound : Prop := ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.WholeResources.originalWork c ≤ 180*(N+1)^3
def M8.WholeTarget.selected_span : Prop := ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M6.ActualTransfer.span (M7.Supports.polynomial (M8.Discovery.transformed c choice).1) (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) ≤ M8.Cutoff.limit N
def M8.WholeTarget.projection : Prop := ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).outcome = M8.Solver.run c
def M8.WholeTarget.charge_length : Prop := ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).charges.length ≤ 6
def M8.WholeTarget.single_calls : Prop := ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).discoveryCalls ≤ 1 ∧ (M8.WholeResources.run c).optimizerCalls ≤ (M8.WholeResources.run c).discoveryCalls
def M8.WholeTarget.noLogical_early : Prop := ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.originalF c = 1 → (M8.WholeResources.run c).charges = [M8.WholeResources.setupWork N,M8.WholeResources.originalWork c] ∧ (M8.WholeResources.run c).discoveryCalls = 0 ∧ (M8.WholeResources.run c).optimizerCalls = 0
def M8.WholeTarget.indexed_work_bound : Prop := ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M8.WholeResources.indexedWork c ≤ 225000*(N+1)^6
