import M8SolverAccepted
import M8RawParametersAccepted
import M8SequentialResourcesAccepted
import M8SequentialStoreAccepted
import M8WholeResourcesAccepted
import M8CoverageAccepted
import M8ExclusionConclusionsAccepted

namespace M8.Final

/-- Exact original-scope obligations copied from accepted frozen targets. -/
def Algorithm : Prop :=
  (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.outputF (M8.Solver.run c) = M8.PhysicalBridge.signature c) ∧
  (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Solver.run c = M8.Solver.Outcome.noLogical (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c = 1) ∧ (M8.Solver.run c = M8.Solver.Outcome.noLogical (M8.PhysicalBridge.signature c) ↔ M7.Transport.distance c = none)) ∧
  (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Solver.run c = M8.Solver.Outcome.unrecognized (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c ≠ 1 ∧ M8.Cutoff.limit N < M8.OrbitSpan.value c)) ∧
  (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ((∃ (d : ℕ) (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (k : ℕ), M8.Solver.run c = M8.Solver.Outcome.recognized (M8.PhysicalBridge.signature c) d z choice k) ↔ M8.PhysicalBridge.signature c ≠ 1 ∧ M8.OrbitSpan.value c ≤ M8.Cutoff.limit N)) ∧
  (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ∀ (F : M8.Solver.BP) (d : ℕ) (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (k : ℕ), M8.Solver.run c = M8.Solver.Outcome.recognized F d z choice k → F = M8.PhysicalBridge.signature c ∧ M8.Discovery.discover c = some choice ∧ M7.Transport.distance c = some d ∧ z ∈ M7.Transport.LX c ∧ M6.Pinned.weight z = d ∧ (∀ u ∈ M7.Transport.LX c, d ≤ M6.Pinned.weight u) ∧ k ≤ 2*N ∧ (∀ j : M8.Discovery.Choice N, M8.Discovery.Good c j → M8.Discovery.key choice ≤ M8.Discovery.key j) ∧ M6.Final.encodedQubits N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) = 2*F.natDegree)

/-- Exact original-scope obligations copied from accepted frozen targets. -/
def PhysicalParameters : Prop :=
  (∀ (N w : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → (M7.Transport.distance c = none ↔ M8.PhysicalBridge.signature c = 1) ∧ (M7.Transport.LX c = ∅ ↔ M8.PhysicalBridge.signature c = 1)) ∧
  (∀ (N w : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → M6.Final.encodedQubits N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) = 2*(M8.PhysicalBridge.signature c).natDegree)

/-- Exact original-scope obligations copied from accepted frozen targets. -/
def Resources : Prop :=
  (∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M8.SequentialStore.prefixCharge (M8.SequentialResources.primitiveCharge N) (M8.WholeResources.run c).charges = M8.WholeResources.indexedWork c * M8.SequentialResources.primitiveCharge N) ∧
  (∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (w : ℕ), 0 < w → M8.PhysicalBridge.Valid w c → M8.SequentialResources.sequentialCharge c ≤ 6000000000000*(N+1)^12)

/-- Exact original-scope obligations copied from accepted frozen targets. -/
def Storage : Prop :=
  (∀ (N : ℕ) [NeZero N], ∀ (mem : List Bool), mem.length = M8.SequentialStore.slots N → ∀ (i : Fin (M8.SequentialStore.slots N)) (bit : Bool), (M8.TaggedStore.read (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem)).1 = mem[i.val]? ∧ (M8.TaggedStore.write (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem)).1 = M8.TaggedStore.packFrom 0 (mem.set i.val bit) ∧ (M8.TaggedStore.read (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem)).2 ≤ M8.SequentialStore.accessCharge N ∧ (M8.TaggedStore.write (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem)).2 ≤ M8.SequentialStore.accessCharge N) ∧
  (∀ (N : ℕ) [NeZero N], ∀ mem : List Bool, mem.length = M8.SequentialStore.slots N → M8.SequentialStore.storeSpace N mem ≤ 2000000*(N+1)^4)

/-- Exact original-scope obligations copied from accepted frozen targets. -/
def CostProjection : Prop :=
  (∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).outcome = M8.Solver.run c)

/-- Exact original-scope obligations copied from accepted frozen targets. -/
def AdmittedFamilies : Prop :=
  (∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M8.Coverage.PhysicalTwo (M8.P3Family.recipe N)) ∧
  (∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M8.PhysicalBridge.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial ∧ M8.Coverage.RecognizedTwo (M8.P3Family.recipe N) ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.P3Family.recipe N)))) ∧
  (∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.Coverage.PhysicalTwo (M8.P4Family.recipe N)) ∧
  (∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.Coverage.RecognizedTwo (M8.P4Family.recipe N) ∧ M8.PhysicalBridge.signature (M8.P4Family.recipe N) = (if 4 ∣ N then M8.P4Family.polynomial else (Polynomial.X+1)^2) ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.P4Family.recipe N)))) ∧
  (∀ (N : ℕ) [NeZero N], 8 ≤ N → ∀ v m : ℕ, 0 < v → Odd m → N = 2^v*m → M8.PhysicalBridge.signature (M8.P4Family.recipe N) = (Polynomial.X+1)^(min 3 (2^v)) ∧ M8.Coverage.RecognizedTwo (M8.P4Family.recipe N)) ∧
  (∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Coverage.Recognized (M8.MixedFamily.recipe N) ∧ M8.PhysicalBridge.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.MixedFamily.recipe N))) ∧ (∀ g : M7.Action.Record N, ¬ M8.MixedNonproduct.Product (M7.Action.act g (M8.MixedFamily.recipe N))))

/-- Exact original-scope obligations copied from accepted frozen targets. -/
def ExcludedFamilies : Prop :=
  (∀ (N : ℕ) [NeZero N] (w : ℕ) (c : M7.Action.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.signature c ≠ 1 → (∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g c)) → M8.Solver.run c = M8.Solver.Outcome.unrecognized (M8.PhysicalBridge.signature c)) ∧
  (∀ (N : ℕ) [NeZero N] (w : ℕ) (c : M7.Action.Recipe N), M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.signature c ≠ 1 → M8.Cutoff.limit N + 1 < w → M8.Solver.run c = M8.Solver.Outcome.unrecognized (M8.PhysicalBridge.signature c)) ∧
  (∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → ∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g (M8.AntipodalFamily.recipe N))) ∧
  (∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → M7.Transport.distance (M8.AntipodalFamily.recipe N) = some 2) ∧
  (∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → M8.Solver.run (M8.AntipodalFamily.recipe N) = M8.Solver.Outcome.unrecognized (M8.AntipodalFamily.polynomial N)) ∧
  (∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → (M8.PhysicalBridge.Valid 4 (M8.AntipodalFamily.recipe N) ∧ M8.PhysicalBridge.signature (M8.AntipodalFamily.recipe N) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(N/2+1) ∧ M8.Solver.run (M8.AntipodalFamily.recipe N) = M8.Solver.Outcome.unrecognized ((Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(N/2+1)) ∧ M7.Transport.distance (M8.AntipodalFamily.recipe N) = some 2))

/-- Revised accepted original M8: exact algorithm, physical output, fixed sequential resources, and explicit admitted/excluded families. -/
def OriginalM8 : Prop :=
  Algorithm ∧ PhysicalParameters ∧ Resources ∧ Storage ∧ CostProjection ∧ AdmittedFamilies ∧ ExcludedFamilies
end M8.Final
