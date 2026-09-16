import M8SolverAccepted
import M8P3FamilyAccepted
import M8P4GcdAccepted
import M8MixedFamilyAccepted
import M8MixedNonproductAccepted
import M8DiagonalPolynomialAccepted
import M8CoverageFoundationAccepted
namespace M8.Coverage
noncomputable def deltaPair (N : ℕ) : M6.Pinned.Vector (2*N) :=
  M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0)
def PhysicalTwo {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Prop :=
  M7.Transport.distance c = some 2 ∧ deltaPair N ∈ M7.Transport.LX c ∧
  M6.Pinned.weight (deltaPair N) = 2 ∧ ∀ u ∈ M7.Transport.LX c, 2 ≤ M6.Pinned.weight u
def Recognized {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Prop :=
  ∃ (d : ℕ) (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (k : ℕ),
    M8.Solver.run c = M8.Solver.Outcome.recognized (M8.PhysicalBridge.signature c) d z choice k
def RecognizedTwo {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Prop :=
  ∃ (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (k : ℕ),
    M8.Solver.run c = M8.Solver.Outcome.recognized (M8.PhysicalBridge.signature c) 2 z choice k
end M8.Coverage
