import M7ActualOrbitAccepted

namespace M7.OrbitResidual
open scoped BigOperators
noncomputable def covered {N : ℕ} [NeZero N] (bases : Finset (M7.Action.Recipe N)) : Finset (M7.Action.Recipe N) := by
  classical
  exact bases.biUnion M7.ActualOrbit.orbit
noncomputable def remaining {N : ℕ} [NeZero N] (C bases : Finset (M7.Action.Recipe N)) : Finset (M7.Action.Recipe N) := by
  classical
  exact C \ covered bases
def Separated {N : ℕ} [NeZero N] (bases : Finset (M7.Action.Recipe N)) : Prop :=
  ∀ c ∈ bases, ∀ d ∈ bases, c ≠ d → Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit d)
noncomputable def subtraction {N : ℕ} [NeZero N] (C bases : Finset (M7.Action.Recipe N)) : ℤ := by
  classical
  exact (C.card : ℤ) - ∑ c ∈ bases, (M7.ActualOrbit.distinctCount c (fun y => y ∈ C) : ℤ)
end M7.OrbitResidual
