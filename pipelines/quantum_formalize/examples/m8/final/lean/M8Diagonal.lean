import M6ActualCSSAccepted

namespace M8.Diagonal
/-- Actual CSS distance of the diagonal convolution code. -/
noncomputable def distance (N : ℕ) [NeZero N] (p : M6.Physical.Block N) : Option ℕ :=
  M6.CSS.quantumDistance (M6.Spaces.boundaryWords N p p)
    (M6.Spaces.cycleWords N p p)
    (M6.Character.subspaceWords (M6.Spaces.D N p p))
    (M6.Character.dualWords (M6.Spaces.B N p p))
/-- Algebraic intermediate obligation, discharged for each explicit source family. -/
def DeltaNotImage (N : ℕ) [NeZero N] (p : M6.Physical.Block N) : Prop :=
  ¬ ∃ h : M6.Physical.Block N, M6.Physical.conv N p h = M6.Physical.delta N 0
end M8.Diagonal
