import M8CutoffAccepted
import M6SolveResourcesAccepted
import M6SolveStorageAccepted
import M6WeightResourcesAccepted
import M6TransferPartialResourcesAccepted

namespace M8.OptimizerResources
noncomputable def weight (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP)
    (pins : M6.Pinned.Pins (2*N)) (character : Bool) :
    ℕ → M6.Transfer.Memory (M6.ActualTransfer.span a b) → M6.Transfer.Bit → Polynomial ℤ :=
  if character then
    M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b pins
  else M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b pins
end M8.OptimizerResources
