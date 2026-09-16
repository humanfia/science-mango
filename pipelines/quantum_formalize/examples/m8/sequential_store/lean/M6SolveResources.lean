import M6ActualTransfer
import M6PinnedAccepted
import M6QueryResources
import M6Euclid
namespace M6.ActualTransfer
noncomputable def actualDistanceWork (N : ℕ) (a b : BP) : ℕ :=
  M6.Transfer.distanceWork (span a b) N (M6.Euclid.preprocessBitCost N a b (M6.Cyclic.modulus N))
noncomputable def actualWitnessWork (N : ℕ) (a b : BP) (k : ℕ) : ℕ :=
  M6.Transfer.witnessWork (span a b) N (M6.Euclid.preprocessBitCost N a b (M6.Cyclic.modulus N)) k
end M6.ActualTransfer
