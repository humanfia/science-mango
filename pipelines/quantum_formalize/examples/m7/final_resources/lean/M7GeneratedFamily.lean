import M7CompactCorrectnessAccepted
import M7RawCoverageAccepted
import M7GlobalQueryAccepted

namespace M7.GeneratedFamily
noncomputable def size (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) : ℕ :=
  (M7.CompactGeneration.generate (N := N) w E).emitted.length
noncomputable def family (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) :
    M7.GlobalQuery.Family (size N w E) N :=
  fun i => ((M7.CompactGeneration.generate (N := N) w E).emitted.get i).representative
end M7.GeneratedFamily
