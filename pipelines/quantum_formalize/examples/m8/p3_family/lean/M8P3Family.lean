import M8PhysicalBridgeAccepted
import M8CoverageFoundationAccepted
import M8CutoffAccepted
import M8AnchorAccepted

namespace M8.P3Family
noncomputable def support (N : ℕ) : Finset (ZMod N) := {0,1,2}
noncomputable def recipe (N : ℕ) : M7.Action.Recipe N := (support N,support N)
noncomputable def polynomial : M6.Cyclic.BinaryPolynomial := 1+Polynomial.X+Polynomial.X^2
end M8.P3Family
