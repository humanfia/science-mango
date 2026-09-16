import M8PhysicalBridgeAccepted
import M8CoverageFoundationAccepted
import M8CutoffAccepted
import M8AnchorAccepted

namespace M8.MixedFamily
noncomputable def left (N : ℕ) : Finset (ZMod N) := {0,1}
noncomputable def right (N : ℕ) : Finset (ZMod N) := {0,2}
noncomputable def recipe (N : ℕ) : M7.Action.Recipe N := (left N,right N)
noncomputable def a : M6.Cyclic.BinaryPolynomial := 1+Polynomial.X
noncomputable def b : M6.Cyclic.BinaryPolynomial := 1+Polynomial.X^2
end M8.MixedFamily
