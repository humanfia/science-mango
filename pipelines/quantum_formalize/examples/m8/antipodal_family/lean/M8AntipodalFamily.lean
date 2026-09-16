import M8PhysicalBridgeAccepted
import M8CoverageFoundationAccepted
import M8CutoffAccepted
import M8AnchorAccepted

namespace M8.AntipodalFamily
noncomputable def support (N : ℕ) : Finset (ZMod N) := {0,1,((N/2 : ℕ) : ZMod N),((N/2+1 : ℕ) : ZMod N)}
noncomputable def recipe (N : ℕ) : M7.Action.Recipe N := (support N,support N)
noncomputable def polynomial (N : ℕ) : M6.Cyclic.BinaryPolynomial := (1+Polynomial.X)*(1+Polynomial.X^(N/2))
end M8.AntipodalFamily
