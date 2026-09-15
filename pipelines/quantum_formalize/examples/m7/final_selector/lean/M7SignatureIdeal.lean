import M6CyclicAccepted

namespace M7.SignatureIdeal
noncomputable def principal (N : ℕ) (F : M6.Cyclic.BinaryPolynomial) : Ideal (M6.Cyclic.CycleRing N) :=
  Ideal.span ({M6.Cyclic.image N F} : Set (M6.Cyclic.CycleRing N))
noncomputable def pairIdeal (N : ℕ) (a b : M6.Cyclic.BinaryPolynomial) : Ideal (M6.Cyclic.CycleRing N) :=
  Ideal.span ({M6.Cyclic.image N a, M6.Cyclic.image N b} : Set (M6.Cyclic.CycleRing N))
end M7.SignatureIdeal
