import M5Accepted

namespace M5.QuotientCharacter

noncomputable def coordinates (P : M5.BinaryPolynomial) (hP : P.Monic) :
    AdjoinRoot P ≃ₗ[ZMod 2] M5.Character.BinaryVector P.natDegree :=
  (AdjoinRoot.powerBasisAux' hP).equivFun

noncomputable def value (P : M5.BinaryPolynomial) (hP : P.Monic)
    (lam : M5.Character.BinaryVector P.natDegree) (z : AdjoinRoot P) : ℤ :=
  M5.Character.value lam (coordinates P hP z)

end M5.QuotientCharacter
