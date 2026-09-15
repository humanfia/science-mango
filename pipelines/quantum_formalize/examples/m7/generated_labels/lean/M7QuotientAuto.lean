import M7CyclicSubstitutionAccepted

namespace M7.QuotientAuto
noncomputable def substitution {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    M6.Cyclic.CycleRing N →+* M6.Cyclic.CycleRing N :=
  M7.CyclicSubstitution.hom u (M7.CyclicSubstitution.point_root N u)
end M7.QuotientAuto
