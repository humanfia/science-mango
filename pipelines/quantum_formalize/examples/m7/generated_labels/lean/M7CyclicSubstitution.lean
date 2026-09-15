import M6Cyclic

namespace M7.CyclicSubstitution
noncomputable def rho (N : ℕ) : M6.Cyclic.CycleRing N :=
  AdjoinRoot.root (M6.Cyclic.modulus N)
noncomputable def point {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) : M6.Cyclic.CycleRing N :=
  rho N ^ (u : ZMod N).val
def RootCondition {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) : Prop :=
  (M6.Cyclic.modulus N).eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (point u) = 0
noncomputable def hom {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (h : RootCondition u) :
    M6.Cyclic.CycleRing N →+* M6.Cyclic.CycleRing N :=
  AdjoinRoot.lift (AdjoinRoot.of (M6.Cyclic.modulus N)) (point u) h
end M7.CyclicSubstitution
