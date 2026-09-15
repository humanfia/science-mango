import M7QuotientAuto

theorem M7.QuotientAuto.substitution_root : ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.QuotientAuto.substitution u (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.point u := by
  intro N inst u
  exact M7.CyclicSubstitution.hom_root N u (M7.CyclicSubstitution.point_root N u)

theorem M7.QuotientAuto.substitution_scalars : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (r : ZMod 2), M7.QuotientAuto.substitution u ((AdjoinRoot.of (M6.Cyclic.modulus N)) r) = (AdjoinRoot.of (M6.Cyclic.modulus N)) r := by
  intro N inst u r
  unfold M7.QuotientAuto.substitution M7.CyclicSubstitution.hom
  exact AdjoinRoot.lift_of (M7.CyclicSubstitution.point_root N u)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ u v : (ZMod N)ˣ, (M7.QuotientAuto.substitution v).comp (M7.QuotientAuto.substitution u) = M7.QuotientAuto.substitution (v*u)
