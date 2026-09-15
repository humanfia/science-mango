import M7QuotientAuto

theorem M7.QuotientAuto.substitution_root : ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.QuotientAuto.substitution u (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.point u := by
  intro N inst u
  exact M7.CyclicSubstitution.hom_root N u (M7.CyclicSubstitution.point_root N u)

theorem M7.QuotientAuto.substitution_scalars : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (r : ZMod 2), M7.QuotientAuto.substitution u ((AdjoinRoot.of (M6.Cyclic.modulus N)) r) = (AdjoinRoot.of (M6.Cyclic.modulus N)) r := by
  intro N inst u r
  unfold M7.QuotientAuto.substitution M7.CyclicSubstitution.hom
  exact AdjoinRoot.lift_of (M7.CyclicSubstitution.point_root N u)

theorem M7.QuotientAuto.substitution_comp : ∀ (N : ℕ) [NeZero N], ∀ u v : (ZMod N)ˣ, (M7.QuotientAuto.substitution v).comp (M7.QuotientAuto.substitution u) = M7.QuotientAuto.substitution (v*u) := by
  intro N inst u v
  apply AdjoinRoot.ringHom_ext
  · ext r
    simp only [RingHom.comp_apply, M7.QuotientAuto.substitution_scalars]
  · change M7.QuotientAuto.substitution v (M7.QuotientAuto.substitution u (M7.CyclicSubstitution.rho N)) = M7.QuotientAuto.substitution (v * u) (M7.CyclicSubstitution.rho N)
    rw [M7.QuotientAuto.substitution_root, M7.QuotientAuto.substitution_root]
    change M7.QuotientAuto.substitution v (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) = M7.CyclicSubstitution.point (v * u)
    rw [map_pow, M7.QuotientAuto.substitution_root]
    simpa only [mul_comm] using M7.CyclicSubstitution.point_mul N v u

theorem M7.QuotientAuto.substitution_one : ∀ (N : ℕ) [NeZero N], M7.QuotientAuto.substitution (1 : (ZMod N)ˣ) = RingHom.id (M6.Cyclic.CycleRing N) := by
  intro N inst
  apply AdjoinRoot.ringHom_ext
  · ext r
    exact M7.QuotientAuto.substitution_scalars N (1 : (ZMod N)ˣ) r
  · change M7.QuotientAuto.substitution (1 : (ZMod N)ˣ) (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.rho N
    rw [M7.QuotientAuto.substitution_root, M7.CyclicSubstitution.point_one]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (x : M6.Cyclic.CycleRing N), M7.QuotientAuto.substitution u (M7.QuotientAuto.substitution (u⁻¹) x) = x
