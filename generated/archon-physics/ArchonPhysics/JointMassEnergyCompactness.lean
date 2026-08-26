import ArchonPhysics.UniformMassGaugeCoercivity

/-!
# Joint compactness of a mass box and a coercive energy shell

For parameter-dependent ODE arguments it is not enough that every fixed-mass
energy shell is compact: the mass and phase variables must live in one fixed
ambient space.  We therefore retain both the mass and inverse-mass coordinates
and impose their reciprocal relation polynomially.  This avoids division in
the definition of the closed set.

The resulting joint shell is closed and, under common upper bounds on masses
and inverse masses, uniformly bounded.  Hence it is compact.  This file makes
no choice of an ODE solution.
-/

namespace ArchonPhysics.JointMassEnergyCompactness

open ArchonPhysics
open ArchonPhysics.UniformMassGaugeCoercivity
open Set Metric

noncomputable section

/-- Mass, inverse mass, position, and momentum in one fixed ambient space. -/
abbrev MassInversePhysicalPhaseSpace (N : Nat) :=
  (Lattice.Configuration N × Lattice.Configuration N) ×
    PhysicalPhaseSpace N

/-- The polynomial Hamiltonian obtained when inverse masses are retained as
independent coordinates. -/
def inverseMassHamiltonian {N : Nat} [NeZero N]
    (u : Lattice.Configuration N) (kappa beta g : Real)
    (p q : Lattice.Configuration N) : Real :=
  (∑ i, u i * p i ^ 2 / 2) +
    CoerciveLatticeEnergy.potentialEnergy kappa beta g q

/-- A joint mass--inverse-mass box and physical energy shell.  The identity
`mᵢ uᵢ = 1` is included in the set, as are both translation-reduction gauges. -/
def jointMassInverseEnergySublevel {N : Nat} [NeZero N]
    (mLower mUpper uLower uUpper kappa beta g H : Real) :
    Set (MassInversePhysicalPhaseSpace N) :=
  {x |
    (∀ i, mLower ≤ x.1.1 i ∧ x.1.1 i ≤ mUpper ∧
      uLower ≤ x.1.2 i ∧ x.1.2 i ≤ uUpper ∧
      x.1.1 i * x.1.2 i = 1) ∧
    (∑ i, x.1.1 i * x.2.1 i) = 0 ∧
    (∑ i, x.2.2 i) = 0 ∧
    inverseMassHamiltonian x.1.2 kappa beta g x.2.2 x.2.1 ≤ H}

/-- The joint shell is closed in the fixed ambient finite-dimensional space.
The reciprocal constraint is polynomial, so no continuity-at-zero issue for
the inverse function occurs in this proof. -/
theorem jointMassInverseEnergySublevel_isClosed
    {N : Nat} [NeZero N]
    (mLower mUpper uLower uUpper kappa beta g H : Real) :
    IsClosed (jointMassInverseEnergySublevel (N := N)
      mLower mUpper uLower uUpper kappa beta g H) := by
  let box : Set (MassInversePhysicalPhaseSpace N) :=
    ⋂ i, {x | mLower ≤ x.1.1 i ∧ x.1.1 i ≤ mUpper ∧
      uLower ≤ x.1.2 i ∧ x.1.2 i ≤ uUpper ∧
      x.1.1 i * x.1.2 i = 1}
  have hbox : IsClosed box := by
    apply isClosed_iInter
    intro i
    have hm : Continuous
        (fun x : MassInversePhysicalPhaseSpace N => x.1.1 i) := by
      fun_prop
    have hu : Continuous
        (fun x : MassInversePhysicalPhaseSpace N => x.1.2 i) := by
      fun_prop
    exact (isClosed_le continuous_const hm).inter
      ((isClosed_le hm continuous_const).inter
      ((isClosed_le continuous_const hu).inter
      ((isClosed_le hu continuous_const).inter
      (isClosed_eq (hm.mul hu) continuous_const))))
  have hgauge : IsClosed
      {x : MassInversePhysicalPhaseSpace N |
        (∑ i, x.1.1 i * x.2.1 i) = 0} := by
    apply isClosed_eq
    · fun_prop
    · exact continuous_const
  have hmomentum : IsClosed
      {x : MassInversePhysicalPhaseSpace N | (∑ i, x.2.2 i) = 0} := by
    apply isClosed_eq
    · fun_prop
    · exact continuous_const
  have henergy : IsClosed
      {x : MassInversePhysicalPhaseSpace N |
        inverseMassHamiltonian x.1.2 kappa beta g x.2.2 x.2.1 ≤ H} := by
    apply isClosed_le
    · unfold inverseMassHamiltonian
        CoerciveLatticeEnergy.potentialEnergy
        CoerciveCubicPotential.potential Lattice.forwardDifference
      fun_prop
    · exact continuous_const
  have hset : jointMassInverseEnergySublevel (N := N)
      mLower mUpper uLower uUpper kappa beta g H =
      ((box ∩ {x | (∑ i, x.1.1 i * x.2.1 i) = 0}) ∩
        {x | (∑ i, x.2.2 i) = 0}) ∩
        {x | inverseMassHamiltonian x.1.2 kappa beta g
          x.2.2 x.2.1 ≤ H} := by
    ext x
    simp only [jointMassInverseEnergySublevel, box, mem_ofPred_eq,
      mem_iInter, mem_inter_iff]
    tauto
  rw [hset]
  exact ((hbox.inter hgauge).inter hmomentum).inter henergy

private theorem configuration_norm_le_of_box
    {N : Nat} [NeZero N] (x : Lattice.Configuration N) {B : Real}
    (hxNonneg : ∀ i, 0 ≤ x i) (hxUpper : ∀ i, x i ≤ B) :
    ‖x‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hxNonneg i)] using hxUpper i

/-- On the reciprocal constraint, the polynomial inverse-mass Hamiltonian is
exactly the original lattice Hamiltonian for the associated positive mass. -/
theorem inverseMassHamiltonian_eq_hamiltonian_of_reciprocal
    {N : Nat} [NeZero N]
    {m u p q : Lattice.Configuration N}
    (hmPos : ∀ i, 0 < m i) (hreciprocal : ∀ i, m i * u i = 1)
    (kappa beta g : Real) :
    inverseMassHamiltonian u kappa beta g p q =
      CoerciveLatticeEnergy.hamiltonian
        ⟨m, hmPos⟩ kappa beta g p q := by
  unfold inverseMassHamiltonian CoerciveLatticeEnergy.hamiltonian
    Lattice.kineticEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  have hmNe : m i ≠ 0 := ne_of_gt (hmPos i)
  have hu : u i = (m i)⁻¹ := by
    calc
      u i = 1 * u i := (one_mul _).symm
      _ = ((m i)⁻¹ * m i) * u i := by rw [inv_mul_cancel₀ hmNe]
      _ = (m i)⁻¹ * (m i * u i) := by ring
      _ = (m i)⁻¹ := by rw [hreciprocal i, mul_one]
  rw [hu]
  field_simp

/-- A single explicit ambient radius controls the entire joint mass box and
energy shell.  The phase-space part reuses the mass-uniform Poincare estimate. -/
theorem jointMassInverseEnergySublevel_norm_le
    {N : Nat} [NeZero N]
    {C mLower mUpper uLower uUpper kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hmLower : 0 < mLower) (huLower : 0 ≤ uLower)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    {x : MassInversePhysicalPhaseSpace N}
    (hx : x ∈ jointMassInverseEnergySublevel (N := N)
      mLower mUpper uLower uUpper kappa beta g H) :
    ‖x‖ ≤ max (max mUpper uUpper)
      (max
        (C * (H /
          CoerciveCubicPotential.coercivityConstant kappa beta + 1))
        (2 * mUpper * H + 1)) := by
  rcases hx with ⟨hbox, hgauge, _hmomentum, henergy⟩
  let m : Lattice.PositiveMassConfig N :=
    ⟨x.1.1, fun i => lt_of_lt_of_le hmLower (hbox i).1⟩
  have hmUpper : ∀ i, m.mass i ≤ mUpper := fun i => (hbox i).2.1
  have hreciprocal : ∀ i, m.mass i * x.1.2 i = 1 :=
    fun i => (hbox i).2.2.2.2
  have hphysical : x.2 ∈ physicalEnergySublevel m kappa beta g H := by
    refine ⟨hgauge, ?_⟩
    rw [← inverseMassHamiltonian_eq_hamiltonian_of_reciprocal
      m.mass_pos hreciprocal]
    exact henergy
  have hphase : ‖x.2‖ ≤ max
      (C * (H /
        CoerciveCubicPotential.coercivityConstant kappa beta + 1))
      (2 * mUpper * H + 1) :=
    physicalEnergySublevel_norm_le hC hPoincare hbeta m hmUpper hphysical
  have hmNorm : ‖x.1.1‖ ≤ mUpper := by
    apply configuration_norm_le_of_box x.1.1
    · intro i
      exact (hmLower.le.trans (hbox i).1)
    · exact fun i => (hbox i).2.1
  have huNorm : ‖x.1.2‖ ≤ uUpper := by
    apply configuration_norm_le_of_box x.1.2
    · intro i
      exact huLower.trans (hbox i).2.2.1
    · exact fun i => (hbox i).2.2.2.1
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le_max (max_le_max hmNorm huNorm) hphase

/-- Joint compactness, rather than merely fiberwise compactness, of the
mass-box energy shell in the fixed ambient space. -/
theorem jointMassInverseEnergySublevel_isCompact
    {N : Nat} [NeZero N]
    {C mLower mUpper uLower uUpper kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hmLower : 0 < mLower) (huLower : 0 ≤ uLower)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    IsCompact (jointMassInverseEnergySublevel (N := N)
      mLower mUpper uLower uUpper kappa beta g H) := by
  apply Metric.isCompact_of_isClosed_isBounded
    (jointMassInverseEnergySublevel_isClosed
      mLower mUpper uLower uUpper kappa beta g H)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max (max mUpper uUpper)
    (max
      (C * (H /
        CoerciveCubicPotential.coercivityConstant kappa beta + 1))
      (2 * mUpper * H + 1)), ?_⟩
  intro x hx
  exact jointMassInverseEnergySublevel_norm_le
    hC hPoincare hmLower huLower hbeta hx

end

end ArchonPhysics.JointMassEnergyCompactness
