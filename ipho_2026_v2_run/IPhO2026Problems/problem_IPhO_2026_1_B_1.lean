import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 1, part B.1

An electron and a positron of equal mass form an isolated, classical,
non-relativistic Coulomb two-body system.  Figure 1b gives an instantaneous
separation of `100 a₀`, opposite transverse velocities, and angular-momentum
magnitude `μ ℏ` for each particle.  This file records the dimensional data and
the effective-energy laws needed to characterize the outer turning point when
`μ = 4`.
-/

namespace IPhO2026Problem1B1

open Dimension

/-! ## Dimension-tagged physical quantities -/

/-- A scalar length measured in an arbitrary but fixed system of units. -/
abbrev LengthQuantity := WithDim L𝓭 ℝ

/-- A scalar mass measured in an arbitrary but fixed system of units. -/
abbrev MassQuantity := WithDim M𝓭 ℝ

/-- A signed electric charge measured in an arbitrary but fixed system of units. -/
abbrev ChargeQuantity := WithDim C𝓭 ℝ

/-- A three-dimensional position vector. -/
abbrev PositionQuantity :=
  WithDim L𝓭 (EuclideanSpace ℝ (Fin 3))

/-- A three-dimensional velocity vector. -/
abbrev VelocityQuantity :=
  WithDim (L𝓭 * T𝓭⁻¹) (EuclideanSpace ℝ (Fin 3))

/-- Action, and hence angular momentum, with dimension `M L² T⁻¹`. -/
abbrev ActionQuantity :=
  WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹) ℝ

/-- Energy with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity :=
  WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- Coulomb's constant, with dimension `M L³ T⁻² C⁻²`. -/
abbrev CoulombConstantQuantity :=
  WithDim
    (M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹)
    ℝ

/-- Vacuum permittivity, with dimension `M⁻¹ L⁻³ T² C²`. -/
abbrev VacuumPermittivityQuantity :=
  WithDim
    (M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 * T𝓭 * C𝓭 * C𝓭)
    ℝ

/-! ## Particle and pair data -/

/-- The state variables displayed for one of the two particles in Fig. 1b. -/
structure ParticleState where
  mass : MassQuantity
  charge : ChargeQuantity
  position : PositionQuantity
  velocity : VelocityQuantity
  angularMomentumMagnitude : ActionQuantity

/--
All named physical quantities used in the electron--positron model.

The scalar fields are readouts in one fixed unit system, while their types retain
their physical dimensions.  `mu` is the dimensionless angular-momentum factor.
-/
structure CoulombPairSystem where
  positron : ParticleState
  electron : ParticleState
  chargeMagnitude : ChargeQuantity
  vacuumPermittivity : VacuumPermittivityQuantity
  reducedPlanckConstant : ActionQuantity
  bohrRadius : LengthQuantity
  coulombConstant : CoulombConstantQuantity
  initialSeparation : LengthQuantity
  maximumSeparation : LengthQuantity
  totalEnergy : EnergyQuantity
  mu : ℝ

/--
The classical effective energy of the pair at a radial turning point of
separation `r`.

For either particle, `ℓ = m (r/2) v`, so the two kinetic energies sum to
`4 ℓ² / (m r²)`.  The electrostatic potential energy of the opposite charges is
`-k e² / r`.
-/
noncomputable def turningPointEnergyReadout
    (s : CoulombPairSystem) (r : LengthQuantity) : ℝ :=
  4 * s.positron.angularMomentumMagnitude.val ^ 2 /
      (s.positron.mass.val * r.val ^ 2) -
    s.coulombConstant.val * s.chargeMagnitude.val ^ 2 / r.val

/-! ## Assumptions and governing laws -/

/--
The figure readouts and physical laws for the isolated classical Coulomb pair.

The two energy equations are the usable mathematical consequences of the
classical, non-relativistic, electrostatic-only, isolated-system assumptions.
The final numerical value of `maximumSeparation` is deliberately not a field.
-/
structure CoulombPairLaws (s : CoulombPairSystem) : Prop where
  positron_mass_positive : 0 < s.positron.mass.val
  electron_mass_positive : 0 < s.electron.mass.val
  charge_magnitude_positive : 0 < s.chargeMagnitude.val
  vacuum_permittivity_positive : 0 < s.vacuumPermittivity.val
  reduced_planck_constant_positive : 0 < s.reducedPlanckConstant.val
  bohr_radius_positive : 0 < s.bohrRadius.val
  initial_separation_positive : 0 < s.initialSeparation.val
  maximum_separation_positive : 0 < s.maximumSeparation.val
  equal_masses : s.positron.mass.val = s.electron.mass.val
  positron_charge :
    s.positron.charge.val = s.chargeMagnitude.val
  electron_charge :
    s.electron.charge.val = -s.chargeMagnitude.val
  coulomb_constant_definition :
    s.coulombConstant.val =
      1 / (4 * Real.pi * s.vacuumPermittivity.val)
  bohr_radius_definition :
    s.bohrRadius.val =
      4 * Real.pi * s.vacuumPermittivity.val *
          s.reducedPlanckConstant.val ^ 2 /
        (s.positron.mass.val * s.chargeMagnitude.val ^ 2)
  figure_center_of_mass :
    s.positron.position.val = -s.electron.position.val
  figure_antiparallel_velocities :
    s.positron.velocity.val = -s.electron.velocity.val
  figure_positron_velocity_perpendicular :
    inner ℝ
        (s.positron.position.val - s.electron.position.val)
        s.positron.velocity.val = 0
  figure_electron_velocity_perpendicular :
    inner ℝ
        (s.positron.position.val - s.electron.position.val)
        s.electron.velocity.val = 0
  figure_initial_separation :
    ‖s.positron.position.val - s.electron.position.val‖ =
      s.initialSeparation.val
  initial_separation_is_one_hundred_bohr_radii :
    s.initialSeparation.val = 100 * s.bohrRadius.val
  figure_positron_angular_momentum_magnitude :
    s.positron.angularMomentumMagnitude.val =
      s.positron.mass.val * (s.initialSeparation.val / 2) *
        ‖s.positron.velocity.val‖
  figure_electron_angular_momentum_magnitude :
    s.electron.angularMomentumMagnitude.val =
      s.electron.mass.val * (s.initialSeparation.val / 2) *
        ‖s.electron.velocity.val‖
  positron_angular_momentum :
    s.positron.angularMomentumMagnitude.val =
      s.mu * s.reducedPlanckConstant.val
  electron_angular_momentum :
    s.electron.angularMomentumMagnitude.val =
      s.mu * s.reducedPlanckConstant.val
  mu_eq_four : s.mu = 4
  bound_orbit_energy : s.totalEnergy.val < 0
  isolated_energy_at_initial_turning_point :
    s.totalEnergy.val =
      turningPointEnergyReadout s s.initialSeparation
  isolated_energy_at_outer_turning_point :
    s.totalEnergy.val =
      turningPointEnergyReadout s s.maximumSeparation
  outer_turning_point_branch :
    s.initialSeparation.val < s.maximumSeparation.val

/-! ## Requested result -/

/--
For `μ = 4`, the maximum electron--positron separation is
`(1600 / 9) a₀`.
-/
theorem maximum_separation_for_mu_four
    (s : CoulombPairSystem) (laws : CoulombPairLaws s) :
    s.maximumSeparation.val =
      (1600 / 9 : ℝ) * s.bohrRadius.val := by
  have hm : s.positron.mass.val ≠ 0 :=
    ne_of_gt laws.positron_mass_positive
  have he : s.chargeMagnitude.val ≠ 0 :=
    ne_of_gt laws.charge_magnitude_positive
  have hε : s.vacuumPermittivity.val ≠ 0 :=
    ne_of_gt laws.vacuum_permittivity_positive
  have hℏ : s.reducedPlanckConstant.val ≠ 0 :=
    ne_of_gt laws.reduced_planck_constant_positive
  have ha : s.bohrRadius.val ≠ 0 :=
    ne_of_gt laws.bohr_radius_positive
  have hr : s.maximumSeparation.val ≠ 0 :=
    ne_of_gt laws.maximum_separation_positive
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcoulomb :
      s.coulombConstant.val * s.chargeMagnitude.val ^ 2 =
        s.reducedPlanckConstant.val ^ 2 /
          (s.positron.mass.val * s.bohrRadius.val) := by
    rw [laws.coulomb_constant_definition, laws.bohr_radius_definition]
    field_simp [hm, he, hε, hℏ, hπ]
  have henergy :
      turningPointEnergyReadout s s.initialSeparation =
        turningPointEnergyReadout s s.maximumSeparation :=
    laws.isolated_energy_at_initial_turning_point.symm.trans
      laws.isolated_energy_at_outer_turning_point
  simp only [turningPointEnergyReadout] at henergy
  rw [laws.positron_angular_momentum, laws.mu_eq_four,
    laws.initial_separation_is_one_hundred_bohr_radii, hcoulomb] at henergy
  have hbranch := laws.outer_turning_point_branch
  rw [laws.initial_separation_is_one_hundred_bohr_radii] at hbranch
  field_simp [hm, ha, hr] at henergy
  ring_nf at henergy
  nlinarith

end IPhO2026Problem1B1
