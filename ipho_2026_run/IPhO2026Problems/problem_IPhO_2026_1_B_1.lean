import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 1, part B.1

This file models the electron-positron pair in Figure 1b.  Physical scalar and
vector quantities use PhysLean's unit-independent `Dimensionful` quantities;
all equations between numerical readouts are explicitly stated in SI units.
The Coulomb conic laws printed as hints on the source page are exposed as
governing laws rather than being replaced by the requested numerical answer.
-/

namespace IPhO2026Problems.IPhO2026_1_B_1

open Dimension UnitChoices

/-- Three-dimensional Euclidean space used for the Figure 1b geometry. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A unit-independent scalar physical quantity of dimension `d`. -/
abbrev ScalarQuantity (d : Dimension) := Dimensionful (WithDim d ℝ)

/-- A unit-independent spatial vector physical quantity of dimension `d`. -/
abbrev VectorQuantity (d : Dimension) := Dimensionful (WithDim d Space)

/-- The dimension of velocity. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The dimension of angular momentum, including the reduced Planck constant. -/
def angularMomentumDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- The dimension of energy. -/
def energyDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension of Coulomb's constant. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension of vacuum permittivity. -/
def permittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

abbrev PhysicalLength := ScalarQuantity L𝓭
abbrev PhysicalMass := ScalarQuantity M𝓭
abbrev PhysicalCharge := ScalarQuantity C𝓭
abbrev PhysicalSpeed := ScalarQuantity velocityDimension
abbrev PhysicalAngularMomentum := ScalarQuantity angularMomentumDimension
abbrev PhysicalEnergy := ScalarQuantity energyDimension
abbrev PhysicalCoulombConstant := ScalarQuantity coulombConstantDimension
abbrev PhysicalPermittivity := ScalarQuantity permittivityDimension
abbrev PositionVector := VectorQuantity L𝓭
abbrev VelocityVector := VectorQuantity velocityDimension

/-- The numerical SI readout of a scalar dimensionful quantity. -/
noncomputable def scalarInSI {d : Dimension} (quantity : ScalarQuantity d) : ℝ :=
  (quantity SI).val

/-- The numerical SI coordinate vector of a dimensionful spatial vector. -/
noncomputable def vectorInSI {d : Dimension} (quantity : VectorQuantity d) : Space :=
  (quantity SI).val

/--
Physical constants and common particle data for the electron-positron pair.
The single mass field records that both particles have mass `m`, while
`elementaryChargeMagnitude` is the positive magnitude `e` of their charges.
-/
structure PhysicalConstants where
  mass : PhysicalMass
  elementaryChargeMagnitude : PhysicalCharge
  reducedPlanckConstant : PhysicalAngularMomentum
  vacuumPermittivity : PhysicalPermittivity
  coulombConstant : PhysicalCoulombConstant
  bohrRadius : PhysicalLength
  speedOfLight : PhysicalSpeed
  mass_pos : 0 < scalarInSI mass
  elementaryChargeMagnitude_pos : 0 < scalarInSI elementaryChargeMagnitude
  reducedPlanckConstant_pos : 0 < scalarInSI reducedPlanckConstant
  vacuumPermittivity_pos : 0 < scalarInSI vacuumPermittivity
  bohrRadius_pos : 0 < scalarInSI bohrRadius
  speedOfLight_pos : 0 < scalarInSI speedOfLight
  coulomb_constant_law :
    scalarInSI coulombConstant =
      1 / (4 * Real.pi * scalarInSI vacuumPermittivity)
  bohr_radius_law :
    scalarInSI bohrRadius =
      4 * Real.pi * scalarInSI vacuumPermittivity *
          scalarInSI reducedPlanckConstant ^ 2 /
        (scalarInSI mass * scalarInSI elementaryChargeMagnitude ^ 2)

/--
The instantaneous data shown in Figure 1b.  Positions are measured from the
center of mass.  The dimensionless factor `mu` is specialized to `4` for B.1.
-/
structure Figure1bInitialState (constants : PhysicalConstants) where
  mu : ℝ
  positronCharge : PhysicalCharge
  electronCharge : PhysicalCharge
  positronPosition : PositionVector
  electronPosition : PositionVector
  relativeSeparationVector : PositionVector
  positronVelocity : VelocityVector
  electronVelocity : VelocityVector
  initialSeparation : PhysicalLength
  positronAngularMomentumMagnitude : PhysicalAngularMomentum
  electronAngularMomentumMagnitude : PhysicalAngularMomentum
  mu_eq_four : mu = 4
  positron_charge_law :
    scalarInSI positronCharge =
      scalarInSI constants.elementaryChargeMagnitude
  electron_charge_law :
    scalarInSI electronCharge =
      -scalarInSI constants.elementaryChargeMagnitude
  center_of_mass_origin :
    vectorInSI positronPosition + vectorInSI electronPosition = 0
  relative_separation_law :
    vectorInSI relativeSeparationVector =
      vectorInSI positronPosition - vectorInSI electronPosition
  separation_is_distance :
    ‖vectorInSI relativeSeparationVector‖ = scalarInSI initialSeparation
  initial_separation_readout :
    scalarInSI initialSeparation = 100 * scalarInSI constants.bohrRadius
  initial_separation_pos : 0 < scalarInSI initialSeparation
  velocities_antiparallel :
    ∃ ratio : ℝ, 0 < ratio ∧
      vectorInSI positronVelocity =
        (-ratio) • vectorInSI electronVelocity
  positron_velocity_transverse :
    inner ℝ (vectorInSI relativeSeparationVector)
      (vectorInSI positronVelocity) = 0
  electron_velocity_transverse :
    inner ℝ (vectorInSI relativeSeparationVector)
      (vectorInSI electronVelocity) = 0
  positron_angular_momentum_definition :
    scalarInSI positronAngularMomentumMagnitude =
      scalarInSI constants.mass * ‖vectorInSI positronPosition‖ *
        ‖vectorInSI positronVelocity‖
  electron_angular_momentum_definition :
    scalarInSI electronAngularMomentumMagnitude =
      scalarInSI constants.mass * ‖vectorInSI electronPosition‖ *
        ‖vectorInSI electronVelocity‖
  positron_angular_momentum_readout :
    scalarInSI positronAngularMomentumMagnitude =
      mu * scalarInSI constants.reducedPlanckConstant
  electron_angular_momentum_readout :
    scalarInSI electronAngularMomentumMagnitude =
      mu * scalarInSI constants.reducedPlanckConstant

/--
A classical trajectory of the pair.  Its real argument is explicitly the SI
time coordinate in seconds.  `conicParameter` is the numerator called `a` in
the polar conic equation printed in Hint 2.
-/
structure ElectronPositronOrbit where
  initialTimeSI : ℝ
  positronPositionAt : ℝ → PositionVector
  electronPositionAt : ℝ → PositionVector
  positronVelocityAt : ℝ → VelocityVector
  electronVelocityAt : ℝ → VelocityVector
  separationAt : ℝ → PhysicalLength
  kineticEnergyAt : ℝ → PhysicalEnergy
  electrostaticPotentialEnergyAt : ℝ → PhysicalEnergy
  totalAngularMomentumMagnitudeAt : ℝ → PhysicalAngularMomentum
  totalEnergy : PhysicalEnergy
  totalAngularMomentumMagnitude : PhysicalAngularMomentum
  eccentricity : ℝ
  conicParameter : PhysicalLength
  polarAngleAt : ℝ → ℝ
  maximumSeparation : PhysicalLength

/-- The relative position coordinate of the positron with respect to the electron. -/
noncomputable def relativePositionInSI
    (orbit : ElectronPositronOrbit) (timeSI : ℝ) : Space :=
  vectorInSI (orbit.positronPositionAt timeSI) -
    vectorInSI (orbit.electronPositionAt timeSI)

/-- The relative velocity coordinate of the positron with respect to the electron. -/
noncomputable def relativeVelocityInSI
    (orbit : ElectronPositronOrbit) (timeSI : ℝ) : Space :=
  vectorInSI (orbit.positronVelocityAt timeSI) -
    vectorInSI (orbit.electronVelocityAt timeSI)

/--
The system is bound in the sense stated in B.1: its relative position is
periodic, hence the particles follow a closed orbit about their center of mass.
The remaining fields give the defining order properties of the maximum
separation and the two apsidal directions of a complete ellipse.
-/
structure IsBoundClosedOrbit (orbit : ElectronPositronOrbit) : Prop where
  closed_orbit :
    ∃ periodSI : ℝ, 0 < periodSI ∧
      ∀ timeSI,
        relativePositionInSI orbit (timeSI + periodSI) =
          relativePositionInSI orbit timeSI
  eccentricity_range : 0 ≤ orbit.eccentricity ∧ orbit.eccentricity < 1
  separation_positive :
    ∀ timeSI, 0 < scalarInSI (orbit.separationAt timeSI)
  maximum_is_upper_bound :
    ∀ timeSI,
      scalarInSI (orbit.separationAt timeSI) ≤
        scalarInSI orbit.maximumSeparation
  maximum_is_attained :
    ∃ timeSI,
      orbit.separationAt timeSI = orbit.maximumSeparation
  apocentre_direction_is_attained :
    ∃ timeSI, Real.cos (orbit.polarAngleAt timeSI) = 1
  pericentre_direction_is_attained :
    ∃ timeSI, Real.cos (orbit.polarAngleAt timeSI) = -1

/--
The governing classical, isolated, non-relativistic electrostatic model.

The energy equations express that the only interaction potential is Coulomb's
potential and that total mechanical energy is conserved.  Angular momentum is
likewise conserved.  The last three fields are precisely the standard Coulomb
conic relations, including the two hints printed on the official source page.
-/
structure SatisfiesClassicalCoulombConicLaws
    (constants : PhysicalConstants)
    (initial : Figure1bInitialState constants)
    (orbit : ElectronPositronOrbit) : Prop where
  initial_positron_position :
    orbit.positronPositionAt orbit.initialTimeSI = initial.positronPosition
  initial_electron_position :
    orbit.electronPositionAt orbit.initialTimeSI = initial.electronPosition
  initial_positron_velocity :
    orbit.positronVelocityAt orbit.initialTimeSI = initial.positronVelocity
  initial_electron_velocity :
    orbit.electronVelocityAt orbit.initialTimeSI = initial.electronVelocity
  initial_separation :
    orbit.separationAt orbit.initialTimeSI = initial.initialSeparation
  center_of_mass_frame :
    ∀ timeSI,
      vectorInSI (orbit.positronPositionAt timeSI) +
        vectorInSI (orbit.electronPositionAt timeSI) = 0
  separation_is_relative_distance :
    ∀ timeSI,
      scalarInSI (orbit.separationAt timeSI) =
        ‖relativePositionInSI orbit timeSI‖
  positron_nonrelativistic :
    ∀ timeSI,
      ‖vectorInSI (orbit.positronVelocityAt timeSI)‖ <
        scalarInSI constants.speedOfLight
  electron_nonrelativistic :
    ∀ timeSI,
      ‖vectorInSI (orbit.electronVelocityAt timeSI)‖ <
        scalarInSI constants.speedOfLight
  classical_kinetic_energy :
    ∀ timeSI,
      scalarInSI (orbit.kineticEnergyAt timeSI) =
        scalarInSI constants.mass / 2 *
          (‖vectorInSI (orbit.positronVelocityAt timeSI)‖ ^ 2 +
            ‖vectorInSI (orbit.electronVelocityAt timeSI)‖ ^ 2)
  electrostatic_potential_energy :
    ∀ timeSI,
      scalarInSI (orbit.electrostaticPotentialEnergyAt timeSI) =
        -(scalarInSI constants.coulombConstant *
            scalarInSI constants.elementaryChargeMagnitude ^ 2 /
          scalarInSI (orbit.separationAt timeSI))
  isolated_energy_conservation :
    ∀ timeSI,
      scalarInSI orbit.totalEnergy =
        scalarInSI (orbit.kineticEnergyAt timeSI) +
          scalarInSI (orbit.electrostaticPotentialEnergyAt timeSI)
  isolated_angular_momentum_conservation :
    ∀ timeSI,
      scalarInSI (orbit.totalAngularMomentumMagnitudeAt timeSI) =
        scalarInSI orbit.totalAngularMomentumMagnitude
  initial_total_angular_momentum :
    scalarInSI orbit.totalAngularMomentumMagnitude =
      scalarInSI initial.positronAngularMomentumMagnitude +
        scalarInSI initial.electronAngularMomentumMagnitude
  eccentricity_law :
    orbit.eccentricity =
      Real.sqrt
        (1 +
          4 * scalarInSI orbit.totalAngularMomentumMagnitude ^ 2 *
              scalarInSI orbit.totalEnergy /
            (scalarInSI constants.coulombConstant ^ 2 *
              scalarInSI constants.elementaryChargeMagnitude ^ 4 *
              scalarInSI constants.mass))
  conic_parameter_law :
    scalarInSI orbit.conicParameter =
      2 * scalarInSI orbit.totalAngularMomentumMagnitude ^ 2 /
        (scalarInSI constants.mass *
          scalarInSI constants.coulombConstant *
          scalarInSI constants.elementaryChargeMagnitude ^ 2)
  polar_conic_law :
    ∀ timeSI,
      scalarInSI (orbit.separationAt timeSI) =
        scalarInSI orbit.conicParameter /
          (1 - orbit.eccentricity * Real.cos (orbit.polarAngleAt timeSI))

/-- For `mu = 4`, the two equal, co-oriented particle angular momenta total `8 ℏ`. -/
theorem total_angular_momentum_for_mu_four
    (constants : PhysicalConstants)
    (initial : Figure1bInitialState constants)
    (orbit : ElectronPositronOrbit)
    (laws : SatisfiesClassicalCoulombConicLaws constants initial orbit) :
    scalarInSI orbit.totalAngularMomentumMagnitude =
      8 * scalarInSI constants.reducedPlanckConstant := by
  rw [laws.initial_total_angular_momentum,
    initial.positron_angular_momentum_readout,
    initial.electron_angular_momentum_readout,
    initial.mu_eq_four]
  ring

/-- The conserved mechanical energy obtained from the Figure 1b initial state. -/
theorem total_energy_for_mu_four
    (constants : PhysicalConstants)
    (initial : Figure1bInitialState constants)
    (orbit : ElectronPositronOrbit)
    (laws : SatisfiesClassicalCoulombConicLaws constants initial orbit) :
    scalarInSI orbit.totalEnergy =
      -((9 : ℝ) / 2500) *
        (scalarInSI constants.coulombConstant *
            scalarInSI constants.elementaryChargeMagnitude ^ 2 /
          scalarInSI constants.bohrRadius) := by
  have helectron_position :
      vectorInSI initial.electronPosition =
        -vectorInSI initial.positronPosition :=
    eq_neg_of_add_eq_zero_right initial.center_of_mass_origin
  have hrelative_norm :
      ‖vectorInSI initial.relativeSeparationVector‖ =
        2 * ‖vectorInSI initial.positronPosition‖ := by
    rw [initial.relative_separation_law, helectron_position, sub_neg_eq_add,
      ← two_smul ℝ, norm_smul]
    norm_num
  have hpositron_position_norm :
      ‖vectorInSI initial.positronPosition‖ =
        50 * scalarInSI constants.bohrRadius := by
    have h := initial.separation_is_distance
    rw [hrelative_norm, initial.initial_separation_readout] at h
    linarith
  have helectron_position_norm :
      ‖vectorInSI initial.electronPosition‖ =
        50 * scalarInSI constants.bohrRadius := by
    rw [helectron_position, norm_neg, hpositron_position_norm]
  have hpositron_angular_momentum :
      scalarInSI constants.mass *
            ‖vectorInSI initial.positronPosition‖ *
            ‖vectorInSI initial.positronVelocity‖ =
        4 * scalarInSI constants.reducedPlanckConstant := by
    rw [← initial.positron_angular_momentum_definition,
      initial.positron_angular_momentum_readout, initial.mu_eq_four]
  have helectron_angular_momentum :
      scalarInSI constants.mass *
            ‖vectorInSI initial.electronPosition‖ *
            ‖vectorInSI initial.electronVelocity‖ =
        4 * scalarInSI constants.reducedPlanckConstant := by
    rw [← initial.electron_angular_momentum_definition,
      initial.electron_angular_momentum_readout, initial.mu_eq_four]
  have hpositron_velocity_norm :
      ‖vectorInSI initial.positronVelocity‖ =
        2 * scalarInSI constants.reducedPlanckConstant /
          (25 * scalarInSI constants.mass *
            scalarInSI constants.bohrRadius) := by
    rw [hpositron_position_norm] at hpositron_angular_momentum
    field_simp [ne_of_gt constants.mass_pos,
      ne_of_gt constants.bohrRadius_pos]
    nlinarith [hpositron_angular_momentum]
  have helectron_velocity_norm :
      ‖vectorInSI initial.electronVelocity‖ =
        2 * scalarInSI constants.reducedPlanckConstant /
          (25 * scalarInSI constants.mass *
            scalarInSI constants.bohrRadius) := by
    rw [helectron_position_norm] at helectron_angular_momentum
    field_simp [ne_of_gt constants.mass_pos,
      ne_of_gt constants.bohrRadius_pos]
    nlinarith [helectron_angular_momentum]
  have hcoulomb_times_permittivity :
      scalarInSI constants.coulombConstant *
          (4 * Real.pi * scalarInSI constants.vacuumPermittivity) =
        1 := by
    rw [constants.coulomb_constant_law]
    field_simp [ne_of_gt Real.pi_pos,
      ne_of_gt constants.vacuumPermittivity_pos]
  have hbohr_radius_times_denominator :
      scalarInSI constants.bohrRadius *
          (scalarInSI constants.mass *
            scalarInSI constants.elementaryChargeMagnitude ^ 2) =
        4 * Real.pi * scalarInSI constants.vacuumPermittivity *
          scalarInSI constants.reducedPlanckConstant ^ 2 := by
    rw [constants.bohr_radius_law]
    field_simp [ne_of_gt constants.mass_pos,
      ne_of_gt constants.elementaryChargeMagnitude_pos]
  have hplanck_square :
      scalarInSI constants.reducedPlanckConstant ^ 2 =
        scalarInSI constants.mass *
          scalarInSI constants.coulombConstant *
          scalarInSI constants.elementaryChargeMagnitude ^ 2 *
          scalarInSI constants.bohrRadius := by
    calc
      scalarInSI constants.reducedPlanckConstant ^ 2 =
          (scalarInSI constants.coulombConstant *
              (4 * Real.pi * scalarInSI constants.vacuumPermittivity)) *
            scalarInSI constants.reducedPlanckConstant ^ 2 := by
              rw [hcoulomb_times_permittivity]
              ring
      _ = scalarInSI constants.coulombConstant *
            (4 * Real.pi * scalarInSI constants.vacuumPermittivity *
              scalarInSI constants.reducedPlanckConstant ^ 2) := by ring
      _ = scalarInSI constants.coulombConstant *
            (scalarInSI constants.bohrRadius *
              (scalarInSI constants.mass *
                scalarInSI constants.elementaryChargeMagnitude ^ 2)) := by
              rw [hbohr_radius_times_denominator]
      _ = scalarInSI constants.mass *
            scalarInSI constants.coulombConstant *
            scalarInSI constants.elementaryChargeMagnitude ^ 2 *
            scalarInSI constants.bohrRadius := by ring
  have hkinetic := laws.classical_kinetic_energy orbit.initialTimeSI
  rw [laws.initial_positron_velocity, laws.initial_electron_velocity] at hkinetic
  have hkinetic_value :
      scalarInSI (orbit.kineticEnergyAt orbit.initialTimeSI) =
        ((4 : ℝ) / 625) *
          (scalarInSI constants.coulombConstant *
              scalarInSI constants.elementaryChargeMagnitude ^ 2 /
            scalarInSI constants.bohrRadius) := by
    calc
      scalarInSI (orbit.kineticEnergyAt orbit.initialTimeSI) =
          scalarInSI constants.mass / 2 *
            (‖vectorInSI initial.positronVelocity‖ ^ 2 +
              ‖vectorInSI initial.electronVelocity‖ ^ 2) := hkinetic
      _ = 4 * scalarInSI constants.reducedPlanckConstant ^ 2 /
            (625 * scalarInSI constants.mass *
              scalarInSI constants.bohrRadius ^ 2) := by
              rw [hpositron_velocity_norm, helectron_velocity_norm]
              field_simp [ne_of_gt constants.mass_pos,
                ne_of_gt constants.bohrRadius_pos]
              ring
      _ = ((4 : ℝ) / 625) *
            (scalarInSI constants.coulombConstant *
                scalarInSI constants.elementaryChargeMagnitude ^ 2 /
              scalarInSI constants.bohrRadius) := by
              rw [hplanck_square]
              field_simp [ne_of_gt constants.mass_pos,
                ne_of_gt constants.bohrRadius_pos]
  have hpotential_value :
      scalarInSI
          (orbit.electrostaticPotentialEnergyAt orbit.initialTimeSI) =
        -(scalarInSI constants.coulombConstant *
              scalarInSI constants.elementaryChargeMagnitude ^ 2 /
            (100 * scalarInSI constants.bohrRadius)) := by
    rw [laws.electrostatic_potential_energy orbit.initialTimeSI,
      laws.initial_separation, initial.initial_separation_readout]
  rw [laws.isolated_energy_conservation orbit.initialTimeSI,
    hkinetic_value, hpotential_value]
  field_simp [ne_of_gt constants.bohrRadius_pos]
  ring

/-- The eccentricity of the bound Coulomb ellipse for `mu = 4`. -/
theorem eccentricity_for_mu_four
    (constants : PhysicalConstants)
    (initial : Figure1bInitialState constants)
    (orbit : ElectronPositronOrbit)
    (laws : SatisfiesClassicalCoulombConicLaws constants initial orbit) :
    orbit.eccentricity = (7 : ℝ) / 25 := by
  have hcoulomb_pos : 0 < scalarInSI constants.coulombConstant := by
    rw [constants.coulomb_constant_law]
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        constants.vacuumPermittivity_pos)
  have hplanck_square :
      scalarInSI constants.reducedPlanckConstant ^ 2 =
        scalarInSI constants.mass *
          scalarInSI constants.coulombConstant *
          scalarInSI constants.elementaryChargeMagnitude ^ 2 *
          scalarInSI constants.bohrRadius := by
    rw [constants.coulomb_constant_law, constants.bohr_radius_law]
    field_simp [ne_of_gt Real.pi_pos,
      ne_of_gt constants.vacuumPermittivity_pos,
      ne_of_gt constants.mass_pos,
      ne_of_gt constants.elementaryChargeMagnitude_pos]
  rw [laws.eccentricity_law,
    total_angular_momentum_for_mu_four constants initial orbit laws,
    total_energy_for_mu_four constants initial orbit laws]
  have hsqrt_argument :
      1 +
          4 * (8 * scalarInSI constants.reducedPlanckConstant) ^ 2 *
              (-((9 : ℝ) / 2500) *
                (scalarInSI constants.coulombConstant *
                    scalarInSI constants.elementaryChargeMagnitude ^ 2 /
                  scalarInSI constants.bohrRadius)) /
            (scalarInSI constants.coulombConstant ^ 2 *
              scalarInSI constants.elementaryChargeMagnitude ^ 4 *
              scalarInSI constants.mass) =
        ((7 : ℝ) / 25) ^ 2 := by
    rw [show (8 * scalarInSI constants.reducedPlanckConstant) ^ 2 =
      64 * scalarInSI constants.reducedPlanckConstant ^ 2 by ring,
      hplanck_square]
    field_simp [ne_of_gt hcoulomb_pos,
      ne_of_gt constants.elementaryChargeMagnitude_pos,
      ne_of_gt constants.mass_pos,
      ne_of_gt constants.bohrRadius_pos]
    ring
  rw [hsqrt_argument, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7 / 25)]

/-- The semi-latus rectum (the numerator in Hint 2) for `mu = 4`. -/
theorem conic_parameter_for_mu_four
    (constants : PhysicalConstants)
    (initial : Figure1bInitialState constants)
    (orbit : ElectronPositronOrbit)
    (laws : SatisfiesClassicalCoulombConicLaws constants initial orbit) :
    scalarInSI orbit.conicParameter =
      128 * scalarInSI constants.bohrRadius := by
  have hcoulomb_pos : 0 < scalarInSI constants.coulombConstant := by
    rw [constants.coulomb_constant_law]
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        constants.vacuumPermittivity_pos)
  have hplanck_square :
      scalarInSI constants.reducedPlanckConstant ^ 2 =
        scalarInSI constants.mass *
          scalarInSI constants.coulombConstant *
          scalarInSI constants.elementaryChargeMagnitude ^ 2 *
          scalarInSI constants.bohrRadius := by
    rw [constants.coulomb_constant_law, constants.bohr_radius_law]
    field_simp [ne_of_gt Real.pi_pos,
      ne_of_gt constants.vacuumPermittivity_pos,
      ne_of_gt constants.mass_pos,
      ne_of_gt constants.elementaryChargeMagnitude_pos]
  rw [laws.conic_parameter_law,
    total_angular_momentum_for_mu_four constants initial orbit laws,
    show (8 * scalarInSI constants.reducedPlanckConstant) ^ 2 =
      64 * scalarInSI constants.reducedPlanckConstant ^ 2 by ring,
    hplanck_square]
  field_simp [ne_of_gt constants.mass_pos, ne_of_gt hcoulomb_pos,
    ne_of_gt constants.elementaryChargeMagnitude_pos]
  ring

/--
For the bound `mu = 4` electron-positron pair, the maximum separation is
`1600 / 9` Bohr radii.

Blueprint: `thm:physics:IPhO_2026_1_B_1:target`.
-/
theorem maximum_separation_for_mu_four
    (constants : PhysicalConstants)
    (initial : Figure1bInitialState constants)
    (orbit : ElectronPositronOrbit)
    (laws : SatisfiesClassicalCoulombConicLaws constants initial orbit)
    (bound : IsBoundClosedOrbit orbit) :
    scalarInSI orbit.maximumSeparation =
      ((1600 : ℝ) / 9) * scalarInSI constants.bohrRadius := by
  have heccentricity :=
    eccentricity_for_mu_four constants initial orbit laws
  have hconic_parameter :=
    conic_parameter_for_mu_four constants initial orbit laws
  obtain ⟨apocentreTime, hapocentre_direction⟩ :=
    bound.apocentre_direction_is_attained
  have hapocentre_polar := laws.polar_conic_law apocentreTime
  rw [hconic_parameter, heccentricity, hapocentre_direction] at hapocentre_polar
  have hapocentre_value :
      scalarInSI (orbit.separationAt apocentreTime) =
        ((1600 : ℝ) / 9) * scalarInSI constants.bohrRadius := by
    calc
      scalarInSI (orbit.separationAt apocentreTime) =
          128 * scalarInSI constants.bohrRadius /
            (1 - (7 : ℝ) / 25 * 1) := hapocentre_polar
      _ = ((1600 : ℝ) / 9) *
            scalarInSI constants.bohrRadius := by ring
  have hlower := bound.maximum_is_upper_bound apocentreTime
  rw [hapocentre_value] at hlower
  obtain ⟨maximumTime, hmaximum_attained⟩ := bound.maximum_is_attained
  have hmaximum_readout :
      scalarInSI (orbit.separationAt maximumTime) =
        scalarInSI orbit.maximumSeparation :=
    congrArg (fun quantity : PhysicalLength => scalarInSI quantity)
      hmaximum_attained
  have hmaximum_polar := laws.polar_conic_law maximumTime
  rw [hconic_parameter, heccentricity] at hmaximum_polar
  have hcos_le_one :
      Real.cos (orbit.polarAngleAt maximumTime) ≤ 1 :=
    Real.cos_le_one _
  have hdenominator_pos :
      0 <
        1 - (7 : ℝ) / 25 *
          Real.cos (orbit.polarAngleAt maximumTime) := by
    nlinarith
  have hmaximum_upper :
      scalarInSI (orbit.separationAt maximumTime) ≤
        ((1600 : ℝ) / 9) * scalarInSI constants.bohrRadius := by
    rw [hmaximum_polar]
    apply (div_le_iff₀ hdenominator_pos).2
    have hproduct_nonneg :
        0 ≤ scalarInSI constants.bohrRadius *
          (1 - Real.cos (orbit.polarAngleAt maximumTime)) :=
      mul_nonneg (le_of_lt constants.bohrRadius_pos)
        (sub_nonneg.mpr hcos_le_one)
    nlinarith
  rw [hmaximum_readout] at hmaximum_upper
  exact le_antisymm hmaximum_upper hlower

end IPhO2026Problems.IPhO2026_1_B_1
