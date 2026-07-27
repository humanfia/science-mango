import Mathlib
import Physlib.Units.Basic

/-!
# IPhO 2026, problem 1, part B.2

An electron and a positron undergo classical, non-relativistic Coulomb
scattering in the plane.  This file records the physical input, the two conic
relations supplied as hints, the orientation visible in Fig. 1b, and the
requested signed angle of the outgoing relative velocity.

Physical quantities themselves live in abstract carrier types indexed by their
Physlib dimensions.  Every real number used in a physical equation is explicitly
a scalar readout in one fixed coherent unit system.  Coordinates, dimensionless
ratios, and angles are real-valued.
-/

namespace IPhO2026_1_B_2

open Filter
open scoped RealInnerProductSpace

abbrev Plane := EuclideanSpace ℝ (Fin 2)

local instance planeFinrank : Fact (Module.finrank ℝ Plane = 2) :=
  ⟨by simp [Plane]⟩

/-- The rightward direction of the initial positron velocity in Fig. 1b. -/
def rightward : Plane := !₂[1, 0]

/-- The upward direction from the electron to the positron in Fig. 1b. -/
def upward : Plane := !₂[0, 1]

/-- The dimension of action and angular momentum, `M L² T⁻¹`. -/
def actionDimension : Dimension :=
  Dimension.M𝓭 * Dimension.L𝓭 * Dimension.L𝓭 * Dimension.T𝓭⁻¹

/-- The dimension of energy, `M L² T⁻²`. -/
def energyDimension : Dimension :=
  Dimension.M𝓭 * Dimension.L𝓭 * Dimension.L𝓭 *
    Dimension.T𝓭⁻¹ * Dimension.T𝓭⁻¹

/-- The dimension of Coulomb's constant, `M L³ T⁻² C⁻²`. -/
def coulombConstantDimension : Dimension :=
  Dimension.M𝓭 * Dimension.L𝓭 * Dimension.L𝓭 * Dimension.L𝓭 *
    Dimension.T𝓭⁻¹ * Dimension.T𝓭⁻¹ *
    Dimension.C𝓭⁻¹ * Dimension.C𝓭⁻¹

/-- The dimension of vacuum permittivity, inverse to Coulomb's constant. -/
def permittivityDimension : Dimension := coulombConstantDimension⁻¹

/--
An abstract physical quantity kind with dimension `d`, together with its
numerical readout in the one coherent system of units used in the equations.
-/
structure QuantityKind (d : Dimension) where
  Carrier : Type
  readout : Carrier → ℝ

/-- The dimensioned primitive quantity types needed by the scattering model. -/
structure QuantityModel where
  mass : QuantityKind Dimension.M𝓭
  charge : QuantityKind Dimension.C𝓭
  length : QuantityKind Dimension.L𝓭
  action : QuantityKind actionDimension
  energy : QuantityKind energyDimension
  coulombConstant : QuantityKind coulombConstantDimension
  permittivity : QuantityKind permittivityDimension

/--
The physical objects, trajectories, conic data, and asymptotic readouts in
part B.2.  The initial instant is represented by `t = 0`, and `t → +∞`
describes the outgoing unbound branch.
-/
structure ScatteringScenario (Q : QuantityModel) where
  particleMass : Q.mass.Carrier
  chargeMagnitude : Q.charge.Carrier
  positronCharge : Q.charge.Carrier
  electronCharge : Q.charge.Carrier
  hbar : Q.action.Carrier
  vacuumPermittivity : Q.permittivity.Carrier
  coulombConstant : Q.coulombConstant.Carrier
  bohrRadius : Q.length.Carrier
  initialSeparation : Q.length.Carrier
  totalAngularMomentum : Q.action.Carrier
  totalEnergy : Q.energy.Carrier
  polarConicParameter : Q.length.Carrier
  mu : ℝ
  initialParticleSpeed : ℝ
  eccentricity : ℝ
  positronPosition : ℝ → Plane
  electronPosition : ℝ → Plane
  positronVelocity : ℝ → Plane
  electronVelocity : ℝ → Plane
  conicAngle : ℝ → ℝ
  outgoingPolarAngle : ℝ
  asymptoticRelativeVelocity : Plane
  screenOrientation : Orientation ℝ Plane (Fin 2)

variable {Q : QuantityModel}

/-- Scalar mass readout in the chosen coherent unit system. -/
def particleMassReadout (S : ScatteringScenario Q) : ℝ :=
  Q.mass.readout S.particleMass

/-- Positive elementary-charge magnitude readout in the chosen unit system. -/
def chargeMagnitudeReadout (S : ScatteringScenario Q) : ℝ :=
  Q.charge.readout S.chargeMagnitude

/-- Reduced Planck constant readout. -/
def hbarReadout (S : ScatteringScenario Q) : ℝ :=
  Q.action.readout S.hbar

/-- Vacuum-permittivity readout. -/
def vacuumPermittivityReadout (S : ScatteringScenario Q) : ℝ :=
  Q.permittivity.readout S.vacuumPermittivity

/-- Coulomb-constant readout. -/
def coulombConstantReadout (S : ScatteringScenario Q) : ℝ :=
  Q.coulombConstant.readout S.coulombConstant

/-- Bohr-radius readout. -/
def bohrRadiusReadout (S : ScatteringScenario Q) : ℝ :=
  Q.length.readout S.bohrRadius

/-- Initial electron--positron separation readout. -/
def initialSeparationReadout (S : ScatteringScenario Q) : ℝ :=
  Q.length.readout S.initialSeparation

/-- Conserved total angular-momentum magnitude readout. -/
def totalAngularMomentumReadout (S : ScatteringScenario Q) : ℝ :=
  Q.action.readout S.totalAngularMomentum

/-- Conserved total-energy readout. -/
def totalEnergyReadout (S : ScatteringScenario Q) : ℝ :=
  Q.energy.readout S.totalEnergy

/-- The length readout denoted by `a` in the supplied polar-conic hint. -/
def polarConicParameterReadout (S : ScatteringScenario Q) : ℝ :=
  Q.length.readout S.polarConicParameter

/-- Separation vector directed from the electron to the positron. -/
def separationVector (S : ScatteringScenario Q) (t : ℝ) : Plane :=
  S.positronPosition t - S.electronPosition t

/-- Positron velocity relative to the electron. -/
def relativeVelocity (S : ScatteringScenario Q) (t : ℝ) : Plane :=
  S.positronVelocity t - S.electronVelocity t

/-- Electron--positron separation distance. -/
noncomputable def separationRadius (S : ScatteringScenario Q) (t : ℝ) : ℝ :=
  ‖separationVector S t‖

/-- The signed, counterclockwise-positive deflection from the initial positron line. -/
noncomputable def signedDeflectionRadians (S : ScatteringScenario Q) : ℝ :=
  (S.screenOrientation.oangle
    (S.positronVelocity 0) S.asymptoticRelativeVelocity).toReal

/-- Conversion of a dimensionless angle readout from radians to degrees. -/
noncomputable def radiansToDegrees (θ : ℝ) : ℝ := θ * 180 / Real.pi

/--
The governing physical laws and source/figure readouts.

These fields state Newton--Coulomb dynamics, the initial data, conserved-energy
and angular-momentum relations, the two supplied conic hints, and genuine limit
relations on the outgoing branch.  They do not contain the requested deflection
angle.
-/
structure CoulombScatteringLaws (S : ScatteringScenario Q) : Prop where
  particleMass_pos : 0 < particleMassReadout S
  chargeMagnitude_pos : 0 < chargeMagnitudeReadout S
  hbar_pos : 0 < hbarReadout S
  vacuumPermittivity_pos : 0 < vacuumPermittivityReadout S
  bohrRadius_pos : 0 < bohrRadiusReadout S
  coulombConstant_pos : 0 < coulombConstantReadout S
  initialParticleSpeed_pos : 0 < S.initialParticleSpeed
  positron_charge_readout :
    Q.charge.readout S.positronCharge = chargeMagnitudeReadout S
  electron_charge_readout :
    Q.charge.readout S.electronCharge = -chargeMagnitudeReadout S
  coulomb_constant_definition :
    coulombConstantReadout S =
      1 / (4 * Real.pi * vacuumPermittivityReadout S)
  bohr_radius_definition :
    bohrRadiusReadout S =
      4 * Real.pi * vacuumPermittivityReadout S * hbarReadout S ^ 2 /
        (particleMassReadout S * chargeMagnitudeReadout S ^ 2)
  mu_value : S.mu = 15 / 2
  initial_separation_value :
    initialSeparationReadout S = 100 * bohrRadiusReadout S
  fig1b_positron_position :
    S.positronPosition 0 =
      (initialSeparationReadout S / 2) • upward
  fig1b_electron_position :
    S.electronPosition 0 =
      -(initialSeparationReadout S / 2) • upward
  fig1b_positron_velocity :
    S.positronVelocity 0 = S.initialParticleSpeed • rightward
  fig1b_electron_velocity :
    S.electronVelocity 0 = -S.initialParticleSpeed • rightward
  initial_velocities_antiparallel :
    S.positronVelocity 0 = -S.electronVelocity 0
  initial_velocity_perpendicular_to_separation :
    inner ℝ (separationVector S 0) (S.positronVelocity 0) = 0
  fig1b_counterclockwise_orientation :
    (S.screenOrientation.oangle rightward upward).toReal = Real.pi / 2
  positron_velocity_is_derivative :
    ∀ t, HasDerivAt S.positronPosition (S.positronVelocity t) t
  electron_velocity_is_derivative :
    ∀ t, HasDerivAt S.electronPosition (S.electronVelocity t) t
  no_collision : ∀ t, separationVector S t ≠ 0
  positron_newton_coulomb :
    ∀ t, HasDerivAt S.positronVelocity
      ((-(coulombConstantReadout S * chargeMagnitudeReadout S ^ 2 /
        (particleMassReadout S * separationRadius S t ^ 3))) •
        separationVector S t) t
  electron_newton_coulomb :
    ∀ t, HasDerivAt S.electronVelocity
      ((coulombConstantReadout S * chargeMagnitudeReadout S ^ 2 /
        (particleMassReadout S * separationRadius S t ^ 3)) •
        separationVector S t) t
  each_particle_angular_momentum :
    particleMassReadout S * (initialSeparationReadout S / 2) *
        S.initialParticleSpeed =
      S.mu * hbarReadout S
  total_angular_momentum :
    totalAngularMomentumReadout S = 2 * S.mu * hbarReadout S
  total_energy_from_initial_data :
    totalEnergyReadout S =
      particleMassReadout S * S.initialParticleSpeed ^ 2 -
        coulombConstantReadout S * chargeMagnitudeReadout S ^ 2 /
          initialSeparationReadout S
  unbound_positive_energy : 0 < totalEnergyReadout S
  eccentricity_hint :
    S.eccentricity =
      Real.sqrt
        (1 + 4 * totalAngularMomentumReadout S ^ 2 * totalEnergyReadout S /
          (coulombConstantReadout S ^ 2 * chargeMagnitudeReadout S ^ 4 *
            particleMassReadout S))
  polar_conic_parameter_pos : 0 < polarConicParameterReadout S
  polar_conic_parameter_definition :
    polarConicParameterReadout S =
      totalAngularMomentumReadout S ^ 2 /
        ((particleMassReadout S / 2) * coulombConstantReadout S *
          chargeMagnitudeReadout S ^ 2)
  polar_conic_hint :
    ∀ t, separationRadius S t =
      polarConicParameterReadout S /
        (1 - S.eccentricity * Real.cos (S.conicAngle t))
  initial_conic_angle : S.conicAngle 0 = Real.pi
  conic_angle_matches_position :
    ∀ t, (S.screenOrientation.oangle (-upward) (separationVector S t)).toReal =
      S.conicAngle t
  outgoing_angle_range :
    0 < S.outgoingPolarAngle ∧ S.outgoingPolarAngle < Real.pi
  outgoing_conic_angle_limit :
    Tendsto S.conicAngle atTop (nhds S.outgoingPolarAngle)
  unbound_separation_limit :
    Tendsto (separationRadius S) atTop atTop
  asymptotic_relative_velocity_limit :
    Tendsto (relativeVelocity S) atTop (nhds S.asymptoticRelativeVelocity)
  asymptotic_relative_velocity_ne_zero :
    S.asymptoticRelativeVelocity ≠ 0
  outgoing_velocity_is_radial :
    Tendsto
      (fun t => (separationRadius S t)⁻¹ • separationVector S t)
      atTop
      (nhds (‖S.asymptoticRelativeVelocity‖⁻¹ •
        S.asymptoticRelativeVelocity))

/--
The conic equation on an unbounded branch forces the limiting polar angle to
be `arccos (1 / eccentricity)`.  The range hypothesis selects the outgoing
branch rather than the other root of the cosine equation.
-/
theorem outgoing_polar_angle_of_hyperbolic_conic
    (eccentricity conicParameter : ℝ)
    (radius polarAngle : ℝ → ℝ)
    (outgoingPolarAngle : ℝ)
    (hEccentricity : 1 < eccentricity)
    (hConicParameter : 0 < conicParameter)
    (hRadiusPositive : ∀ t, 0 < radius t)
    (hConic :
      ∀ t, radius t =
        conicParameter / (1 - eccentricity * Real.cos (polarAngle t)))
    (hRadiusLimit : Tendsto radius atTop atTop)
    (hAngleLimit : Tendsto polarAngle atTop (nhds outgoingPolarAngle))
    (hOutgoingBranch : 0 ≤ outgoingPolarAngle ∧ outgoingPolarAngle ≤ Real.pi) :
    outgoingPolarAngle = Real.arccos (1 / eccentricity) := by
  have hEccentricity_ne : eccentricity ≠ 0 := ne_of_gt (lt_trans zero_lt_one hEccentricity)
  have hDenom_ne :
      ∀ t, 1 - eccentricity * Real.cos (polarAngle t) ≠ 0 := by
    intro t hzero
    have hEq := hConic t
    rw [hzero, div_zero] at hEq
    linarith [hRadiusPositive t]
  have hDenom :
      ∀ t, 1 - eccentricity * Real.cos (polarAngle t) =
        conicParameter * (radius t)⁻¹ := by
    intro t
    have hRadius_ne : radius t ≠ 0 := ne_of_gt (hRadiusPositive t)
    have hEq := hConic t
    field_simp [hDenom_ne t, hRadius_ne] at hEq ⊢
    nlinarith
  have hCosLimit :
      Tendsto (fun t => Real.cos (polarAngle t)) atTop
        (nhds (Real.cos outgoingPolarAngle)) :=
    Real.continuous_cos.continuousAt.tendsto.comp hAngleLimit
  have hDenomLimit :
      Tendsto (fun t => 1 - eccentricity * Real.cos (polarAngle t)) atTop
        (nhds (1 - eccentricity * Real.cos outgoingPolarAngle)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hCosLimit)
  have hInvRadiusLimit :
      Tendsto (fun t => (radius t)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hRadiusLimit
  have hDenomZero :
      Tendsto (fun t => 1 - eccentricity * Real.cos (polarAngle t)) atTop
        (nhds 0) := by
    have hProductZero :
        Tendsto (fun t => conicParameter * (radius t)⁻¹) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hInvRadiusLimit
    exact hProductZero.congr'
      (Filter.Eventually.of_forall fun t => (hDenom t).symm)
  have hLimitEq :
      1 - eccentricity * Real.cos outgoingPolarAngle = 0 :=
    tendsto_nhds_unique hDenomLimit hDenomZero
  have hCosEq : Real.cos outgoingPolarAngle = 1 / eccentricity := by
    field_simp [hEccentricity_ne]
    nlinarith
  calc
    outgoingPolarAngle = Real.arccos (Real.cos outgoingPolarAngle) :=
      (Real.arccos_cos hOutgoingBranch.1 hOutgoingBranch.2).symm
    _ = Real.arccos (1 / eccentricity) := congrArg Real.arccos hCosEq

/--
The source constants, initial angular momentum, energy relation, and supplied
eccentricity formula give eccentricity `7/2` when `μ = 15/2`.
-/
theorem eccentricity_at_mu_fifteen_halves
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    S.eccentricity = 7 / 2 := by
  let m := particleMassReadout S
  let q := chargeMagnitudeReadout S
  let hb := hbarReadout S
  let eps := vacuumPermittivityReadout S
  let k := coulombConstantReadout S
  let a₀ := bohrRadiusReadout S
  let r₀ := initialSeparationReadout S
  let v := S.initialParticleSpeed
  let L := totalAngularMomentumReadout S
  let E := totalEnergyReadout S
  have hm : 0 < m := by simpa [m] using h.particleMass_pos
  have hq : 0 < q := by simpa [q] using h.chargeMagnitude_pos
  have hhb : 0 < hb := by simpa [hb] using h.hbar_pos
  have heps : 0 < eps := by simpa [eps] using h.vacuumPermittivity_pos
  have hk : 0 < k := by simpa [k] using h.coulombConstant_pos
  have ha₀ : 0 < a₀ := by simpa [a₀] using h.bohrRadius_pos
  have hv : 0 < v := by simpa [v] using h.initialParticleSpeed_pos
  have hk_def : k = 1 / (4 * Real.pi * eps) := by
    simpa [k, eps] using h.coulomb_constant_definition
  have ha₀_def : a₀ = 4 * Real.pi * eps * hb ^ 2 / (m * q ^ 2) := by
    simpa [a₀, eps, hb, m, q] using h.bohr_radius_definition
  have hr₀ : r₀ = 100 * a₀ := by
    simpa [r₀, a₀] using h.initial_separation_value
  have hμ : S.mu = 15 / 2 := h.mu_value
  have hfundamental : m * k * q ^ 2 * a₀ = hb ^ 2 := by
    rw [hk_def, ha₀_def]
    field_simp [ne_of_gt hm, ne_of_gt hq, ne_of_gt hhb, ne_of_gt heps,
      Real.pi_ne_zero]
  have hangular :
      m * (r₀ / 2) * v = S.mu * hb := by
    simpa [m, r₀, v, hb] using h.each_particle_angular_momentum
  have hvelocity : 20 * m * a₀ * v = 3 * hb := by
    rw [hr₀, hμ] at hangular
    norm_num at hangular ⊢
    nlinarith
  have hvelocity_sq := congrArg (fun x : ℝ => x ^ 2) hvelocity
  have hL : L = 15 * hb := by
    have hL' := h.total_angular_momentum
    rw [hμ] at hL'
    norm_num [L, hb] at hL' ⊢
    exact hL'
  have henergy :
      E = m * v ^ 2 - k * q ^ 2 / r₀ := by
    simpa [E, m, v, k, q, r₀] using h.total_energy_from_initial_data
  rw [hr₀] at henergy
  have henergy_clear :
      100 * a₀ * E = 100 * a₀ * m * v ^ 2 - k * q ^ 2 := by
    field_simp [ne_of_gt ha₀] at henergy
    nlinarith
  have henergy_scaled :=
    congrArg (fun x : ℝ => 4 * m * a₀ * x) henergy_clear
  have hE : 80 * m * a₀ ^ 2 * E = hb ^ 2 := by
    ring_nf at hvelocity_sq henergy_scaled hfundamental ⊢
    nlinarith [hvelocity_sq, henergy_scaled, hfundamental]
  have hfundamental_sq :=
    congrArg (fun x : ℝ => x ^ 2) hfundamental
  have hE_hb_sq :=
    congrArg (fun x : ℝ => x * hb ^ 2) hE
  have hratio : 80 * E * hb ^ 2 = m * k ^ 2 * q ^ 4 := by
    apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt hm) (pow_ne_zero 2 (ne_of_gt ha₀)))
    ring_nf at hE_hb_sq hfundamental_sq ⊢
    nlinarith [hE_hb_sq, hfundamental_sq]
  have hradicand :
      1 + 4 * L ^ 2 * E / (k ^ 2 * q ^ 4 * m) = 49 / 4 := by
    rw [hL]
    field_simp [ne_of_gt hm, ne_of_gt hq, ne_of_gt hk]
    ring_nf at hratio ⊢
    linear_combination 45 * hratio
  rw [h.eccentricity_hint, show
    1 + 4 * totalAngularMomentumReadout S ^ 2 * totalEnergyReadout S /
      (coulombConstantReadout S ^ 2 * chargeMagnitudeReadout S ^ 4 *
        particleMassReadout S) = 49 / 4 by
          simpa [L, E, k, q, m] using hradicand]
  rw [show (49 / 4 : ℝ) = (7 / 2) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

/-- The outgoing branch therefore has polar angle `arccos (2/7)`. -/
theorem outgoing_polar_angle_at_mu_fifteen_halves
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    S.outgoingPolarAngle = Real.arccos (2 / 7) := by
  have hecc : S.eccentricity = 7 / 2 :=
    eccentricity_at_mu_fifteen_halves S h
  have hradius : ∀ t, 0 < separationRadius S t := by
    intro t
    exact norm_pos_iff.mpr (h.no_collision t)
  have hangle :=
    outgoing_polar_angle_of_hyperbolic_conic
      S.eccentricity (polarConicParameterReadout S)
      (separationRadius S) S.conicAngle S.outgoingPolarAngle
      (by rw [hecc]; norm_num)
      h.polar_conic_parameter_pos hradius h.polar_conic_hint
      h.unbound_separation_limit h.outgoing_conic_angle_limit
      ⟨h.outgoing_angle_range.1.le, h.outgoing_angle_range.2.le⟩
  rw [hecc] at hangle
  norm_num at hangle ⊢
  exact hangle

/--
Fig. 1b puts the initial positron velocity along the positive horizontal axis,
while the conic's polar zero-axis points downward.  The radial outgoing limit
therefore converts polar angle `θ∞` into signed deflection `θ∞ - π/2`.
-/
theorem fig1b_signed_deflection_from_polar_angle
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    signedDeflectionRadians S = S.outgoingPolarAngle - Real.pi / 2 := by
  set_option maxHeartbeats 1000000 in
    have hright : rightward ≠ 0 := by
      intro hzero
      have hcomponent := congrArg (fun x : Plane => x 0) hzero
      norm_num [rightward] at hcomponent
    have hup : upward ≠ 0 := by
      intro hzero
      have hcomponent := congrArg (fun x : Plane => x 1) hzero
      norm_num [upward] at hcomponent
    have hradius : ∀ t, 0 < separationRadius S t := by
      intro t
      exact norm_pos_iff.mpr (h.no_collision t)
    have hasymp_norm : 0 < ‖S.asymptoticRelativeVelocity‖ :=
      norm_pos_iff.mpr h.asymptotic_relative_velocity_ne_zero
    have hnormalized_asymp :
        ‖S.asymptoticRelativeVelocity‖⁻¹ • S.asymptoticRelativeVelocity ≠ 0 :=
      smul_ne_zero (inv_ne_zero (ne_of_gt hasymp_norm))
        h.asymptotic_relative_velocity_ne_zero
    have hpolar_angle :
        ∀ t,
          S.screenOrientation.oangle (-upward)
              ((separationRadius S t)⁻¹ • separationVector S t) =
            (S.conicAngle t : Real.Angle) := by
      intro t
      calc
        S.screenOrientation.oangle (-upward)
            ((separationRadius S t)⁻¹ • separationVector S t) =
            S.screenOrientation.oangle (-upward) (separationVector S t) :=
          S.screenOrientation.oangle_smul_right_of_pos _ _
            (inv_pos.mpr (hradius t))
        _ = ((S.screenOrientation.oangle (-upward)
            (separationVector S t)).toReal : Real.Angle) :=
          (Real.Angle.coe_toReal _).symm
        _ = (S.conicAngle t : Real.Angle) :=
          congrArg (fun x : ℝ => (x : Real.Angle))
            (h.conic_angle_matches_position t)
    have hcoerced_angle_limit :
        Tendsto (fun t => (S.conicAngle t : Real.Angle)) atTop
          (nhds (S.outgoingPolarAngle : Real.Angle)) :=
      Real.Angle.continuous_coe.continuousAt.tendsto.comp
        h.outgoing_conic_angle_limit
    have hpolar_oangle_limit :
        Tendsto
          (fun t => S.screenOrientation.oangle (-upward)
            ((separationRadius S t)⁻¹ • separationVector S t))
          atTop (nhds (S.outgoingPolarAngle : Real.Angle)) :=
      hcoerced_angle_limit.congr'
        (Filter.Eventually.of_forall fun t => (hpolar_angle t).symm)
    have hnormalized_oangle_limit :
        Tendsto
          (fun t => S.screenOrientation.oangle (-upward)
            ((separationRadius S t)⁻¹ • separationVector S t))
          atTop
          (nhds (S.screenOrientation.oangle (-upward)
            (‖S.asymptoticRelativeVelocity‖⁻¹ •
              S.asymptoticRelativeVelocity))) := by
      have hpairs :
          Tendsto
            (fun t => (-upward,
              (separationRadius S t)⁻¹ • separationVector S t))
            atTop
            (nhds (-upward,
              ‖S.asymptoticRelativeVelocity‖⁻¹ •
                S.asymptoticRelativeVelocity)) :=
        by
          simpa only [nhds_prod_eq] using
            ((tendsto_const_nhds :
              Tendsto (fun _ : ℝ => -upward) atTop (nhds (-upward))).prodMk
                h.outgoing_velocity_is_radial)
      have hcontinuous :
          ContinuousAt
            (fun p : Plane × Plane =>
              S.screenOrientation.oangle p.1 p.2)
            (-upward,
              ‖S.asymptoticRelativeVelocity‖⁻¹ •
                S.asymptoticRelativeVelocity) :=
        S.screenOrientation.continuousAt_oangle
          (neg_ne_zero.mpr hup) hnormalized_asymp
      have hraw_limit := hcontinuous.tendsto.comp hpairs
      simpa only [Function.comp_def] using hraw_limit
    have houtgoing_angle :
        (S.outgoingPolarAngle : Real.Angle) =
          S.screenOrientation.oangle (-upward)
            (‖S.asymptoticRelativeVelocity‖⁻¹ •
              S.asymptoticRelativeVelocity) :=
      tendsto_nhds_unique hpolar_oangle_limit hnormalized_oangle_limit
    have horientation :
        S.screenOrientation.oangle rightward upward =
          (Real.pi / 2 : ℝ) :=
      Real.Angle.toReal_eq_pi_div_two_iff.mp
        h.fig1b_counterclockwise_orientation
    have hright_neg_up :
        S.screenOrientation.oangle rightward (-upward) =
          (-Real.pi / 2 : ℝ) := by
      rw [S.screenOrientation.oangle_neg_right hright hup, horientation,
        ← Real.Angle.sub_coe_pi_eq_add_coe_pi, ← Real.Angle.coe_sub]
      congr 1
      ring
    have hright_normalized :
        S.screenOrientation.oangle rightward
            (‖S.asymptoticRelativeVelocity‖⁻¹ •
              S.asymptoticRelativeVelocity) =
          (S.outgoingPolarAngle - Real.pi / 2 : ℝ) := by
      calc
        S.screenOrientation.oangle rightward
            (‖S.asymptoticRelativeVelocity‖⁻¹ •
              S.asymptoticRelativeVelocity) =
            S.screenOrientation.oangle rightward (-upward) +
              S.screenOrientation.oangle (-upward)
                (‖S.asymptoticRelativeVelocity‖⁻¹ •
                  S.asymptoticRelativeVelocity) :=
          (S.screenOrientation.oangle_add hright (neg_ne_zero.mpr hup)
            hnormalized_asymp).symm
        _ = ((-Real.pi / 2 : ℝ) : Real.Angle) +
            (S.outgoingPolarAngle : Real.Angle) := by
          rw [hright_neg_up, ← houtgoing_angle]
        _ = (S.outgoingPolarAngle - Real.pi / 2 : ℝ) := by
          rw [← Real.Angle.coe_add]
          congr 1
          ring
    have hright_asymp :
        S.screenOrientation.oangle rightward S.asymptoticRelativeVelocity =
          (S.outgoingPolarAngle - Real.pi / 2 : ℝ) := by
      rw [← S.screenOrientation.oangle_smul_right_of_pos rightward
        S.asymptoticRelativeVelocity (inv_pos.mpr hasymp_norm)]
      exact hright_normalized
    unfold signedDeflectionRadians
    rw [h.fig1b_positron_velocity,
      S.screenOrientation.oangle_smul_left_of_pos _ _
        h.initialParticleSpeed_pos,
      hright_asymp]
    exact Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [h.outgoing_angle_range.1, Real.pi_pos],
        by linarith [h.outgoing_angle_range.2, Real.pi_pos]⟩

/--
For `μ = 15/2`, the outgoing relative velocity is deflected clockwise, below
the initial positron line.  The last conjunct is a rounding certificate:
the signed angle in degrees rounds to `-16.60°` to two decimal places.
-/
theorem asymptotic_relative_velocity_angle
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    signedDeflectionRadians S =
        Real.arccos (2 / 7) - Real.pi / 2 ∧
      signedDeflectionRadians S < 0 ∧
      |radiansToDegrees (signedDeflectionRadians S) + 83 / 5| < 1 / 200 := by
  have hpolar := outgoing_polar_angle_at_mu_fifteen_halves S h
  have hdeflection := fig1b_signed_deflection_from_polar_angle S h
  have hexact :
      signedDeflectionRadians S =
        Real.arccos (2 / 7) - Real.pi / 2 := by
    rw [hdeflection, hpolar]
  refine ⟨hexact, ?_, ?_⟩
  · rw [hexact]
    linarith [Real.arccos_lt_pi_div_two.mpr (by norm_num : (0 : ℝ) < 2 / 7)]
  · let z : ℝ → ℝ := fun x => x / 4
    let err : ℝ → ℝ := fun x => z x ^ 4 * (5 / 96)
    let sl : ℝ → ℝ := fun x => z x - z x ^ 3 / 6 - err x
    let su : ℝ → ℝ := fun x => z x - z x ^ 3 / 6 + err x
    let cl : ℝ → ℝ := fun x => 1 - z x ^ 2 / 2 - err x
    let cu : ℝ → ℝ := fun x => 1 - z x ^ 2 / 2 + err x
    have sin_quarter_bounds
        (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
        (hsl0 : 0 ≤ sl x) (hsu0 : 0 ≤ su x)
        (hcl0 : 0 ≤ cl x) (hcu0 : 0 ≤ cu x)
        (hc2l0 : 0 ≤ 2 * cl x ^ 2 - 1) :
        2 * (2 * sl x * cl x) * (2 * cl x ^ 2 - 1) ≤ Real.sin x ∧
          Real.sin x ≤
            2 * (2 * su x * cu x) * (2 * cu x ^ 2 - 1) := by
      have hz0 : 0 < z x := by
        dsimp [z]
        positivity
      have hz1 : |z x| ≤ 1 := by
        rw [abs_of_pos hz0]
        dsimp [z]
        linarith
      have hsbound := abs_le.mp (Real.sin_bound hz1)
      have hcbound := abs_le.mp (Real.cos_bound hz1)
      rw [abs_of_pos hz0] at hsbound hcbound
      have hsl : sl x ≤ Real.sin (z x) := by
        dsimp [sl, err]
        linarith [hsbound.1]
      have hsu : Real.sin (z x) ≤ su x := by
        dsimp [su, err]
        linarith [hsbound.2]
      have hcl : cl x ≤ Real.cos (z x) := by
        dsimp [cl, err]
        linarith [hcbound.1]
      have hcu : Real.cos (z x) ≤ cu x := by
        dsimp [cu, err]
        linarith [hcbound.2]
      have hsinz0 : 0 ≤ Real.sin (z x) :=
        (Real.sin_pos_of_pos_of_le_one hz0 (by
          rw [abs_of_pos hz0] at hz1
          exact hz1)).le
      have hcosz0 : 0 ≤ Real.cos (z x) :=
        (Real.cos_pos_of_le_one hz1).le
      have hs2l :
          2 * sl x * cl x ≤ Real.sin (2 * z x) := by
        rw [Real.sin_two_mul]
        gcongr
      have hs2u :
          Real.sin (2 * z x) ≤ 2 * su x * cu x := by
        rw [Real.sin_two_mul]
        gcongr
      have hcl_sq : cl x ^ 2 ≤ Real.cos (z x) ^ 2 :=
        pow_le_pow_left₀ hcl0 hcl 2
      have hcu_sq : Real.cos (z x) ^ 2 ≤ cu x ^ 2 :=
        pow_le_pow_left₀ hcosz0 hcu 2
      have hc2l :
          2 * cl x ^ 2 - 1 ≤ Real.cos (2 * z x) := by
        rw [Real.cos_two_mul]
        linarith
      have hc2u :
          Real.cos (2 * z x) ≤ 2 * cu x ^ 2 - 1 := by
        rw [Real.cos_two_mul]
        linarith
      have hsin2z0 : 0 ≤ Real.sin (2 * z x) := by
        have h2z0 : 0 < 2 * z x := mul_pos two_pos hz0
        exact (Real.sin_pos_of_pos_of_le_one h2z0 (by
          dsimp [z]
          linarith)).le
      have hcos2z0 : 0 ≤ Real.cos (2 * z x) := by
        exact (Real.cos_pos_of_le_one (by
          rw [abs_of_pos (mul_pos two_pos hz0)]
          dsimp [z]
          linarith)).le
      have hxangle : x = 2 * (2 * z x) := by
        dsimp [z]
        ring
      have hsin_double :
          Real.sin x =
            2 * Real.sin (2 * z x) * Real.cos (2 * z x) := by
        calc
          Real.sin x = Real.sin (2 * (2 * z x)) :=
            congrArg Real.sin hxangle
          _ = 2 * Real.sin (2 * z x) * Real.cos (2 * z x) :=
            Real.sin_two_mul (2 * z x)
      constructor
      · calc
          2 * (2 * sl x * cl x) * (2 * cl x ^ 2 - 1) ≤
              2 * Real.sin (2 * z x) * Real.cos (2 * z x) := by
                gcongr
          _ = Real.sin x := hsin_double.symm
      · calc
          Real.sin x =
              2 * Real.sin (2 * z x) * Real.cos (2 * z x) := hsin_double
          _ ≤ 2 * (2 * su x * cu x) * (2 * cu x ^ 2 - 1) := by
                gcongr
    have hsin_lower :
        Real.sin (3319 * Real.pi / 36000) < 2 / 7 := by
      have harg :
          3319 * Real.pi / 36000 < (289638 : ℝ) / 1000000 := by
        nlinarith [Real.pi_lt_d20]
      have hmono :
          Real.sin (3319 * Real.pi / 36000) ≤
            Real.sin ((289638 : ℝ) / 1000000) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.two_le_pi]
        · exact harg.le
      have hb := sin_quarter_bounds ((289638 : ℝ) / 1000000)
        (by norm_num) (by norm_num)
        (by norm_num [sl, err, z]) (by norm_num [su, err, z])
        (by norm_num [cl, err, z]) (by norm_num [cu, err, z])
        (by norm_num [cl, err, z])
      have hnumeric :
          Real.sin ((289638 : ℝ) / 1000000) < 2 / 7 := by
        calc
          Real.sin ((289638 : ℝ) / 1000000) ≤
              2 * (2 * su ((289638 : ℝ) / 1000000) *
                cu ((289638 : ℝ) / 1000000)) *
                (2 * cu ((289638 : ℝ) / 1000000) ^ 2 - 1) := hb.2
          _ < 2 / 7 := by norm_num [su, cu, err, z]
      exact hmono.trans_lt hnumeric
    have hsin_upper :
        2 / 7 < Real.sin (3321 * Real.pi / 36000) := by
      have harg :
          (289811 : ℝ) / 1000000 < 3321 * Real.pi / 36000 := by
        nlinarith [Real.pi_gt_d20]
      have hmono :
          Real.sin ((289811 : ℝ) / 1000000) ≤
            Real.sin (3321 * Real.pi / 36000) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
        · exact harg.le
      have hb := sin_quarter_bounds ((289811 : ℝ) / 1000000)
        (by norm_num) (by norm_num)
        (by norm_num [sl, err, z]) (by norm_num [su, err, z])
        (by norm_num [cl, err, z]) (by norm_num [cu, err, z])
        (by norm_num [cl, err, z])
      have hnumeric :
          2 / 7 < Real.sin ((289811 : ℝ) / 1000000) := by
        calc
          2 / 7 <
              2 * (2 * sl ((289811 : ℝ) / 1000000) *
                cl ((289811 : ℝ) / 1000000)) *
                (2 * cl ((289811 : ℝ) / 1000000) ^ 2 - 1) := by
                  norm_num [sl, cl, err, z]
          _ ≤ Real.sin ((289811 : ℝ) / 1000000) := hb.1
      exact hnumeric.trans_le hmono
    have harcsin_lower :
        3319 * Real.pi / 36000 < Real.arcsin (2 / 7) := by
      refine (Real.lt_arcsin_iff_sin_lt
        (x := 3319 * Real.pi / 36000) (y := 2 / 7) ?_ ?_).mpr ?_
      · constructor <;> nlinarith [Real.pi_pos, Real.pi_lt_d20]
      · norm_num
      · exact hsin_lower
    have harcsin_upper :
        Real.arcsin (2 / 7) < 3321 * Real.pi / 36000 := by
      refine (Real.arcsin_lt_iff_lt_sin
        (x := 2 / 7) (y := 3321 * Real.pi / 36000) ?_ ?_).mpr ?_
      · norm_num
      · constructor <;> nlinarith [Real.pi_pos, Real.pi_lt_d20]
      · exact hsin_upper
    rw [hexact, Real.arccos_eq_pi_div_two_sub_arcsin]
    unfold radiansToDegrees
    rw [abs_lt]
    constructor <;>
      field_simp [Real.pi_ne_zero] <;>
      nlinarith [Real.pi_pos, harcsin_lower, harcsin_upper]

end IPhO2026_1_B_2
