import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026, problem 1, part B.2

This file models the classical electron--positron Coulomb-scattering problem
shown in Figure 1b. Physical quantities are represented by Physlib
`Dimensionful (WithDim ...)` types; real numbers occur only as explicit SI
readouts, dimensionless parameters, time-in-seconds coordinates, or angles.

The supplied eccentricity and polar-conic formulas are recorded as governing
laws. The requested signed asymptotic deflection is only a theorem conclusion.
-/

noncomputable section

open Dimension Filter
open scoped RealInnerProductSpace Topology

namespace IPhO2026Problems.IPhO2026_1_B_2

/-! ## Dimension-carrying quantities -/

/-- The oriented two-dimensional plane containing the trajectories in Figure 1b. -/
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- The standard plane has real dimension two, as required by the oriented-angle API. -/
local instance planeFinrankTwo : Fact (Module.finrank ℝ Plane = 2) :=
  ⟨by simp [Plane]⟩

/-- Velocity dimension `L T⁻¹`. -/
def velocityDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- Angular-momentum/action dimension `M L² T⁻¹`. -/
def angularMomentumDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- Vacuum-permittivity dimension `C² T² M⁻¹ L⁻³`. -/
def permittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- Coulomb-constant dimension `M L³ T⁻² C⁻²`. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

abbrev DimLength : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

abbrev DimMass : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

abbrev DimCharge : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

abbrev DimPosition : Type :=
  Dimensionful (WithDim L𝓭 Plane)

abbrev DimVelocityVector : Type :=
  Dimensionful (WithDim velocityDimension Plane)

abbrev DimSpeed : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

abbrev DimAngularMomentum : Type :=
  Dimensionful (WithDim angularMomentumDimension ℝ)

abbrev DimPermittivity : Type :=
  Dimensionful (WithDim permittivityDimension ℝ)

abbrev DimCoulombConstant : Type :=
  Dimensionful (WithDim coulombConstantDimension ℝ)

/-- The scalar SI readout of a dimensionful scalar quantity. -/
def scalarSI {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity.1 UnitChoices.SI).val

/-- The component vector in the standard SI units for its dimension. -/
def vectorSI {d : Dimension}
    (quantity : Dimensionful (WithDim d Plane)) : Plane :=
  (quantity.1 UnitChoices.SI).val

/-! ## Particles, constants, and Figure 1b -/

/-- The two labeled particles in Figure 1b. -/
inductive ParticleLabel where
  | positron
  | electron
deriving DecidableEq

/--
The universal constants and common particle mass used in the problem.
`elementaryChargeMagnitude` is positive; the signs of the two particles are
specified separately in `Figure1bInitialConditions`.
-/
structure PhysicalConstants where
  particleMass_m : DimMass
  elementaryChargeMagnitude_e : DimCharge
  reducedPlanckConstant_hbar : DimAngularMomentum
  vacuumPermittivity_epsilon0 : DimPermittivity
  bohrRadius_a0 : DimLength
  coulombConstant_k : DimCoulombConstant
  speedOfLight_c : DimSpeed
  particleMass_positive : 0 < scalarSI particleMass_m
  elementaryCharge_positive : 0 < scalarSI elementaryChargeMagnitude_e
  hbar_positive : 0 < scalarSI reducedPlanckConstant_hbar
  vacuumPermittivity_positive : 0 < scalarSI vacuumPermittivity_epsilon0
  bohrRadius_positive : 0 < scalarSI bohrRadius_a0
  coulombConstant_positive : 0 < scalarSI coulombConstant_k
  speedOfLight_positive : 0 < scalarSI speedOfLight_c

/--
The two constant identities printed on the source page:
`a₀ = 4 π ε₀ ℏ² / (m e²)` and `k = 1 / (4 π ε₀)`.
-/
structure ConstantRelations (constants : PhysicalConstants) : Prop where
  bohrRadius_formula :
    scalarSI constants.bohrRadius_a0 =
      4 * Real.pi * scalarSI constants.vacuumPermittivity_epsilon0 *
          scalarSI constants.reducedPlanckConstant_hbar ^ 2 /
        (scalarSI constants.particleMass_m *
          scalarSI constants.elementaryChargeMagnitude_e ^ 2)
  coulombConstant_formula :
    scalarSI constants.coulombConstant_k =
      1 / (4 * Real.pi * scalarSI constants.vacuumPermittivity_epsilon0)

/--
The dimensionful positions and velocities of both particles. The real
argument is the time readout in seconds, with the pictured instant at `0`.
-/
structure PairMotion where
  mass : ParticleLabel → DimMass
  charge : ParticleLabel → DimCharge
  position : ParticleLabel → ℝ → DimPosition
  velocity : ParticleLabel → ℝ → DimVelocityVector

/-- SI position vector of a labeled particle at the specified time in seconds. -/
def positionSI
    (motion : PairMotion) (particle : ParticleLabel) (seconds : ℝ) : Plane :=
  vectorSI (motion.position particle seconds)

/-- SI velocity vector of a labeled particle at the specified time in seconds. -/
def velocitySI
    (motion : PairMotion) (particle : ParticleLabel) (seconds : ℝ) : Plane :=
  vectorSI (motion.velocity particle seconds)

/-- SI mass readout of a labeled particle. -/
def particleMassSI (motion : PairMotion) (particle : ParticleLabel) : ℝ :=
  scalarSI (motion.mass particle)

/-- SI charge readout of a labeled particle. -/
def particleChargeSI (motion : PairMotion) (particle : ParticleLabel) : ℝ :=
  scalarSI (motion.charge particle)

/-- Relative displacement from the electron to the positron, in metres. -/
def relativeDisplacementSI (motion : PairMotion) (seconds : ℝ) : Plane :=
  positionSI motion .positron seconds - positionSI motion .electron seconds

/-- Positron velocity relative to the electron, in metres per second. -/
def relativeVelocitySI (motion : PairMotion) (seconds : ℝ) : Plane :=
  velocitySI motion .positron seconds - velocitySI motion .electron seconds

/-- Electron--positron separation in metres. -/
def separationSI (motion : PairMotion) (seconds : ℝ) : ℝ :=
  ‖relativeDisplacementSI motion seconds‖

/--
The oriented axes read from Figure 1b. `initialPositronDirection` points right,
and `electronToPositronDirection` points upward from `e⁻` to `e⁺`.
-/
structure Figure1bFrame where
  orientation : Orientation ℝ Plane (Fin 2)
  initialPositronDirection : Plane
  electronToPositronDirection : Plane
  initialDirection_unit : ‖initialPositronDirection‖ = 1
  separationDirection_unit : ‖electronToPositronDirection‖ = 1
  positiveQuarterTurn :
    orientation.oangle initialPositronDirection electronToPositronDirection =
      ((Real.pi / 2 : ℝ) : Real.Angle)

/-- Signed angular momentum of one particle about a chosen center, in SI units. -/
def signedAngularMomentumSI
    (motion : PairMotion) (frame : Figure1bFrame)
    (centerOfMass : DimPosition) (particle : ParticleLabel) : ℝ :=
  particleMassSI motion particle *
    frame.orientation.areaForm
      (positionSI motion particle 0 - vectorSI centerOfMass)
      (velocitySI motion particle 0)

/-- Magnitude of the pair's total angular momentum about the center of mass. -/
def totalAngularMomentumMagnitudeSI
    (motion : PairMotion) (frame : Figure1bFrame)
    (centerOfMass : DimPosition) : ℝ :=
  |signedAngularMomentumSI motion frame centerOfMass .positron +
    signedAngularMomentumSI motion frame centerOfMass .electron|

/--
All numerical and geometric data at the pictured instant. These fields encode
equal masses, opposite elementary charges, vertical separation `100 a₀`,
antiparallel transverse velocities, and individual angular-momentum magnitude
`μ ℏ` with `μ = 15/2`.
-/
structure Figure1bInitialConditions
    (constants : PhysicalConstants) (motion : PairMotion)
    (frame : Figure1bFrame) where
  centerOfMass : DimPosition
  initialParticleSpeed : DimSpeed
  mu : ℝ
  initialParticleSpeed_positive : 0 < scalarSI initialParticleSpeed
  mu_value : mu = (15 : ℝ) / 2
  positronMass :
    particleMassSI motion .positron = scalarSI constants.particleMass_m
  electronMass :
    particleMassSI motion .electron = scalarSI constants.particleMass_m
  positronCharge :
    particleChargeSI motion .positron =
      scalarSI constants.elementaryChargeMagnitude_e
  electronCharge :
    particleChargeSI motion .electron =
      -scalarSI constants.elementaryChargeMagnitude_e
  centerOfMass_midpoint :
    positionSI motion .positron 0 + positionSI motion .electron 0 =
      (2 : ℝ) • vectorSI centerOfMass
  initialSeparation :
    relativeDisplacementSI motion 0 =
      (100 * scalarSI constants.bohrRadius_a0) •
        frame.electronToPositronDirection
  positronInitialVelocity :
    velocitySI motion .positron 0 =
      scalarSI initialParticleSpeed • frame.initialPositronDirection
  electronInitialVelocity :
    velocitySI motion .electron 0 =
      (-scalarSI initialParticleSpeed) • frame.initialPositronDirection
  positronAngularMomentumMagnitude :
    |signedAngularMomentumSI motion frame centerOfMass .positron| =
      mu * scalarSI constants.reducedPlanckConstant_hbar
  electronAngularMomentumMagnitude :
    |signedAngularMomentumSI motion frame centerOfMass .electron| =
      mu * scalarSI constants.reducedPlanckConstant_hbar

/-! ## Classical isolated Coulomb dynamics -/

/-- Coulomb force on the positron, evaluated in SI components. -/
def coulombForceOnPositronSI
    (constants : PhysicalConstants) (motion : PairMotion)
    (seconds : ℝ) : Plane :=
  ((scalarSI constants.coulombConstant_k *
        particleChargeSI motion .positron *
        particleChargeSI motion .electron) /
      ‖relativeDisplacementSI motion seconds‖ ^ 3) •
    relativeDisplacementSI motion seconds

/--
The classical non-relativistic, isolated two-body model.

The kinematic derivative identifies the velocity fields. The two acceleration
equations are Newton's second law with equal-and-opposite Coulomb forces, so no
external force or non-electrostatic interaction is present. The final field
states the non-relativistic speed regime.
-/
structure CoulombDynamics
    (constants : PhysicalConstants) (motion : PairMotion) : Prop where
  noCollision :
    ∀ seconds : ℝ, relativeDisplacementSI motion seconds ≠ 0
  positionDerivative :
    ∀ (particle : ParticleLabel) (seconds : ℝ),
      HasDerivAt
        (fun time => positionSI motion particle time)
        (velocitySI motion particle seconds)
        seconds
  newtonCoulomb :
    ∀ seconds : ℝ, ∃ positronAcceleration electronAcceleration : Plane,
      HasDerivAt
          (fun time => velocitySI motion .positron time)
          positronAcceleration seconds ∧
        HasDerivAt
          (fun time => velocitySI motion .electron time)
          electronAcceleration seconds ∧
        particleMassSI motion .positron • positronAcceleration =
          coulombForceOnPositronSI constants motion seconds ∧
        particleMassSI motion .electron • electronAcceleration =
          -coulombForceOnPositronSI constants motion seconds
  nonrelativistic :
    ∀ (particle : ParticleLabel) (seconds : ℝ),
      ‖velocitySI motion particle seconds‖ <
        scalarSI constants.speedOfLight_c

/-- Total mechanical energy computed at the pictured instant, in joules. -/
def initialTotalEnergySI
    (constants : PhysicalConstants) (motion : PairMotion) : ℝ :=
  (1 / 2 : ℝ) * particleMassSI motion .positron *
      ‖velocitySI motion .positron 0‖ ^ 2 +
    (1 / 2 : ℝ) * particleMassSI motion .electron *
      ‖velocitySI motion .electron 0‖ ^ 2 +
    scalarSI constants.coulombConstant_k *
      particleChargeSI motion .positron *
      particleChargeSI motion .electron /
        separationSI motion 0

/--
Data used by the two conic-orbit hints on the official source page.
`semiLatusRectum_a` is the length denoted `a` in the printed polar equation.
-/
structure ConicOrbitData where
  totalEnergy_E : DimEnergy
  totalAngularMomentumMagnitude_L : DimAngularMomentum
  eccentricity : ℝ
  semiLatusRectum_a : DimLength
  periapsisAxis : Plane
  polarAngleRad : ℝ → ℝ

/--
The supplied Kepler/Coulomb eccentricity law and polar conic equation.
Neither field contains the requested asymptotic deflection.
-/
structure ConicOrbitLaws
    (constants : PhysicalConstants) (motion : PairMotion)
    (frame : Figure1bFrame)
    (initial : Figure1bInitialConditions constants motion frame)
    (orbit : ConicOrbitData) : Prop where
  energyMatchesInitialState :
    scalarSI orbit.totalEnergy_E = initialTotalEnergySI constants motion
  angularMomentumMatchesInitialState :
    scalarSI orbit.totalAngularMomentumMagnitude_L =
      totalAngularMomentumMagnitudeSI motion frame initial.centerOfMass
  eccentricityFormula :
    orbit.eccentricity =
      Real.sqrt
        (1 +
          4 * scalarSI orbit.totalAngularMomentumMagnitude_L ^ 2 *
              scalarSI orbit.totalEnergy_E /
            (scalarSI constants.coulombConstant_k ^ 2 *
              scalarSI constants.elementaryChargeMagnitude_e ^ 4 *
              scalarSI constants.particleMass_m))
  hyperbolicEccentricity : 1 < orbit.eccentricity
  semiLatusRectum_positive : 0 < scalarSI orbit.semiLatusRectum_a
  periapsisAxis_unit : ‖orbit.periapsisAxis‖ = 1
  polarAngleDefinition :
    ∀ seconds : ℝ,
      frame.orientation.oangle
          orbit.periapsisAxis (relativeDisplacementSI motion seconds) =
        ((orbit.polarAngleRad seconds : ℝ) : Real.Angle)
  polarConicEquation :
    ∀ seconds : ℝ,
      separationSI motion seconds =
        scalarSI orbit.semiLatusRectum_a /
          (1 - orbit.eccentricity * Real.cos (orbit.polarAngleRad seconds))

/-- The stated unbound condition: the separation tends to infinity in the future. -/
def IsUnbound (motion : PairMotion) : Prop :=
  Tendsto (separationSI motion) atTop atTop

/-! ## Current B.2 target -/

/--
The signed counterclockwise angle from the initial positron velocity to the
asymptotic positron-relative-to-electron velocity, reported in degrees.
-/
def signedDeflectionDegrees
    (motion : PairMotion) (frame : Figure1bFrame)
    (uInfinity : Plane) : ℝ :=
  (frame.orientation.oangle
      (velocitySI motion .positron 0) uInfinity).toReal *
    180 / Real.pi

/--
`actual` rounds to `reported` at two digits after the decimal point. The
half-unit tolerance is `0.005`.
-/
def RoundsToNearestHundredth (actual reported : ℝ) : Prop :=
  |actual - reported| ≤ (1 : ℝ) / 200

set_option maxHeartbeats 2000000 in
/--
IPhO 2026 Problem 1 B.2: the outgoing relative velocity is directed
`16.60°` below the initial positron line of motion.

The hypotheses assigning `uInfinity` its limiting-velocity role contain no
information about its direction. The negative sign and the numerical
deflection occur only in this conclusion.
-/
theorem IPhO_2026_1_B_2
    (constants : PhysicalConstants)
    (constantRelations : ConstantRelations constants)
    (motion : PairMotion)
    (frame : Figure1bFrame)
    (initial : Figure1bInitialConditions constants motion frame)
    (dynamics : CoulombDynamics constants motion)
    (orbit : ConicOrbitData)
    (orbitLaws : ConicOrbitLaws constants motion frame initial orbit)
    (uInfinity : Plane)
    (unbound : IsUnbound motion)
    (uInfinity_nonzero : uInfinity ≠ 0)
    (uInfinity_isAsymptoticRelativeVelocity :
      Tendsto (relativeVelocitySI motion) atTop (𝓝 uInfinity)) :
    signedDeflectionDegrees motion frame uInfinity < 0 ∧
      RoundsToNearestHundredth
        (signedDeflectionDegrees motion frame uInfinity)
        (-(83 : ℝ) / 5) := by
  have mu_positive : 0 < initial.mu := by
    rw [initial.mu_value]
    norm_num
  have eccentricity_positive : 0 < orbit.eccentricity :=
    lt_trans (by norm_num) orbitLaws.hyperbolicEccentricity
  have separation_tends_to_infinity :
      Tendsto (separationSI motion) atTop atTop := by
    simpa [IsUnbound] using unbound
  have relative_velocity_tends_to_uInfinity :
      Tendsto (relativeVelocitySI motion) atTop (𝓝 uInfinity) :=
    uInfinity_isAsymptoticRelativeVelocity
  have separation_positive (seconds : ℝ) :
      0 < separationSI motion seconds := by
    exact norm_pos_iff.mpr (dynamics.noCollision seconds)
  have frame_directions_inner_zero :
      ⟪frame.initialPositronDirection,
        frame.electronToPositronDirection⟫ = 0 := by
    rw [frame.orientation.inner_eq_norm_mul_norm_mul_cos_oangle,
      frame.initialDirection_unit, frame.separationDirection_unit,
      frame.positiveQuarterTurn, Real.Angle.cos_coe]
    simp
  have frame_directions_area_abs :
      |frame.orientation.areaForm frame.initialPositronDirection
        frame.electronToPositronDirection| = 1 := by
    have hnorm :=
      frame.orientation.norm_kahler
        frame.initialPositronDirection frame.electronToPositronDirection
    rw [frame.initialDirection_unit, frame.separationDirection_unit,
      mul_one] at hnorm
    rw [frame.orientation.kahler_apply_apply,
      frame_directions_inner_zero] at hnorm
    simpa using hnorm
  have reversed_frame_directions_area_abs :
      |frame.orientation.areaForm frame.electronToPositronDirection
        frame.initialPositronDirection| = 1 := by
    rw [frame.orientation.areaForm_swap, abs_neg,
      frame_directions_area_abs]
  have positron_offset_eq_half_relative :
      positionSI motion .positron 0 - vectorSI initial.centerOfMass =
        (1 / 2 : ℝ) • relativeDisplacementSI motion 0 := by
    have hmid := initial.centerOfMass_midpoint
    rw [relativeDisplacementSI]
    calc
      positionSI motion .positron 0 - vectorSI initial.centerOfMass =
          positionSI motion .positron 0 -
            (1 / 2 : ℝ) •
              ((2 : ℝ) • vectorSI initial.centerOfMass) := by module
      _ = positionSI motion .positron 0 -
            (1 / 2 : ℝ) •
              (positionSI motion .positron 0 +
                positionSI motion .electron 0) := by rw [hmid]
      _ = (1 / 2 : ℝ) •
            (positionSI motion .positron 0 -
              positionSI motion .electron 0) := by module
  have electron_offset_eq_neg_half_relative :
      positionSI motion .electron 0 - vectorSI initial.centerOfMass =
        (-1 / 2 : ℝ) • relativeDisplacementSI motion 0 := by
    have hmid := initial.centerOfMass_midpoint
    rw [relativeDisplacementSI]
    calc
      positionSI motion .electron 0 - vectorSI initial.centerOfMass =
          positionSI motion .electron 0 -
            (1 / 2 : ℝ) •
              ((2 : ℝ) • vectorSI initial.centerOfMass) := by module
      _ = positionSI motion .electron 0 -
            (1 / 2 : ℝ) •
              (positionSI motion .positron 0 +
                positionSI motion .electron 0) := by rw [hmid]
      _ = (-1 / 2 : ℝ) •
            (positionSI motion .positron 0 -
              positionSI motion .electron 0) := by module
  have signed_angular_momenta_equal :
      signedAngularMomentumSI motion frame initial.centerOfMass .positron =
        signedAngularMomentumSI motion frame initial.centerOfMass .electron := by
    rw [signedAngularMomentumSI, signedAngularMomentumSI,
      initial.positronMass, initial.electronMass,
      positron_offset_eq_half_relative,
      electron_offset_eq_neg_half_relative,
      initial.positronInitialVelocity, initial.electronInitialVelocity]
    simp
    ring
  have positron_angular_momentum_abs_formula :
      |signedAngularMomentumSI
          motion frame initial.centerOfMass .positron| =
        50 * scalarSI constants.particleMass_m *
          scalarSI constants.bohrRadius_a0 *
          scalarSI initial.initialParticleSpeed := by
    rw [signedAngularMomentumSI, initial.positronMass,
      positron_offset_eq_half_relative, initial.initialSeparation,
      initial.positronInitialVelocity]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_pos constants.particleMass_positive,
      abs_of_pos
        (mul_pos (by norm_num : (0 : ℝ) < 100)
          constants.bohrRadius_positive),
      abs_of_pos initial.initialParticleSpeed_positive,
      reversed_frame_directions_area_abs]
    ring
  have total_angular_momentum_value :
      totalAngularMomentumMagnitudeSI
          motion frame initial.centerOfMass =
        2 * initial.mu *
          scalarSI constants.reducedPlanckConstant_hbar := by
    rw [totalAngularMomentumMagnitudeSI, signed_angular_momenta_equal,
      ← two_mul, abs_mul, abs_of_nonneg (by norm_num),
      initial.electronAngularMomentumMagnitude]
    ring
  have orbit_angular_momentum_value :
      scalarSI orbit.totalAngularMomentumMagnitude_L =
        2 * initial.mu *
          scalarSI constants.reducedPlanckConstant_hbar := by
    rw [orbitLaws.angularMomentumMatchesInitialState,
      total_angular_momentum_value]
  have speed_angular_momentum_relation :
      50 * scalarSI constants.particleMass_m *
          scalarSI constants.bohrRadius_a0 *
          scalarSI initial.initialParticleSpeed =
        initial.mu *
          scalarSI constants.reducedPlanckConstant_hbar := by
    rw [← positron_angular_momentum_abs_formula,
      initial.positronAngularMomentumMagnitude]
  have initial_speed_value :
      scalarSI initial.initialParticleSpeed =
        initial.mu *
            scalarSI constants.reducedPlanckConstant_hbar /
          (50 * scalarSI constants.particleMass_m *
            scalarSI constants.bohrRadius_a0) := by
    apply (eq_div_iff ?_).2
    · nlinarith [speed_angular_momentum_relation]
    · exact mul_ne_zero
        (mul_ne_zero (by norm_num)
          (ne_of_gt constants.particleMass_positive))
        (ne_of_gt constants.bohrRadius_positive)
  have bohr_coulomb_identity :
      scalarSI constants.particleMass_m *
          scalarSI constants.coulombConstant_k *
          scalarSI constants.elementaryChargeMagnitude_e ^ 2 *
          scalarSI constants.bohrRadius_a0 =
        scalarSI constants.reducedPlanckConstant_hbar ^ 2 := by
    rw [constantRelations.coulombConstant_formula,
      constantRelations.bohrRadius_formula]
    field_simp [ne_of_gt constants.particleMass_positive,
      ne_of_gt constants.elementaryCharge_positive,
      ne_of_gt constants.vacuumPermittivity_positive,
      Real.pi_ne_zero]
  have initial_separation_value :
      separationSI motion 0 =
        100 * scalarSI constants.bohrRadius_a0 := by
    rw [separationSI, initial.initialSeparation, norm_smul,
      frame.separationDirection_unit, mul_one, Real.norm_eq_abs,
      abs_of_pos
        (mul_pos (by norm_num : (0 : ℝ) < 100)
          constants.bohrRadius_positive)]
  have initial_positron_speed_norm :
      ‖velocitySI motion .positron 0‖ =
        scalarSI initial.initialParticleSpeed := by
    rw [initial.positronInitialVelocity, norm_smul,
      frame.initialDirection_unit, mul_one, Real.norm_eq_abs,
      abs_of_pos initial.initialParticleSpeed_positive]
  have initial_electron_speed_norm :
      ‖velocitySI motion .electron 0‖ =
        scalarSI initial.initialParticleSpeed := by
    rw [initial.electronInitialVelocity, norm_smul,
      frame.initialDirection_unit, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_pos initial.initialParticleSpeed_positive]
  have initial_energy_formula :
      initialTotalEnergySI constants motion =
        scalarSI constants.particleMass_m *
            scalarSI initial.initialParticleSpeed ^ 2 -
          scalarSI constants.coulombConstant_k *
              scalarSI constants.elementaryChargeMagnitude_e ^ 2 /
            (100 * scalarSI constants.bohrRadius_a0) := by
    rw [initialTotalEnergySI, initial.positronMass,
      initial.electronMass, initial_positron_speed_norm,
      initial_electron_speed_norm, initial.positronCharge,
      initial.electronCharge, initial_separation_value]
    ring
  have initial_energy_value :
      initialTotalEnergySI constants motion =
        scalarSI constants.coulombConstant_k *
            scalarSI constants.elementaryChargeMagnitude_e ^ 2 /
          (80 * scalarSI constants.bohrRadius_a0) := by
    rw [initial_energy_formula, initial_speed_value, initial.mu_value]
    have hm := ne_of_gt constants.particleMass_positive
    have ha := ne_of_gt constants.bohrRadius_positive
    field_simp [hm, ha]
    nlinarith [bohr_coulomb_identity]
  have orbit_energy_value :
      scalarSI orbit.totalEnergy_E =
        scalarSI constants.coulombConstant_k *
            scalarSI constants.elementaryChargeMagnitude_e ^ 2 /
          (80 * scalarSI constants.bohrRadius_a0) := by
    rw [orbitLaws.energyMatchesInitialState, initial_energy_value]
  have eccentricity_value :
      orbit.eccentricity = (7 : ℝ) / 2 := by
    rw [orbitLaws.eccentricityFormula,
      orbit_angular_momentum_value, orbit_energy_value,
      initial.mu_value]
    have hinside :
        1 +
            4 *
                (2 * ((15 : ℝ) / 2) *
                    scalarSI constants.reducedPlanckConstant_hbar) ^ 2 *
                (scalarSI constants.coulombConstant_k *
                    scalarSI constants.elementaryChargeMagnitude_e ^ 2 /
                  (80 * scalarSI constants.bohrRadius_a0)) /
              (scalarSI constants.coulombConstant_k ^ 2 *
                scalarSI constants.elementaryChargeMagnitude_e ^ 4 *
                scalarSI constants.particleMass_m) =
          (49 : ℝ) / 4 := by
      field_simp [ne_of_gt constants.particleMass_positive,
        ne_of_gt constants.elementaryCharge_positive,
        ne_of_gt constants.bohrRadius_positive,
        ne_of_gt constants.coulombConstant_positive]
      nlinarith [bohr_coulomb_identity]
    rw [hinside]
    rw [show (49 : ℝ) / 4 = ((7 : ℝ) / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have polar_angle_geometry := orbitLaws.polarAngleDefinition
  have polar_conic := orbitLaws.polarConicEquation
  have conic_denominator_positive (seconds : ℝ) :
      0 <
        1 - orbit.eccentricity *
          Real.cos (orbit.polarAngleRad seconds) := by
    have hsep := separation_positive seconds
    rw [polar_conic seconds] at hsep
    rcases (div_pos_iff.mp hsep) with hpos | hneg
    · exact hpos.2
    · exfalso
      linarith [orbitLaws.semiLatusRectum_positive]
  have periapsisAxis_ne_zero : orbit.periapsisAxis ≠ 0 := by
    intro hzero
    have hunit := orbitLaws.periapsisAxis_unit
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  have polar_cosine_geometry (seconds : ℝ) :
      Real.cos (orbit.polarAngleRad seconds) =
        ⟪orbit.periapsisAxis, relativeDisplacementSI motion seconds⟫ /
          separationSI motion seconds := by
    have hangle :=
      congrArg Real.Angle.cos (polar_angle_geometry seconds)
    rw [Real.Angle.cos_coe] at hangle
    rw [← hangle,
      frame.orientation.cos_oangle_eq_inner_div_norm_mul_norm
        periapsisAxis_ne_zero (dynamics.noCollision seconds)]
    simp [orbitLaws.periapsisAxis_unit, separationSI]
  have conic_denominator_eq (seconds : ℝ) :
      1 - orbit.eccentricity *
          Real.cos (orbit.polarAngleRad seconds) =
        scalarSI orbit.semiLatusRectum_a /
          separationSI motion seconds := by
    have hconic := polar_conic seconds
    have hsep_ne := ne_of_gt (separation_positive seconds)
    have hden_ne := ne_of_gt (conic_denominator_positive seconds)
    field_simp [hsep_ne, hden_ne] at hconic ⊢
    linarith
  have cartesian_conic_equation (seconds : ℝ) :
      separationSI motion seconds -
          orbit.eccentricity *
            ⟪orbit.periapsisAxis,
              relativeDisplacementSI motion seconds⟫ =
        scalarSI orbit.semiLatusRectum_a := by
    have hsep_ne := ne_of_gt (separation_positive seconds)
    have hden := conic_denominator_eq seconds
    rw [polar_cosine_geometry seconds] at hden
    field_simp [hsep_ne] at hden
    linarith
  have conic_denominator_tends_to_zero :
      Tendsto
        (fun seconds =>
          1 - orbit.eccentricity *
            Real.cos (orbit.polarAngleRad seconds))
        atTop (𝓝 0) := by
    exact
      (tendsto_const_nhds.div_atTop separation_tends_to_infinity).congr'
        (Filter.Eventually.of_forall fun seconds =>
          (conic_denominator_eq seconds).symm)
  have polar_cosine_tends_to_inverse_eccentricity :
      Tendsto
        (fun seconds => Real.cos (orbit.polarAngleRad seconds))
        atTop (𝓝 (1 / orbit.eccentricity)) := by
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h :=
      (hone.sub conic_denominator_tends_to_zero).div_const
        orbit.eccentricity
    convert h using 1
    · ext seconds
      field_simp [ne_of_gt eccentricity_positive]
      ring
    · norm_num
  have polar_cosine_tends_to_two_sevenths :
      Tendsto
        (fun seconds => Real.cos (orbit.polarAngleRad seconds))
        atTop (𝓝 ((2 : ℝ) / 7)) := by
    simpa [eccentricity_value] using
      polar_cosine_tends_to_inverse_eccentricity
  have normalized_displacement_axis_component_tends :
      Tendsto
        (fun seconds =>
          ⟪orbit.periapsisAxis,
            relativeDisplacementSI motion seconds⟫ /
            separationSI motion seconds)
        atTop (𝓝 (1 / orbit.eccentricity)) := by
    exact polar_cosine_tends_to_inverse_eccentricity.congr'
      (Filter.Eventually.of_forall fun seconds =>
        polar_cosine_geometry seconds)

  /-
  The numerical part of the answer is certified below without trusting a
  floating-point evaluation of either `π` or `arcsin`.  Repeated use of the
  double-angle formulas amplifies the fourth-order bounds `Real.sin_bound`
  and `Real.cos_bound` into the decimal enclosure
  `3.1415 < π < 3.1416`.  The same device then encloses `arcsin (2 / 7)`.
  -/
  let TrigBounds := fun (x sl su cl cu : ℝ) =>
    (sl ≤ Real.sin x ∧ Real.sin x ≤ su) ∧
      (cl ≤ Real.cos x ∧ Real.cos x ≤ cu)
  have rounded_double_trig_bounds
      (x sl su cl cu sl₂ su₂ cl₂ cu₂ : ℝ)
      (h : TrigBounds x sl su cl cu)
      (hsl : 0 ≤ sl) (hcl : 0 ≤ cl)
      (hr : sl₂ ≤ 2 * sl * cl ∧ 2 * su * cu ≤ su₂ ∧
        cl₂ ≤ 2 * cl ^ 2 - 1 ∧ 2 * cu ^ 2 - 1 ≤ cu₂) :
      TrigBounds (2 * x) sl₂ su₂ cl₂ cu₂ := by
    dsimp [TrigBounds] at h ⊢
    rw [Real.sin_two_mul, Real.cos_two_mul]
    have hsx : 0 ≤ Real.sin x := le_trans hsl h.1.1
    have hcx : 0 ≤ Real.cos x := le_trans hcl h.2.1
    have hsu : 0 ≤ su := le_trans hsx h.1.2
    have hcu : 0 ≤ cu := le_trans hcx h.2.2
    have hsin_lower :
        2 * sl * cl ≤ 2 * Real.sin x * Real.cos x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h.1.1) hcx,
        mul_nonneg hsl (sub_nonneg.mpr h.2.1)]
    have hsin_upper :
        2 * Real.sin x * Real.cos x ≤ 2 * su * cu := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h.1.2) hcx,
        mul_nonneg hsu (sub_nonneg.mpr h.2.2)]
    have hcos_lower :
        2 * cl ^ 2 - 1 ≤ 2 * Real.cos x ^ 2 - 1 := by
      nlinarith [
        mul_nonneg (sub_nonneg.mpr h.2.1) (add_nonneg hcx hcl)]
    have hcos_upper :
        2 * Real.cos x ^ 2 - 1 ≤ 2 * cu ^ 2 - 1 := by
      nlinarith [
        mul_nonneg (sub_nonneg.mpr h.2.2) (add_nonneg hcu hcx)]
    exact
      ⟨⟨hr.1.trans hsin_lower, hsin_upper.trans hr.2.1⟩,
        ⟨hr.2.2.1.trans hcos_lower, hcos_upper.trans hr.2.2.2⟩⟩

  let piLowerTrial : ℝ := 3.1415
  have piLowerBounds0 :
      TrigBounds (piLowerTrial / 2048)
        0.00153393494503 0.00153393494562
        0.99999882352058 0.99999882352116 := by
    dsimp [TrigBounds]
    constructor
    · have h := Real.sin_bound
        (x := piLowerTrial / 2048) (by
          norm_num [piLowerTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [piLowerTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
    · have h := Real.cos_bound
        (x := piLowerTrial / 2048) (by
          norm_num [piLowerTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [piLowerTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
  have piLowerBounds1Raw := rounded_double_trig_bounds
    (piLowerTrial / 2048)
    0.00153393494503 0.00153393494562
    0.99999882352058 0.99999882352116
    0.00306786628077 0.00306786628196
    0.99999529408508 0.99999529408741
    piLowerBounds0 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds1 :
      TrigBounds (piLowerTrial / 1024)
        0.00306786628077 0.00306786628196
        0.99999529408508 0.99999529408741 := by
    convert piLowerBounds1Raw using 1 <;> ring
  have piLowerBounds2Raw := rounded_double_trig_bounds
    (piLowerTrial / 1024)
    0.00306786628077 0.00306786628196
    0.99999529408508 0.99999529408741
    0.00613570368730 0.00613570368970
    0.99998117638461 0.99998117639394
    piLowerBounds1 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds2 :
      TrigBounds (piLowerTrial / 512)
        0.00613570368730 0.00613570368970
        0.99998117638461 0.99998117639394 := by
    convert piLowerBounds2Raw using 1 <;> ring
  have piLowerBounds3Raw := rounded_double_trig_bounds
    (piLowerTrial / 512)
    0.00613570368730 0.00613570368970
    0.99998117638461 0.99998117639394
    0.01227117638234 0.01227117638727
    0.99992470624709 0.99992470628442
    piLowerBounds2 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds3 :
      TrigBounds (piLowerTrial / 256)
        0.01227117638234 0.01227117638727
        0.99992470624709 0.99992470628442 := by
    convert piLowerBounds3Raw using 1 <;> ring
  have piLowerBounds4Raw := rounded_double_trig_bounds
    (piLowerTrial / 256)
    0.01227117638234 0.01227117638727
    0.99992470624709 0.99992470628442
    0.02454050487883 0.02454050488962
    0.99969883632665 0.99969883647597
    piLowerBounds3 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds4 :
      TrigBounds (piLowerTrial / 128)
        0.02454050487883 0.02454050488962
        0.99969883632665 0.99969883647597 := by
    convert piLowerBounds4Raw using 1 <;> ring
  have piLowerBounds5Raw := rounded_double_trig_bounds
    (piLowerTrial / 128)
    0.02454050487883 0.02454050488962
    0.99969883632665 0.99969883647597
    0.04906622834046 0.04906622836938
    0.99879552670571 0.99879552730282
    piLowerBounds4 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds5 :
      TrigBounds (piLowerTrial / 64)
        0.04906622834046 0.04906622836938
        0.99879552670571 0.99879552730282 := by
    convert piLowerBounds5Raw using 1 <;> ring
  have piLowerBounds6Raw := rounded_double_trig_bounds
    (piLowerTrial / 64)
    0.04906622834046 0.04906622836938
    0.99879552670571 0.99879552730282
    0.09801425875754 0.09801425887392
    0.99518500833467 0.99518501072024
    piLowerBounds5 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds6 :
      TrigBounds (piLowerTrial / 32)
        0.09801425875754 0.09801425887392
        0.99518500833467 0.99518501072024 := by
    convert piLowerBounds6Raw using 1 <;> ring
  have piLowerBounds7Raw := rounded_double_trig_bounds
    (piLowerTrial / 32)
    0.09801425875754 0.09801425887392
    0.99518500833467 0.99518501072024
    0.19508464183707 0.19508464253636
    0.98078640162815 0.98078641112449
    piLowerBounds6 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds7 :
      TrigBounds (piLowerTrial / 16)
        0.19508464183707 0.19508464253636
        0.98078640162815 0.98078641112449 := by
    convert piLowerBounds7Raw using 1 <;> ring
  have piLowerBounds8Raw := rounded_double_trig_bounds
    (piLowerTrial / 16)
    0.19508464183707 0.19508464253636
    0.98078640162815 0.98078641112449
    0.38267272776059 0.38267273283749
    0.92388393123738 0.92388396849292
    piLowerBounds7 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds8 :
      TrigBounds (piLowerTrial / 8)
        0.38267272776059 0.38267273283749
        0.92388393123738 0.92388396849292 := by
    convert piLowerBounds8Raw using 1 <;> ring
  have piLowerBounds9Raw := rounded_double_trig_bounds
    (piLowerTrial / 8)
    0.38267272776059 0.38267273283749
    0.92388393123738 0.92388396849292
    0.70709036820157 0.70709040609587
    0.70712303679727 0.70712317447646
    piLowerBounds8 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds9 :
      TrigBounds (piLowerTrial / 4)
        0.70709036820157 0.70709040609587
        0.70712303679727 0.70712317447646 := by
    convert piLowerBounds9Raw using 1 <;> ring
  have piLowerBounds10Raw := rounded_double_trig_bounds
    (piLowerTrial / 4)
    0.70709036820157 0.70709040609587
    0.70712303679727 0.70712317447646
    0.99999977690558 1.00000002520073
    0.00004597833878 0.00004636776334
    piLowerBounds9 (by norm_num) (by norm_num) (by norm_num)
  have piLowerBounds10 :
      TrigBounds (piLowerTrial / 2)
        0.99999977690558 1.00000002520073
        0.00004597833878 0.00004636776334 := by
    convert piLowerBounds10Raw using 1 <;> ring
  have sin_piLowerTrial_positive : 0 < Real.sin piLowerTrial := by
    have hs : 0 < Real.sin (piLowerTrial / 2) :=
      lt_of_lt_of_le (by norm_num) piLowerBounds10.1.1
    have hc : 0 < Real.cos (piLowerTrial / 2) :=
      lt_of_lt_of_le (by norm_num) piLowerBounds10.2.1
    rw [show piLowerTrial = 2 * (piLowerTrial / 2) by ring,
      Real.sin_two_mul]
    positivity
  have pi_lower_bound : (3.1415 : ℝ) < Real.pi := by
    change piLowerTrial < Real.pi
    by_contra h
    have hpi : Real.pi ≤ piLowerTrial := le_of_not_gt h
    have hsub_nonneg : 0 ≤ piLowerTrial - Real.pi := sub_nonneg.mpr hpi
    have hsub_le_pi : piLowerTrial - Real.pi ≤ Real.pi := by
      dsimp [piLowerTrial]
      nlinarith [Real.two_le_pi]
    have hsin_nonneg :=
      Real.sin_nonneg_of_nonneg_of_le_pi hsub_nonneg hsub_le_pi
    have hrewrite :
        Real.sin piLowerTrial =
          -Real.sin (piLowerTrial - Real.pi) := by
      calc
        Real.sin piLowerTrial =
            Real.sin ((piLowerTrial - Real.pi) + Real.pi) := by
          congr 1
          ring
        _ = -Real.sin (piLowerTrial - Real.pi) :=
          Real.sin_add_pi _
    rw [hrewrite] at sin_piLowerTrial_positive
    linarith

  let piUpperTrial : ℝ := 3.1416
  have piUpperBounds0 :
      TrigBounds (piUpperTrial / 2048)
        0.00153398377310 0.00153398377369
        0.99999882344568 0.99999882344626 := by
    dsimp [TrigBounds]
    constructor
    · have h := Real.sin_bound
        (x := piUpperTrial / 2048) (by
          norm_num [piUpperTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [piUpperTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
    · have h := Real.cos_bound
        (x := piUpperTrial / 2048) (by
          norm_num [piUpperTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [piUpperTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
  have piUpperBounds1Raw := rounded_double_trig_bounds
    (piUpperTrial / 2048)
    0.00153398377310 0.00153398377369
    0.99999882344568 0.99999882344626
    0.00306796393656 0.00306796393776
    0.99999529378548 0.99999529378781
    piUpperBounds0 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds1 :
      TrigBounds (piUpperTrial / 1024)
        0.00306796393656 0.00306796393776
        0.99999529378548 0.99999529378781 := by
    convert piUpperBounds1Raw using 1 <;> ring
  have piUpperBounds2Raw := rounded_double_trig_bounds
    (piUpperTrial / 1024)
    0.00306796393656 0.00306796393776
    0.99999529378548 0.99999529378781
    0.00613589899612 0.00613589899855
    0.99998117518621 0.99998117519554
    piUpperBounds1 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds2 :
      TrigBounds (piUpperTrial / 512)
        0.00613589899612 0.00613589899855
        0.99998117518621 0.99998117519554 := by
    convert piUpperBounds2Raw using 1 <;> ring
  have piUpperBounds3Raw := rounded_double_trig_bounds
    (piUpperTrial / 512)
    0.00613589899612 0.00613589899855
    0.99998117518621 0.99998117519554
    0.01227156697792 0.01227156698291
    0.99992470145358 0.99992470149091
    piUpperBounds2 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds3 :
      TrigBounds (piUpperTrial / 256)
        0.01227156697792 0.01227156698291
        0.99992470145358 0.99992470149091 := by
    convert piUpperBounds3Raw using 1 <;> ring
  have piUpperBounds4Raw := rounded_double_trig_bounds
    (piUpperTrial / 256)
    0.01227156697792 0.01227156698291
    0.99992470145358 0.99992470149091
    0.02454128589352 0.02454128590443
    0.99969881715406 0.99969881730338
    piUpperBounds3 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds4 :
      TrigBounds (piUpperTrial / 128)
        0.02454128589352 0.02454128590443
        0.99969881715406 0.99969881730338 := by
    convert piUpperBounds4Raw using 1 <;> ring
  have piUpperBounds5Raw := rounded_double_trig_bounds
    (piUpperTrial / 128)
    0.02454128589352 0.02454128590443
    0.99969881715406 0.99969881730338
    0.04906778895838 0.04906778898753
    0.99879545003845 0.99879545063556
    piUpperBounds4 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds5 :
      TrigBounds (piUpperTrial / 64)
        0.04906778895838 0.04906778898753
        0.99879545003845 0.99879545063556 := by
    convert piUpperBounds5Raw using 1 <;> ring
  have piUpperBounds6Raw := rounded_double_trig_bounds
    (piUpperTrial / 64)
    0.04906778895838 0.04906778898753
    0.99879545003845 0.99879545063556
    0.09801736871015 0.09801736882699
    0.99518470203501 0.99518470442059
    piUpperBounds5 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds6 :
      TrigBounds (piUpperTrial / 32)
        0.09801736871015 0.09801736882699
        0.99518470203501 0.99518470442059 := by
    convert piUpperBounds6Raw using 1 <;> ring
  have piUpperBounds7Raw := rounded_double_trig_bounds
    (piUpperTrial / 32)
    0.09801736871015 0.09801736882699
    0.99518470203501 0.99518470442059
    0.19509077174813 0.19509077244835
    0.98078518232902 0.98078519182540
    piUpperBounds6 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds7 :
      TrigBounds (piUpperTrial / 16)
        0.19509077174813 0.19509077244835
        0.98078518232902 0.98078519182540 := by
    convert piUpperBounds7Raw using 1 <;> ring
  have piUpperBounds8Raw := rounded_double_trig_bounds
    (piUpperTrial / 16)
    0.19509077174813 0.19509077244835
    0.98078518232902 0.98078519182540
    0.38268427627939 0.38268428135825
    0.92387914775233 0.92387918500798
    piUpperBounds7 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds8 :
      TrigBounds (piUpperTrial / 8)
        0.38268427627939 0.38268428135825
        0.92387914775233 0.92387918500798 := by
    convert piUpperBounds8Raw using 1 <;> ring
  have piUpperBounds9Raw := rounded_double_trig_bounds
    (piUpperTrial / 8)
    0.38268427627939 0.38268428135825
    0.92387914775233 0.92387918500798
    0.70710804605444 0.70710808395325
    0.70710535930314 0.70710549698202
    piUpperBounds8 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds9 :
      TrigBounds (piUpperTrial / 4)
        0.70710804605444 0.70710808395325
        0.70710535930314 0.70710549698202 := by
    convert piUpperBounds9Raw using 1 <;> ring
  have piUpperBounds10Raw := rounded_double_trig_bounds
    (piUpperTrial / 4)
    0.70710804605444 0.70710808395325
    0.70710535930314 0.70710549698202
    0.99999977794293 1.00000002624754
    (-0.00000402168956) (-0.00000363227562)
    piUpperBounds9 (by norm_num) (by norm_num) (by norm_num)
  have piUpperBounds10 :
      TrigBounds (piUpperTrial / 2)
        0.99999977794293 1.00000002624754
        (-0.00000402168956) (-0.00000363227562) := by
    convert piUpperBounds10Raw using 1 <;> ring
  have sin_piUpperTrial_negative : Real.sin piUpperTrial < 0 := by
    have hs : 0 < Real.sin (piUpperTrial / 2) :=
      lt_of_lt_of_le (by norm_num) piUpperBounds10.1.1
    have hc : Real.cos (piUpperTrial / 2) < 0 :=
      lt_of_le_of_lt piUpperBounds10.2.2 (by norm_num)
    rw [show piUpperTrial = 2 * (piUpperTrial / 2) by ring,
      Real.sin_two_mul]
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hs) hc
  have pi_upper_bound : Real.pi < (3.1416 : ℝ) := by
    change Real.pi < piUpperTrial
    by_contra h
    have htrial_le_pi : piUpperTrial ≤ Real.pi := le_of_not_gt h
    have hsin_nonneg :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        (by norm_num [piUpperTrial]) htrial_le_pi
    linarith

  let lowerAngleTrial : ℝ := 3319 * (3.1416 : ℝ) / 36000
  have lowerAngleBounds0 :
      TrigBounds (lowerAngleTrial / 8)
        0.03619675940653 0.03619693838114
        0.99934451824971 0.99934469722431 := by
    dsimp [TrigBounds]
    constructor
    · have h := Real.sin_bound
        (x := lowerAngleTrial / 8) (by
          norm_num [lowerAngleTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [lowerAngleTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
    · have h := Real.cos_bound
        (x := lowerAngleTrial / 8) (by
          norm_num [lowerAngleTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [lowerAngleTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
  have lowerAngleBounds1Raw := rounded_double_trig_bounds
    (lowerAngleTrial / 8)
    0.03619675940653 0.03619693838114
    0.99934451824971 0.99934469722431
    0.07234606618263 0.07234643685390
    0.99737893231148 0.99737964774070
    lowerAngleBounds0 (by norm_num) (by norm_num) (by norm_num)
  have lowerAngleBounds1 :
      TrigBounds (lowerAngleTrial / 4)
        0.07234606618263 0.07234643685390
        0.99737893231148 0.99737964774070 := by
    convert lowerAngleBounds1Raw using 1 <;> ring
  have lowerAngleBounds2Raw := rounded_double_trig_bounds
    (lowerAngleTrial / 4)
    0.07234606618263 0.07234643685390
    0.99737893231148 0.99737964774070
    0.14431288449233 0.14431372740928
    0.98952946923757 0.98953232345473
    lowerAngleBounds1 (by norm_num) (by norm_num) (by norm_num)
  have lowerAngleBounds2 :
      TrigBounds (lowerAngleTrial / 2)
        0.14431288449233 0.14431372740928
        0.98952946923757 0.98953232345473 := by
    convert lowerAngleBounds2Raw using 1 <;> ring
  have lowerAngleBounds3Raw := rounded_double_trig_bounds
    (lowerAngleTrial / 2)
    0.14431288449233 0.14431372740928
    0.98952946923757 0.98953232345473
    0.28560370399167 0.28560619597944
    0.95833714097917 0.95834843832344
    lowerAngleBounds2 (by norm_num) (by norm_num) (by norm_num)
  have lowerAngleBounds3 :
      TrigBounds lowerAngleTrial
        0.28560370399167 0.28560619597944
        0.95833714097917 0.95834843832344 := by
    convert lowerAngleBounds3Raw using 1 <;> ring
  have lower_endpoint_sine_le :
      Real.sin (3319 * Real.pi / 36000) ≤ (2 : ℝ) / 7 := by
    have harg :
        3319 * Real.pi / 36000 ≤ lowerAngleTrial := by
      dsimp [lowerAngleTrial]
      nlinarith [pi_upper_bound]
    have htrial_le_half_pi : lowerAngleTrial ≤ Real.pi / 2 := by
      dsimp [lowerAngleTrial]
      nlinarith [Real.two_le_pi]
    have hmono :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := 3319 * Real.pi / 36000)
        (y := lowerAngleTrial)
        (by nlinarith [Real.pi_pos])
        htrial_le_half_pi harg
    calc
      Real.sin (3319 * Real.pi / 36000) ≤
          Real.sin lowerAngleTrial := hmono
      _ ≤ 0.28560619597944 := lowerAngleBounds3.1.2
      _ ≤ (2 : ℝ) / 7 := by norm_num

  let upperAngleTrial : ℝ := 3321 * (3.1415 : ℝ) / 36000
  have upperAngleBounds0 :
      TrigBounds (upperAngleTrial / 8)
        0.03621740919327 0.03621758857682
        0.99934376971322 0.99934394909676 := by
    dsimp [TrigBounds]
    constructor
    · have h := Real.sin_bound
        (x := upperAngleTrial / 8) (by
          norm_num [upperAngleTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [upperAngleTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
    · have h := Real.cos_bound
        (x := upperAngleTrial / 8) (by
          norm_num [upperAngleTrial, abs_of_nonneg])
      rw [abs_le] at h
      constructor <;>
        norm_num [upperAngleTrial, abs_of_nonneg] at h ⊢ <;>
        linarith [h.1, h.2]
  have upperAngleBounds1Raw := rounded_double_trig_bounds
    (upperAngleTrial / 8)
    0.03621740919327 0.03621758857682
    0.99934376971322 0.99934394909676
    0.07238728446489 0.07238765599025
    0.99737594012925 0.99737665719262
    upperAngleBounds0 (by norm_num) (by norm_num) (by norm_num)
  have upperAngleBounds1 :
      TrigBounds (upperAngleTrial / 4)
        0.07238728446489 0.07238765599025
        0.99737594012925 0.99737665719262 := by
    convert upperAngleBounds1Raw using 1 <;> ring
  have upperAngleBounds2Raw := rounded_double_trig_bounds
    (upperAngleTrial / 4)
    0.07238728446489 0.07238765599025
    0.99737594012925 0.99737665719262
    0.14439467179314 0.14439551670713
    0.98951753189741 0.98952039262546
    upperAngleBounds1 (by norm_num) (by norm_num) (by norm_num)
  have upperAngleBounds2 :
      TrigBounds (upperAngleTrial / 2)
        0.14439467179314 0.14439551670713
        0.98951753189741 0.98952039262546 := by
    convert upperAngleBounds2Raw using 1 <;> ring
  have upperAngleBounds3Raw := rounded_double_trig_bounds
    (upperAngleTrial / 2)
    0.14439467179314 0.14439551670713
    0.98951753189741 0.98952039262546
    0.28576211850376 0.28576461677080
    0.95828989186468 0.95830121484329
    upperAngleBounds2 (by norm_num) (by norm_num) (by norm_num)
  have upperAngleBounds3 :
      TrigBounds upperAngleTrial
        0.28576211850376 0.28576461677080
        0.95828989186468 0.95830121484329 := by
    convert upperAngleBounds3Raw using 1 <;> ring
  have upper_endpoint_sine_ge :
      (2 : ℝ) / 7 ≤ Real.sin (3321 * Real.pi / 36000) := by
    have harg :
        upperAngleTrial ≤ 3321 * Real.pi / 36000 := by
      dsimp [upperAngleTrial]
      nlinarith [pi_lower_bound]
    have htarget_le_half_pi :
        3321 * Real.pi / 36000 ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hmono :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := upperAngleTrial)
        (y := 3321 * Real.pi / 36000)
        (by
          dsimp [upperAngleTrial]
          nlinarith [Real.pi_pos])
        htarget_le_half_pi harg
    calc
      (2 : ℝ) / 7 ≤ 0.28576211850376 := by norm_num
      _ ≤ Real.sin upperAngleTrial := upperAngleBounds3.1.1
      _ ≤ Real.sin (3321 * Real.pi / 36000) := hmono

  have arcsin_lower_bound :
      3319 * Real.pi / 36000 ≤ Real.arcsin ((2 : ℝ) / 7) := by
    rw [Real.le_arcsin_iff_sin_le]
    · exact lower_endpoint_sine_le
    · constructor <;> nlinarith [Real.pi_pos]
    · norm_num
  have arcsin_upper_bound :
      Real.arcsin ((2 : ℝ) / 7) ≤
        3321 * Real.pi / 36000 := by
    rw [Real.arcsin_le_iff_le_sin]
    · exact upper_endpoint_sine_ge
    · norm_num
    · constructor <;> nlinarith [Real.pi_pos]
  have deflection_number_lower :
      (3319 : ℝ) / 200 ≤
        Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi := by
    have hpi := Real.pi_pos
    apply (le_div_iff₀ hpi).2
    nlinarith [arcsin_lower_bound]
  have deflection_number_upper :
      Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi ≤
        (3321 : ℝ) / 200 := by
    have hpi := Real.pi_pos
    apply (div_le_iff₀ hpi).2
    nlinarith [arcsin_upper_bound]
  have negative_arcsin_deflection :
      -Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi < 0 := by
    have harcsin : 0 < Real.arcsin ((2 : ℝ) / 7) :=
      Real.arcsin_pos.mpr (by norm_num)
    have hpositive :
        0 < Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi :=
      div_pos (mul_pos harcsin (by norm_num)) Real.pi_pos
    rw [show -Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi =
        -(Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi) by ring]
    exact neg_neg_of_pos hpositive
  have negative_arcsin_rounds :
      RoundsToNearestHundredth
        (-Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi)
        (-(83 : ℝ) / 5) := by
    rw [RoundsToNearestHundredth,
      show -Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi =
          -(Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi) by ring,
      abs_le]
    constructor <;> nlinarith

  -- It remains to identify the limiting relative velocity with the outgoing
  -- branch of the position conic, including its clockwise sign.  The facts
  -- proved above determine the asymptotic position-axis cosine, but the
  -- frozen imports provide no mean-value/asymptotic-integration theorem that
  -- turns `positionDerivative` and the velocity limit into a normalized
  -- displacement limit.
  have signed_deflection_formula :
      signedDeflectionDegrees motion frame uInfinity =
        -Real.arcsin ((2 : ℝ) / 7) * 180 / Real.pi := by
    sorry
  constructor
  · rw [signed_deflection_formula]
    exact negative_arcsin_deflection
  · rw [signed_deflection_formula]
    exact negative_arcsin_rounds

end IPhO2026Problems.IPhO2026_1_B_2
