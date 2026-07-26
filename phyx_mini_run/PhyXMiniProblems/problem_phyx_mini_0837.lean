import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0837

open Dimension

/-!
# Limiting launch speed of an electron between parallel plates

An electron is launched from the positive lower plate at `45 degrees` through
a uniform electric field of strength `1.0 * 10^4 N/C`.  The negative upper
plate is `2.0 cm` above the launch point.  Because the electron is negatively
charged, its electric acceleration is downward, so its vertical motion is the
electric analogue of projectile motion.

Lengths, elapsed times, mass, charge, speed, force, acceleration, and field
strength are represented by unit-independent Physlib quantities.  Real
numbers occur only as coherent-SI readouts, dimensionless angles, schematic
figure metadata, trajectory coordinates, and displayed answer values.

The phrase "maximum speed without hitting" is represented by a limiting
non-impact speed: every strictly slower launch avoids the negative plate, and
every speed which avoids it is at most the limit.  Thus the threshold may
correspond to a grazing trajectory without incorrectly asserting that a
strictly non-impacting trajectory attains a maximum.

Assumption/target split:

* governing laws: uniform-field geometry, `F = q E`, Newton's second law, and
  the horizontal and vertical constant-acceleration trajectory equations;
* previous-part results: none;
* figure/data readouts: the positive lower and negative upper plates, the
  `2.0 cm` separation, `1.0 * 10^4 N/C` field, and the up-right `45 degree`
  launch arrow labelled `v_0`;
* current target conclusions: existence of the limiting non-impact speed, its
  symbolic and numerical square/square-root forms, rounding to
  `1.19 * 10^7 m/s`, and selection of choice D.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T^-2`. -/
def forceDimension : Dimension :=
  M𝓭 * accelerationDimension

/-- The physical dimension of electric-field strength, `M L T^-2 C^-1`. -/
def electricFieldStrengthDimension : Dimension :=
  forceDimension * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical elapsed time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative electric-field-strength magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A signed planar displacement vector. -/
abbrev PlanarDisplacementQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A signed planar force vector. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- A signed planar acceleration vector. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful
    (WithDim accelerationDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, horizontal and positive to the right in the figure. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive toward the negative plate. -/
def yAxis : Fin 2 := 1

/-- The unit vector pointing from the positive plate to the negative plate. -/
def upwardDirection : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single yAxis 1

/-- Read a nonnegative dimensionful scalar in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful scalar in coherent SI units. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Read a dimensionful planar vector in coherent SI units. -/
def planarSIReadout {dimension : Dimension}
    (quantity : Dimensionful
      (WithDim dimension (EuclideanSpace ℝ (Fin 2)))) :
    EuclideanSpace ℝ (Fin 2) :=
  (quantity UnitChoices.SI).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Second readout of a physical elapsed time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  signedSIReadout charge

/-- Metre-per-second readout of a physical speed magnitude. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Newton-per-coulomb readout of an electric-field-strength magnitude. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (fieldStrength : ElectricFieldStrengthQuantity) : ℝ :=
  nonnegativeSIReadout fieldStrength

/-- Cartesian displacement readout in metres. -/
def displacementInMeters (displacement : PlanarDisplacementQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  planarSIReadout displacement

/-- Cartesian net-force readout in newtons. -/
def forceInNewtons (force : PlanarForceQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  planarSIReadout force

/-- Cartesian acceleration readout in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  planarSIReadout acceleration

/-! ## Physical roles and primary-image vocabulary -/

/-- The particle species named in the problem. -/
inductive ParticleSpecies where
  | electron
  deriving DecidableEq, Repr

/-- The two horizontal plates in the supplied raster. -/
inductive Plate where
  | lower
  | upper
  deriving DecidableEq, Fintype, Repr

/-- Electric polarity attached to each plate. -/
inductive PlatePolarity where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

/-- Qualitative direction of the velocity arrow in the diagram. -/
inductive LaunchArrowDirection where
  | upRight
  deriving DecidableEq, Repr

/-- Idealized physical regime intended by the textbook problem. -/
inductive MotionRegime where
  | nonrelativisticUniformElectricField
  deriving DecidableEq, Repr

/-!
Literal and qualitative information transcribed from `837.png`.  The two
real-valued fields are printed figure labels, not solved physical quantities.
-/
structure ParallelPlateElectronFigure where
  showsPlate : Plate → Bool
  plateIsHorizontal : Plate → Bool
  platePolarity : Plate → PlatePolarity
  platesShownParallel : Bool
  separationDoubleArrowShown : Bool
  printedSeparationCentimeters : ℝ
  velocityArrowShown : Bool
  velocityArrowLabelledV0 : Bool
  velocityArrowDirection : LaunchArrowDirection
  velocityArrowStartsAtLowerPlate : Bool
  angleArcShown : Bool
  printedLaunchAngleDegrees : ℝ

/-!
Independent physical quantities and the family of trajectories obtained by
varying the launch-speed magnitude.  No maximum speed or answer choice is a
field of this setup.
-/
structure ElectronParallelPlateSetup where
  figure : ParallelPlateElectronFigure
  particleSpecies : ParticleSpecies
  motionRegime : MotionRegime
  plateSeparation : LengthQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  electronMass : MassQuantity
  electronCharge : SignedChargeQuantity
  launchAngleRadians : ℝ
  appliedElectricField : Electromagnetism.ElectricField 2
  netElectricForce : PlanarForceQuantity
  electronAcceleration : PlanarAccelerationQuantity
  displacementFromLaunchAt :
    DimSpeed → TimeQuantity → PlanarDisplacementQuantity

/-! ## Scenario, data, figure evidence, and governing laws -/

/-- Qualitative physical scenario stated in the problem. -/
structure MatchesElectronParallelPlateScenario
    (setup : ElectronParallelPlateSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  intendedMotionRegime :
    setup.motionRegime = .nonrelativisticUniformElectricField
  lowerPlateIsPositive : setup.figure.platePolarity .lower = .positive
  upperPlateIsNegative : setup.figure.platePolarity .upper = .negative

/-!
The three calibrated physical readouts stated in the prose.  This record does
not constrain a launch-speed magnitude.
-/
structure MatchesProblemReadouts
    (setup : ElectronParallelPlateSetup) : Prop where
  plateSeparationMeters : lengthInMeters setup.plateSeparation = 2 / 100
  fieldStrengthNewtonsPerCoulomb :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldStrength = 1 * 10 ^ 4
  launchAngleIsFortyFiveDegrees :
    setup.launchAngleRadians = Real.pi / 4

/-- Facts read directly from the supplied parallel-plate diagram. -/
structure MatchesSuppliedParallelPlateFigure
    (setup : ElectronParallelPlateSetup) : Prop where
  bothPlatesShown : ∀ plate, setup.figure.showsPlate plate = true
  bothPlatesHorizontal :
    ∀ plate, setup.figure.plateIsHorizontal plate = true
  platesAreParallel : setup.figure.platesShownParallel = true
  separationArrowShown : setup.figure.separationDoubleArrowShown = true
  printedSeparationIsTwoCentimeters :
    setup.figure.printedSeparationCentimeters = 2
  launchArrowShown : setup.figure.velocityArrowShown = true
  launchArrowHasV0Label : setup.figure.velocityArrowLabelledV0 = true
  launchArrowPointsUpAndRight :
    setup.figure.velocityArrowDirection = .upRight
  launchBeginsAtPositiveLowerPlate :
    setup.figure.velocityArrowStartsAtLowerPlate = true
  angleArcIsShown : setup.figure.angleArcShown = true
  printedAngleIsFortyFiveDegrees :
    setup.figure.printedLaunchAngleDegrees = 45

/-!
Standard electron reference data needed by the calculation.  The magnitude
ratio `|q_e| / m_e = 1.76 * 10^11 C/kg` is independent of the requested
launch speed and of all displayed choices.
-/
structure UsesStandardElectronReferenceData
    (setup : ElectronParallelPlateSetup) : Prop where
  electronChargeIsNegative : chargeInCoulombs setup.electronCharge < 0
  chargeMagnitudeToMassRatio :
    |chargeInCoulombs setup.electronCharge| /
        massInKilograms setup.electronMass = 176 / 100 * 10 ^ 11

/-- Positivity and angle-range conditions selecting the physical branch. -/
structure HasPhysicalParallelPlateParameters
    (setup : ElectronParallelPlateSetup) : Prop where
  positivePlateSeparation : 0 < lengthInMeters setup.plateSeparation
  positiveFieldStrength :
    0 < electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldStrength
  positiveElectronMass : 0 < massInKilograms setup.electronMass
  nonzeroElectronCharge : chargeInCoulombs setup.electronCharge ≠ 0
  launchAnglePositive : 0 < setup.launchAngleRadians
  launchAngleAcute : setup.launchAngleRadians < Real.pi / 2

/-!
The Physlib electric field is spatially and temporally uniform and points from
the positive lower plate toward the negative upper plate.  Its vector entries
are interpreted as coherent-SI field-strength components.
-/
structure IsUniformUpwardParallelPlateField
    (setup : ElectronParallelPlateSetup) : Prop where
  fieldUniformAndUpward : ∀ spacetimeTime position,
    setup.appliedElectricField spacetimeTime position =
      electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength • upwardDirection

/-!
Governing force and kinematic laws:

* the horizontal electric-force component vanishes;
* the vertical component is `q E` in the upward-positive convention;
* Newton's second law holds componentwise; and
* every trial speed produces the usual constant-acceleration trajectory from
  the launch point on the lower plate.

These equations apply uniformly to arbitrary trial speeds and contain no
limiting speed or displayed answer value.
-/
structure SatisfiesElectronParallelPlateMotionLaws
    (setup : ElectronParallelPlateSetup) : Prop where
  noHorizontalElectricForce :
    forceInNewtons setup.netElectricForce xAxis = 0
  verticalElectricForceLaw :
    forceInNewtons setup.netElectricForce yAxis =
      chargeInCoulombs setup.electronCharge *
        electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength
  newtonsSecondLaw : ∀ axis,
    forceInNewtons setup.netElectricForce axis =
      massInKilograms setup.electronMass *
        accelerationInMetersPerSecondSquared
          setup.electronAcceleration axis
  horizontalTrajectoryLaw : ∀ speed elapsed,
    displacementInMeters
        (setup.displacementFromLaunchAt speed elapsed) xAxis =
      speedInMetersPerSecond speed *
        Real.cos setup.launchAngleRadians * timeInSeconds elapsed
  verticalTrajectoryLaw : ∀ speed elapsed,
    displacementInMeters
        (setup.displacementFromLaunchAt speed elapsed) yAxis =
      speedInMetersPerSecond speed *
          Real.sin setup.launchAngleRadians * timeInSeconds elapsed +
        accelerationInMetersPerSecondSquared
            setup.electronAcceleration yAxis /
          2 * timeInSeconds elapsed ^ 2

/-! ## Non-impact criterion, displayed choices, and derived target -/

/-!
A trial launch avoids the negative plate when its vertical coordinate remains
strictly below the plate separation at every nonnegative physical elapsed
time.
-/
def AvoidsNegativePlate
    (setup : ElectronParallelPlateSetup) (speed : DimSpeed) : Prop :=
  ∀ elapsed,
    displacementInMeters
        (setup.displacementFromLaunchAt speed elapsed) yAxis <
      lengthInMeters setup.plateSeparation

/-!
`speedLimit` is the supremal non-impact speed: it bounds every avoiding speed,
and every strictly slower physical speed avoids the upper plate.  Membership
of the threshold itself is intentionally not required.
-/
def IsLimitingNonimpactSpeed
    (setup : ElectronParallelPlateSetup) (speedLimit : DimSpeed) : Prop :=
  (∀ speed, AvoidsNegativePlate setup speed →
      speedInMetersPerSecond speed ≤
        speedInMetersPerSecond speedLimit) ∧
    (∀ speed,
      speedInMetersPerSecond speed <
          speedInMetersPerSecond speedLimit →
        AvoidsNegativePlate setup speed)

/-- Labels attached to the four displayed speed choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre-per-second value printed beside each answer label. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 13 / 10 * 10 ^ 7
  | .B => 53 / 10 * 10 ^ 7
  | .C => 1 * 10 ^ 7
  | .D => 119 / 100 * 10 ^ 7

/-- A general nearest-rounding relation at a positive displayed increment. -/
def RoundsToNearestIncrement
    (value displayed increment : ℝ) : Prop :=
  0 < increment ∧ |value - displayed| ≤ increment / 2

/-- A choice is closest when no displayed alternative is nearer. -/
def IsClosestDisplayedSpeed
    (speed : DimSpeed) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |speedInMetersPerSecond speed -
        displayedSpeedInMetersPerSecond choice| ≤
      |speedInMetersPerSecond speed -
        displayedSpeedInMetersPerSecond alternative|

/-!
For an arbitrary physical instance, the vertical trajectory and electric
force laws give

`v_limit^2 = 2 (|q_e| / m_e) E d / sin(theta)^2`.

This symbolic relation is derived from the governing laws and limiting
property; it does not occur in a premise structure.
-/
lemma limiting_nonimpact_speed_squared_formula
    (setup : ElectronParallelPlateSetup)
    (speedLimit : DimSpeed)
    (hElectron : UsesStandardElectronReferenceData setup)
    (hPhysical : HasPhysicalParallelPlateParameters setup)
    (hField : IsUniformUpwardParallelPlateField setup)
    (hMotion : SatisfiesElectronParallelPlateMotionLaws setup)
    (hLimit : IsLimitingNonimpactSpeed setup speedLimit) :
    speedInMetersPerSecond speedLimit ^ 2 =
      2 *
          (|chargeInCoulombs setup.electronCharge| /
            massInKilograms setup.electronMass) *
        electricFieldStrengthInNewtonsPerCoulomb
            setup.electricFieldStrength *
          lengthInMeters setup.plateSeparation /
            Real.sin setup.launchAngleRadians ^ 2 := by
  let q := chargeInCoulombs setup.electronCharge
  let m := massInKilograms setup.electronMass
  let E :=
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  let d := lengthInMeters setup.plateSeparation
  let s := Real.sin setup.launchAngleRadians
  let g := |q| / m * E
  let V := speedInMetersPerSecond speedLimit
  have hq : q < 0 := by
    simpa [q] using hElectron.electronChargeIsNegative
  have hm : 0 < m := by
    simpa [m] using hPhysical.positiveElectronMass
  have hE : 0 < E := by
    simpa [E] using hPhysical.positiveFieldStrength
  have hd : 0 < d := by
    simpa [d] using hPhysical.positivePlateSeparation
  have hs : 0 < s := by
    apply Real.sin_pos_of_pos_of_lt_pi hPhysical.launchAnglePositive
    nlinarith [hPhysical.launchAngleAcute, Real.pi_pos]
  have hg : 0 < g := by
    dsimp [g]
    exact mul_pos (div_pos (abs_pos.mpr (ne_of_lt hq)) hm) hE
  have hV : 0 ≤ V := by
    change 0 ≤ (((speedLimit UnitChoices.SI).val : NNReal) : ℝ)
    exact NNReal.coe_nonneg _
  have hAcceleration :
      accelerationInMetersPerSecondSquared
          setup.electronAcceleration yAxis = -g := by
    have hNewton := hMotion.newtonsSecondLaw yAxis
    rw [hMotion.verticalElectricForceLaw] at hNewton
    change q * E =
      m * accelerationInMetersPerSecondSquared
        setup.electronAcceleration yAxis at hNewton
    have hAcceleration' :
        accelerationInMetersPerSecondSquared
            setup.electronAcceleration yAxis = q * E / m := by
      apply (eq_div_iff (ne_of_gt hm)).2
      nlinarith
    rw [hAcceleration']
    dsimp [g]
    rw [abs_of_neg hq]
    field_simp
  let mkSpeed : ∀ u : ℝ, 0 ≤ u → DimSpeed :=
    fun u hu =>
      CarriesDimension.toDimensionful UnitChoices.SI
        (⟨⟨u, hu⟩⟩ :
          WithDim (L𝓭 * T𝓭⁻¹) NNReal)
  have mkSpeed_readout (u : ℝ) (hu : 0 ≤ u) :
      speedInMetersPerSecond (mkSpeed u hu) = u := by
    simp only [mkSpeed, speedInMetersPerSecond,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self, one_smul]
    exact NNReal.coe_mk u hu
  let mkTime : ∀ t : ℝ, 0 ≤ t → TimeQuantity :=
    fun t ht =>
      CarriesDimension.toDimensionful UnitChoices.SI
        (⟨⟨t, ht⟩⟩ : WithDim T𝓭 NNReal)
  have mkTime_readout (t : ℝ) (ht : 0 ≤ t) :
      timeInSeconds (mkTime t ht) = t := by
    simp only [mkTime, timeInSeconds, nonnegativeSIReadout,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self, one_smul]
    exact NNReal.coe_mk t ht
  have avoids_of_energy_lt (speed : DimSpeed)
      (hEnergy :
        speedInMetersPerSecond speed ^ 2 * s ^ 2 < 2 * g * d) :
      AvoidsNegativePlate setup speed := by
    intro elapsed
    rw [hMotion.verticalTrajectoryLaw, hAcceleration]
    have ht : 0 ≤ timeInSeconds elapsed := by
      change 0 ≤ (((elapsed UnitChoices.SI).val : NNReal) : ℝ)
      exact NNReal.coe_nonneg _
    have hSquare :
        0 ≤
          (g * timeInSeconds elapsed -
              speedInMetersPerSecond speed * s) ^ 2 :=
      sq_nonneg _
    nlinarith
  have not_avoids_of_energy_gt (speed : DimSpeed)
      (hEnergy :
        2 * g * d <
          speedInMetersPerSecond speed ^ 2 * s ^ 2) :
      ¬ AvoidsNegativePlate setup speed := by
    intro hAvoids
    have hv : 0 ≤ speedInMetersPerSecond speed := by
      change 0 ≤ (((speed UnitChoices.SI).val : NNReal) : ℝ)
      exact NNReal.coe_nonneg _
    let t := speedInMetersPerSecond speed * s / g
    have ht : 0 ≤ t := by
      dsimp [t]
      positivity
    have hVertex :
        g * t = speedInMetersPerSecond speed * s := by
      dsimp [t]
      field_simp
    have hAtVertex := hAvoids (mkTime t ht)
    rw [hMotion.verticalTrajectoryLaw, hAcceleration,
      mkTime_readout] at hAtVertex
    have hEnergy' :
        2 * g * d <
          (speedInMetersPerSecond speed * s) ^ 2 := by
      nlinarith
    rw [← hVertex] at hEnergy'
    have hPeak : 2 * d < g * t ^ 2 := by
      apply lt_of_mul_lt_mul_left
        (show g * (2 * d) < g * (g * t ^ 2) by nlinarith)
        (le_of_lt hg)
    nlinarith
  let K := Real.sqrt (2 * g * d) / s
  have hRadicand : 0 < 2 * g * d := by positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hKenergy : K ^ 2 * s ^ 2 = 2 * g * d := by
    dsimp [K]
    rw [div_pow]
    rw [Real.sq_sqrt (le_of_lt hRadicand)]
    field_simp
  have hVK : V = K := by
    apply le_antisymm
    · by_contra hNot
      have hKV : K < V := lt_of_not_ge hNot
      let u := (K + V) / 2
      have hu0 : 0 ≤ u := by
        dsimp [u]
        positivity
      have hKu : K < u := by
        dsimp [u]
        linarith
      have huV : u < V := by
        dsimp [u]
        linarith
      have hEnergy : 2 * g * d < u ^ 2 * s ^ 2 := by
        have hSquares : K ^ 2 < u ^ 2 :=
          (sq_lt_sq₀ (le_of_lt hK) hu0).2 hKu
        nlinarith [sq_pos_of_pos hs]
      have hAvoids :
          AvoidsNegativePlate setup (mkSpeed u hu0) := by
        apply hLimit.2
        rw [mkSpeed_readout]
        simpa [V] using huV
      exact
        not_avoids_of_energy_gt (mkSpeed u hu0)
          (by simpa [mkSpeed_readout] using hEnergy) hAvoids
    · by_contra hNot
      have hVK' : V < K := lt_of_not_ge hNot
      let u := (V + K) / 2
      have hu0 : 0 ≤ u := by
        dsimp [u]
        positivity
      have hVu : V < u := by
        dsimp [u]
        linarith
      have huK : u < K := by
        dsimp [u]
        linarith
      have hEnergy : u ^ 2 * s ^ 2 < 2 * g * d := by
        have hSquares : u ^ 2 < K ^ 2 :=
          (sq_lt_sq₀ hu0 (le_of_lt hK)).2 huK
        nlinarith [sq_pos_of_pos hs]
      have hBound :=
        hLimit.1 (mkSpeed u hu0)
          (avoids_of_energy_lt (mkSpeed u hu0)
            (by simpa [mkSpeed_readout] using hEnergy))
      rw [mkSpeed_readout] at hBound
      exact (not_le_of_gt hVu) (by simpa [V] using hBound)
  apply
    (eq_div_iff
      (pow_ne_zero 2
        (by simpa [s] using (ne_of_gt hs)))).2
  change V ^ 2 * s ^ 2 =
    2 * (|q| / m) * E * d
  rw [hVK, hKenergy]
  ring

/-!
Blueprint: `thm:physics:phyx_mini_0837:target`.

At `45 degrees`, `sin^2(theta) = 1/2`, so the limiting square is
`1.408 * 10^14 (m/s)^2`.  Its positive square root rounds to
`1.19 * 10^7 m/s` at the displayed `10^5 m/s` increment and is closer to
choice D than to every other displayed option.
-/
theorem maximum_initial_speed_matches_choiceD
    (setup : ElectronParallelPlateSetup)
    (hScenario : MatchesElectronParallelPlateScenario setup)
    (hData : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedParallelPlateFigure setup)
    (hElectron : UsesStandardElectronReferenceData setup)
    (hPhysical : HasPhysicalParallelPlateParameters setup)
    (hField : IsUniformUpwardParallelPlateField setup)
    (hMotion : SatisfiesElectronParallelPlateMotionLaws setup) :
    ∃ speedLimit : DimSpeed,
      IsLimitingNonimpactSpeed setup speedLimit ∧
        speedInMetersPerSecond speedLimit ^ 2 = 140800000000000 ∧
        speedInMetersPerSecond speedLimit =
          Real.sqrt 140800000000000 ∧
        RoundsToNearestIncrement
          (speedInMetersPerSecond speedLimit)
          (displayedSpeedInMetersPerSecond .D) 100000 ∧
        displayedSpeedInMetersPerSecond .D = 11900000 ∧
        IsClosestDisplayedSpeed speedLimit .D := by
  let q := chargeInCoulombs setup.electronCharge
  let m := massInKilograms setup.electronMass
  let E :=
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  let d := lengthInMeters setup.plateSeparation
  let s := Real.sin setup.launchAngleRadians
  let g := |q| / m * E
  let N : ℝ := 140800000000000
  have hq : q < 0 := by
    simpa [q] using hElectron.electronChargeIsNegative
  have hm : 0 < m := by
    simpa [m] using hPhysical.positiveElectronMass
  have hE : 0 < E := by
    simpa [E] using hPhysical.positiveFieldStrength
  have hd : 0 < d := by
    simpa [d] using hPhysical.positivePlateSeparation
  have hs : 0 < s := by
    apply Real.sin_pos_of_pos_of_lt_pi hPhysical.launchAnglePositive
    nlinarith [hPhysical.launchAngleAcute, Real.pi_pos]
  have hg : 0 < g := by
    dsimp [g]
    exact mul_pos (div_pos (abs_pos.mpr (ne_of_lt hq)) hm) hE
  have hN : 0 ≤ N := by
    norm_num [N]
  have hsSquare : s ^ 2 = 1 / 2 := by
    dsimp [s]
    rw [hData.launchAngleIsFortyFiveDegrees, Real.sin_pi_div_four,
      div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hCutoff : 2 * g * d = N * s ^ 2 := by
    have hRatio : |q| / m = 176 / 100 * 10 ^ 11 := by
      simpa [q, m] using hElectron.chargeMagnitudeToMassRatio
    have hFieldStrength : E = 1 * 10 ^ 4 := by
      simpa [E] using hData.fieldStrengthNewtonsPerCoulomb
    have hSeparation : d = 2 / 100 := by
      simpa [d] using hData.plateSeparationMeters
    dsimp only [g]
    rw [hRatio, hFieldStrength, hSeparation, hsSquare]
    norm_num [N]
  have hAcceleration :
      accelerationInMetersPerSecondSquared
          setup.electronAcceleration yAxis = -g := by
    have hNewton := hMotion.newtonsSecondLaw yAxis
    rw [hMotion.verticalElectricForceLaw] at hNewton
    change q * E =
      m * accelerationInMetersPerSecondSquared
        setup.electronAcceleration yAxis at hNewton
    have hAcceleration' :
        accelerationInMetersPerSecondSquared
            setup.electronAcceleration yAxis = q * E / m := by
      apply (eq_div_iff (ne_of_gt hm)).2
      nlinarith
    rw [hAcceleration']
    dsimp [g]
    rw [abs_of_neg hq]
    field_simp
  let mkTime : ∀ t : ℝ, 0 ≤ t → TimeQuantity :=
    fun t ht =>
      CarriesDimension.toDimensionful UnitChoices.SI
        (⟨⟨t, ht⟩⟩ : WithDim T𝓭 NNReal)
  have mkTime_readout (t : ℝ) (ht : 0 ≤ t) :
      timeInSeconds (mkTime t ht) = t := by
    simp only [mkTime, timeInSeconds, nonnegativeSIReadout,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self, one_smul]
    exact NNReal.coe_mk t ht
  have avoids_of_energy_lt (speed : DimSpeed)
      (hEnergy :
        speedInMetersPerSecond speed ^ 2 * s ^ 2 < 2 * g * d) :
      AvoidsNegativePlate setup speed := by
    intro elapsed
    rw [hMotion.verticalTrajectoryLaw, hAcceleration]
    have ht : 0 ≤ timeInSeconds elapsed := by
      change 0 ≤ (((elapsed UnitChoices.SI).val : NNReal) : ℝ)
      exact NNReal.coe_nonneg _
    have hSquare :
        0 ≤
          (g * timeInSeconds elapsed -
              speedInMetersPerSecond speed * s) ^ 2 :=
      sq_nonneg _
    nlinarith
  have not_avoids_of_energy_gt (speed : DimSpeed)
      (hEnergy :
        2 * g * d <
          speedInMetersPerSecond speed ^ 2 * s ^ 2) :
      ¬ AvoidsNegativePlate setup speed := by
    intro hAvoids
    have hv : 0 ≤ speedInMetersPerSecond speed := by
      change 0 ≤ (((speed UnitChoices.SI).val : NNReal) : ℝ)
      exact NNReal.coe_nonneg _
    let t := speedInMetersPerSecond speed * s / g
    have ht : 0 ≤ t := by
      dsimp [t]
      positivity
    have hVertex :
        g * t = speedInMetersPerSecond speed * s := by
      dsimp [t]
      field_simp
    have hAtVertex := hAvoids (mkTime t ht)
    rw [hMotion.verticalTrajectoryLaw, hAcceleration,
      mkTime_readout] at hAtVertex
    have hEnergy' :
        2 * g * d <
          (speedInMetersPerSecond speed * s) ^ 2 := by
      nlinarith
    rw [← hVertex] at hEnergy'
    have hPeak : 2 * d < g * t ^ 2 := by
      apply lt_of_mul_lt_mul_left
        (show g * (2 * d) < g * (g * t ^ 2) by nlinarith)
        (le_of_lt hg)
    nlinarith
  let speedLimit : DimSpeed :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨⟨Real.sqrt N, Real.sqrt_nonneg N⟩⟩ :
        WithDim (L𝓭 * T𝓭⁻¹) NNReal)
  have hSpeedLimit :
      speedInMetersPerSecond speedLimit = Real.sqrt N := by
    simp only [speedLimit, speedInMetersPerSecond,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self, one_smul]
    exact NNReal.coe_mk (Real.sqrt N) (Real.sqrt_nonneg N)
  have hLimit : IsLimitingNonimpactSpeed setup speedLimit := by
    constructor
    · intro speed hAvoids
      rw [hSpeedLimit]
      by_contra hNot
      have hSqrtLess :
          Real.sqrt N < speedInMetersPerSecond speed :=
        lt_of_not_ge hNot
      have hv : 0 ≤ speedInMetersPerSecond speed := by
        change 0 ≤ (((speed UnitChoices.SI).val : NNReal) : ℝ)
        exact NNReal.coe_nonneg _
      have hSquareLess :
          N < speedInMetersPerSecond speed ^ 2 :=
        (Real.sqrt_lt hN hv).mp hSqrtLess
      have hEnergy :
          2 * g * d <
            speedInMetersPerSecond speed ^ 2 * s ^ 2 := by
        nlinarith [
          mul_pos (sub_pos.mpr hSquareLess) (sq_pos_of_pos hs)]
      exact not_avoids_of_energy_gt speed hEnergy hAvoids
    · intro speed hLess
      rw [hSpeedLimit] at hLess
      have hv : 0 ≤ speedInMetersPerSecond speed := by
        change 0 ≤ (((speed UnitChoices.SI).val : NNReal) : ℝ)
        exact NNReal.coe_nonneg _
      have hSquareLess :
          speedInMetersPerSecond speed ^ 2 < N :=
        (Real.lt_sqrt hv).mp hLess
      apply avoids_of_energy_lt
      nlinarith [
        mul_pos (sub_pos.mpr hSquareLess) (sq_pos_of_pos hs)]
  have hSqrtSquare : Real.sqrt N ^ 2 = N :=
    Real.sq_sqrt hN
  have hRoundingLower : (11850000 : ℝ) ≤ Real.sqrt N := by
    apply (Real.le_sqrt (by norm_num) hN).2
    norm_num [N]
  have hRoundingUpper : Real.sqrt N ≤ (11950000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num [N]
  have hBelowChoiceD : Real.sqrt N ≤ (11900000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num [N]
  have hAboveChoiceC : (10000000 : ℝ) ≤ Real.sqrt N := by
    apply (Real.le_sqrt (by norm_num) hN).2
    norm_num [N]
  have hDisplayedA :
      displayedSpeedInMetersPerSecond .A = 13000000 := by
    norm_num [displayedSpeedInMetersPerSecond]
  have hDisplayedB :
      displayedSpeedInMetersPerSecond .B = 53000000 := by
    norm_num [displayedSpeedInMetersPerSecond]
  have hDisplayedC :
      displayedSpeedInMetersPerSecond .C = 10000000 := by
    norm_num [displayedSpeedInMetersPerSecond]
  have hDisplayedD :
      displayedSpeedInMetersPerSecond .D = 11900000 := by
    norm_num [displayedSpeedInMetersPerSecond]
  refine ⟨speedLimit, hLimit, ?_, hSpeedLimit, ?_, ?_, ?_⟩
  · rw [hSpeedLimit, hSqrtSquare]
  · constructor
    · norm_num
    rw [hSpeedLimit, hDisplayedD]
    change |Real.sqrt N - 11900000| ≤ 100000 / 2
    rw [abs_le]
    constructor <;> linarith
  · exact hDisplayedD
  · intro alternative
    rw [hSpeedLimit]
    cases alternative
    · rw [hDisplayedD, hDisplayedA]
      rw [abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
    · rw [hDisplayedD, hDisplayedB]
      rw [abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
    · rw [hDisplayedD, hDisplayedC]
      rw [abs_of_nonpos (by linarith),
        abs_of_nonneg (by linarith)]
      linarith
    · rw [hDisplayedD]

end PhyXMiniProblems.ProblemPhyXMini0837
