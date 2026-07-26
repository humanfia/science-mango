import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Recoil of a gold-197 nucleus after alpha-particle scattering

An alpha particle initially travels horizontally toward a stationary
gold-197 nucleus at `1.50 * 10^7 m/s`.  After the encounter it travels at
`1.49 * 10^7 m/s`, deflected through `49 degrees` into the upper half-plane.
The supplied figure shows the gold nucleus recoiling down and to the right.

Masses, speeds, planar velocities, and planar momenta are unit-independent
Physlib quantities.  Real numbers occur only as named-unit readouts,
dimensionless nuclear counts, angles, qualitative figure coordinates, and
displayed answer values.

Assumption/target boundary:

* `MatchesScatteringProblemData` contains only the two alpha speeds stated in
  the prose.
* `ModelsInitiallyStationaryGoldTarget` exposes the standard textbook
  stationary-target interpretation, which the source needs but does not state
  literally.
* `UsesMassNumberApproximation` supplies the standard textbook approximation
  that the alpha and gold-197 masses are respectively four and 197 atomic
  mass units.
* `MatchesPrimaryScatteringFigure` contains only labels, charge marks,
  qualitative arrow directions, and the displayed `49 degree` angle.
* `InterpretsScatteringFigureGeometry` turns those visible directions and the
  displayed angle into Cartesian component relations; it does not prescribe a
  recoil magnitude.
* `SatisfiesNonrelativisticMomentumLaws` states the general speed-magnitude,
  `p = m v`, and total-linear-momentum conservation laws.
* There are no previous-part results.
* The requested `2.52 * 10^5 m/s` value and answer B occur only in the
  displayed-answer table and theorem conclusion, never in a premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0641

open Dimension

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical rest mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A unit-independent velocity vector in the plane of the scattering figure. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) (Fin 2 → ℝ))

/-- A unit-independent momentum vector in the plane of the scattering figure. -/
abbrev PlanarMomentumQuantity : Type :=
  Dimensionful (Momentum 2)

/-- The two Cartesian directions used in the supplied diagram. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index corresponding to a displayed diagram axis. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .horizontal => 0
  | .vertical => 1

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read one planar velocity component in selected length and time units. -/
def velocityComponentReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocityQuantity) (axis : DiagramAxis) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val axis.toFin

/-- Read a speed magnitude in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read one planar momentum component in coherent selected base units. -/
def momentumComponentReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (momentum : PlanarMomentumQuantity) (axis : DiagramAxis) : ℝ :=
  (momentum {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val axis.toFin

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- SI readout of one planar velocity component. -/
def velocityComponentInMetersPerSecond
    (velocity : PlanarVelocityQuantity) (axis : DiagramAxis) : ℝ :=
  velocityComponentReadout LengthUnit.meters TimeUnit.seconds velocity axis

/-! ## Nuclear identities and scattering states -/

/-- The two physical bodies participating in the encounter. -/
inductive ScatteringBody where
  | alphaParticle
  | gold197Nucleus
  deriving DecidableEq, Fintype, Repr

/-- Nucleon number `A` of each body in the textbook mass approximation. -/
def ScatteringBody.massNumber : ScatteringBody → ℕ
  | .alphaParticle => 4
  | .gold197Nucleus => 197

/-- Proton number `Z`, hence the positive nuclear charge number. -/
def ScatteringBody.atomicNumber : ScatteringBody → ℕ
  | .alphaParticle => 2
  | .gold197Nucleus => 79

/-- Whether a state is before or after the scattering interaction. -/
inductive ScatteringPhase where
  | beforeInteraction
  | afterInteraction
  deriving DecidableEq, Fintype, Repr

/-- Independent kinematic data of one body in one phase of the encounter. -/
structure PlanarMotionState where
  velocity : PlanarVelocityQuantity
  speed : DimSpeed
  momentum : PlanarMomentumQuantity

/-! ## Primary-figure vocabulary -/

/-- Qualitative arrow directions visible in the primary raster. -/
inductive PlanarDirection where
  | positiveHorizontal
  | upperRight
  | lowerRight
  deriving DecidableEq, Repr

/-- Text and symbolic labels visible in the supplied figure. -/
inductive FigureLabel where
  | alphaSymbol
  | gold197Symbol
  | nucleusText
  | deflectionAngle49Degrees
  deriving DecidableEq, Fintype, Repr

/-- Presentation-level data transcribed from the primary image. -/
structure AlphaGoldScatteringFigure where
  labelShown : FigureLabel → Bool
  bodyShown : ScatteringBody → Bool
  displayedPositiveChargeMarks : ScatteringBody → ℕ
  incomingAlphaPathShown : Bool
  outgoingAlphaPathShown : Bool
  goldRecoilArrowShown : Bool
  incomingAlphaDirection : PlanarDirection
  outgoingAlphaDirection : PlanarDirection
  goldRecoilDirection : PlanarDirection
  displayedDeflectionAngleDegrees : ℝ
  alphaDrawnLeftOfGold : Bool

/-!
All independent quantities in the scattering model.  In particular, the
gold recoil speed is an unconstrained dimensionful field here; it is neither
defined from the recorded answer nor fixed by any answer-choice value.
-/
structure AlphaGoldScatteringSetup where
  restMass : ScatteringBody → MassQuantity
  referenceAtomicMassUnit : MassQuantity
  motion : ScatteringBody → ScatteringPhase → PlanarMotionState
  scatteringAngleRadians : ℝ
  figure : AlphaGoldScatteringFigure

/-! ## Stated data, primary-image evidence, and governing laws -/

/-- The two numerical alpha-particle speeds stated in the prose. -/
structure MatchesScatteringProblemData
    (setup : AlphaGoldScatteringSetup) : Prop where
  incidentAlphaSpeedMetersPerSecond :
    speedInMetersPerSecond
        (setup.motion .alphaParticle .beforeInteraction).speed = 15_000_000
  scatteredAlphaSpeedMetersPerSecond :
    speedInMetersPerSecond
        (setup.motion .alphaParticle .afterInteraction).speed = 14_900_000

/-!
The source does not literally say that the gold nucleus is initially at rest,
but that standard target-at-rest idealization is necessary to determine the
recoil from the supplied data.  It is therefore a separate, visible modeling
assumption rather than being presented as a source or figure readout.
-/
structure ModelsInitiallyStationaryGoldTarget
    (setup : AlphaGoldScatteringSetup) : Prop where
  goldInitiallyAtRest :
    ∀ axis,
      velocityComponentInMetersPerSecond
          (setup.motion .gold197Nucleus .beforeInteraction).velocity axis = 0

/-!
The standard mass-number approximation used by this textbook calculation:
each nuclear mass is its nucleon number times one common atomic mass unit.
This fixes only the mass ratio `4 : 197`, not the requested recoil speed.
-/
structure UsesMassNumberApproximation
    (setup : AlphaGoldScatteringSetup) : Prop where
  referenceMassPositive :
    0 < massInKilograms setup.referenceAtomicMassUnit
  massFromNucleonNumber :
    ∀ (body : ScatteringBody) (unit : MassUnit),
      massReadout unit (setup.restMass body) =
        (body.massNumber : ℝ) *
          massReadout unit setup.referenceAtomicMassUnit

/-!
Labels, stylized positive-charge marks, paths, qualitative directions, and the
printed angle read from image 641.  This structure records no velocity
components and no recoil magnitude.
-/
structure MatchesPrimaryScatteringFigure
    (setup : AlphaGoldScatteringSetup) : Prop where
  allLabelsShown : ∀ label, setup.figure.labelShown label = true
  bothBodiesShown : ∀ body, setup.figure.bodyShown body = true
  twoAlphaChargeMarks :
    setup.figure.displayedPositiveChargeMarks .alphaParticle = 2
  fourStylizedGoldChargeMarks :
    setup.figure.displayedPositiveChargeMarks .gold197Nucleus = 4
  incomingAlphaPathShown : setup.figure.incomingAlphaPathShown = true
  outgoingAlphaPathShown : setup.figure.outgoingAlphaPathShown = true
  goldRecoilArrowShown : setup.figure.goldRecoilArrowShown = true
  alphaStartsLeftOfGold : setup.figure.alphaDrawnLeftOfGold = true
  incomingDirection :
    setup.figure.incomingAlphaDirection = .positiveHorizontal
  outgoingDirection : setup.figure.outgoingAlphaDirection = .upperRight
  recoilDirection : setup.figure.goldRecoilDirection = .lowerRight
  displayedAngleIs49Degrees :
    setup.figure.displayedDeflectionAngleDegrees = 49

/-!
Cartesian interpretation of the primary figure.  The green recoil arrow fixes
only the signs of its velocity components; it does not fix their magnitude.
-/
structure InterpretsScatteringFigureGeometry
    (setup : AlphaGoldScatteringSetup) : Prop where
  angleConversion :
    setup.scatteringAngleRadians =
      setup.figure.displayedDeflectionAngleDegrees * Real.pi / 180
  incomingAlphaAlongHorizontal :
    velocityComponentInMetersPerSecond
        (setup.motion .alphaParticle .beforeInteraction).velocity .horizontal =
      speedInMetersPerSecond
        (setup.motion .alphaParticle .beforeInteraction).speed ∧
    velocityComponentInMetersPerSecond
        (setup.motion .alphaParticle .beforeInteraction).velocity .vertical = 0
  outgoingAlphaAtDisplayedAngle :
    velocityComponentInMetersPerSecond
        (setup.motion .alphaParticle .afterInteraction).velocity .horizontal =
      speedInMetersPerSecond
          (setup.motion .alphaParticle .afterInteraction).speed *
        Real.cos setup.scatteringAngleRadians ∧
    velocityComponentInMetersPerSecond
        (setup.motion .alphaParticle .afterInteraction).velocity .vertical =
      speedInMetersPerSecond
          (setup.motion .alphaParticle .afterInteraction).speed *
        Real.sin setup.scatteringAngleRadians
  recoilArrowComponentSigns :
    0 < velocityComponentInMetersPerSecond
        (setup.motion .gold197Nucleus .afterInteraction).velocity .horizontal ∧
      velocityComponentInMetersPerSecond
          (setup.motion .gold197Nucleus .afterInteraction).velocity .vertical < 0

/-!
The nonrelativistic laws used by the solution, stated in arbitrary coherent
units: speed is the Euclidean magnitude of velocity, `p = m v` componentwise,
and total planar linear momentum is conserved.  These are general governing
relations and contain no numerical recoil-speed conclusion.
-/
structure SatisfiesNonrelativisticMomentumLaws
    (setup : AlphaGoldScatteringSetup) : Prop where
  speedIsVelocityMagnitude :
    ∀ (body : ScatteringBody) (phase : ScatteringPhase)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit (setup.motion body phase).speed =
        Real.sqrt
          (velocityComponentReadout lengthUnit timeUnit
                (setup.motion body phase).velocity .horizontal ^ 2 +
            velocityComponentReadout lengthUnit timeUnit
                (setup.motion body phase).velocity .vertical ^ 2)
  momentumEqualsMassTimesVelocity :
    ∀ (body : ScatteringBody) (phase : ScatteringPhase)
        (axis : DiagramAxis) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      momentumComponentReadout massUnit lengthUnit timeUnit
          (setup.motion body phase).momentum axis =
        massReadout massUnit (setup.restMass body) *
          velocityComponentReadout lengthUnit timeUnit
            (setup.motion body phase).velocity axis
  totalMomentumConservation :
    ∀ (axis : DiagramAxis) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      momentumComponentReadout massUnit lengthUnit timeUnit
          (setup.motion .alphaParticle .beforeInteraction).momentum axis +
        momentumComponentReadout massUnit lengthUnit timeUnit
          (setup.motion .gold197Nucleus .beforeInteraction).momentum axis =
      momentumComponentReadout massUnit lengthUnit timeUnit
          (setup.motion .alphaParticle .afterInteraction).momentum axis +
        momentumComponentReadout massUnit lengthUnit timeUnit
          (setup.motion .gold197Nucleus .afterInteraction).momentum axis

/-! ## Displayed answers and target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Recoil speed printed beside each answer, in metres per second. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 248_000
  | .B => 252_000
  | .C => 256_000
  | .D => 262_000

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed choice is uniquely closest to the modeled gold recoil speed. -/
def IsUniqueClosestDisplayedRecoilSpeed
    (setup : AlphaGoldScatteringSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |speedInMetersPerSecond
          (setup.motion .gold197Nucleus .afterInteraction).speed -
        choice.speedInMetersPerSecond| <
      |speedInMetersPerSecond
          (setup.motion .gold197Nucleus .afterInteraction).speed -
        other.speedInMetersPerSecond|

/-!
Momentum conservation gives a gold recoil speed of approximately
`2.52 * 10^5 m/s`: it lies within `500 m/s` of the three-significant-figure
value `252000 m/s`, and B is the unique closest displayed choice.

This formalizes `thm:physics:phyx_mini_0641:target`.  Neither the rounding
bound nor the assertion that B is closest occurs in any data, stationary-
target, figure, geometry, mass, or governing-law premise.
-/
theorem problem_phyx_mini_0641
    (setup : AlphaGoldScatteringSetup)
    (h_data : MatchesScatteringProblemData setup)
    (h_stationary : ModelsInitiallyStationaryGoldTarget setup)
    (h_mass : UsesMassNumberApproximation setup)
    (h_figure : MatchesPrimaryScatteringFigure setup)
    (h_geometry : InterpretsScatteringFigureGeometry setup)
    (h_laws : SatisfiesNonrelativisticMomentumLaws setup) :
    |speedInMetersPerSecond
          (setup.motion .gold197Nucleus .afterInteraction).speed - 252_000| ≤
        500 ∧
      IsUniqueClosestDisplayedRecoilSpeed setup .B := by
  let atomicMassReadout : ℝ :=
    massReadout MassUnit.kilograms setup.referenceAtomicMassUnit
  let recoilX : ℝ :=
    velocityComponentReadout LengthUnit.meters TimeUnit.seconds
      (setup.motion .gold197Nucleus .afterInteraction).velocity .horizontal
  let recoilY : ℝ :=
    velocityComponentReadout LengthUnit.meters TimeUnit.seconds
      (setup.motion .gold197Nucleus .afterInteraction).velocity .vertical
  let recoilSpeed : ℝ :=
    speedReadout LengthUnit.meters TimeUnit.seconds
      (setup.motion .gold197Nucleus .afterInteraction).speed

  have hAtomicMassPositive : 0 < atomicMassReadout := by
    simpa [atomicMassReadout, massInKilograms] using
      h_mass.referenceMassPositive
  have hAlphaMass :
      massReadout MassUnit.kilograms
          (setup.restMass .alphaParticle) =
        4 * atomicMassReadout := by
    simpa [atomicMassReadout, ScatteringBody.massNumber] using
      h_mass.massFromNucleonNumber
        ScatteringBody.alphaParticle MassUnit.kilograms
  have hGoldMass :
      massReadout MassUnit.kilograms
          (setup.restMass .gold197Nucleus) =
        197 * atomicMassReadout := by
    simpa [atomicMassReadout, ScatteringBody.massNumber] using
      h_mass.massFromNucleonNumber
        ScatteringBody.gold197Nucleus MassUnit.kilograms
  have hIncidentSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .alphaParticle .beforeInteraction).speed =
        15_000_000 := by
    simpa [speedInMetersPerSecond] using
      h_data.incidentAlphaSpeedMetersPerSecond
  have hScatteredSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .alphaParticle .afterInteraction).speed =
        14_900_000 := by
    simpa [speedInMetersPerSecond] using
      h_data.scatteredAlphaSpeedMetersPerSecond
  have hIncomingX :
      velocityComponentReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .alphaParticle .beforeInteraction).velocity
          .horizontal =
        speedReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .alphaParticle .beforeInteraction).speed := by
    simpa [velocityComponentInMetersPerSecond, speedInMetersPerSecond] using
      h_geometry.incomingAlphaAlongHorizontal.1
  have hIncomingY :
      velocityComponentReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .alphaParticle .beforeInteraction).velocity
          .vertical = 0 := by
    simpa [velocityComponentInMetersPerSecond] using
      h_geometry.incomingAlphaAlongHorizontal.2
  have hOutgoingX :
      velocityComponentReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .alphaParticle .afterInteraction).velocity
          .horizontal =
        speedReadout LengthUnit.meters TimeUnit.seconds
            (setup.motion .alphaParticle .afterInteraction).speed *
          Real.cos setup.scatteringAngleRadians := by
    simpa [velocityComponentInMetersPerSecond, speedInMetersPerSecond] using
      h_geometry.outgoingAlphaAtDisplayedAngle.1
  have hOutgoingY :
      velocityComponentReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .alphaParticle .afterInteraction).velocity
          .vertical =
        speedReadout LengthUnit.meters TimeUnit.seconds
            (setup.motion .alphaParticle .afterInteraction).speed *
          Real.sin setup.scatteringAngleRadians := by
    simpa [velocityComponentInMetersPerSecond, speedInMetersPerSecond] using
      h_geometry.outgoingAlphaAtDisplayedAngle.2
  have hInitialGoldX :
      velocityComponentReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .gold197Nucleus .beforeInteraction).velocity
          .horizontal = 0 := by
    simpa [velocityComponentInMetersPerSecond] using
      h_stationary.goldInitiallyAtRest DiagramAxis.horizontal
  have hInitialGoldY :
      velocityComponentReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .gold197Nucleus .beforeInteraction).velocity
          .vertical = 0 := by
    simpa [velocityComponentInMetersPerSecond] using
      h_stationary.goldInitiallyAtRest DiagramAxis.vertical
  have hAngle :
      setup.scatteringAngleRadians = 49 * Real.pi / 180 := by
    rw [h_geometry.angleConversion, h_figure.displayedAngleIs49Degrees]

  have hMomentumX :=
    h_laws.totalMomentumConservation DiagramAxis.horizontal
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  simp only [h_laws.momentumEqualsMassTimesVelocity] at hMomentumX
  rw [hAlphaMass, hGoldMass, hIncomingX, hIncidentSpeed, hInitialGoldX,
    hOutgoingX, hScatteredSpeed] at hMomentumX
  change
    4 * atomicMassReadout * 15_000_000 +
        197 * atomicMassReadout * 0 =
      4 * atomicMassReadout *
          (14_900_000 * Real.cos setup.scatteringAngleRadians) +
        197 * atomicMassReadout * recoilX at hMomentumX
  have hMomentumXFactored :
      atomicMassReadout *
          (4 * 15_000_000 -
            4 * (14_900_000 * Real.cos setup.scatteringAngleRadians) -
            197 * recoilX) = 0 := by
    nlinarith only [hMomentumX]
  have hRecoilXFactor :
      4 * 15_000_000 -
          4 * (14_900_000 * Real.cos setup.scatteringAngleRadians) -
          197 * recoilX = 0 :=
    (mul_eq_zero.mp hMomentumXFactored).resolve_left
      (ne_of_gt hAtomicMassPositive)
  have hRecoilX :
      recoilX =
        (4 / 197 : ℝ) *
          (15_000_000 -
            14_900_000 * Real.cos setup.scatteringAngleRadians) := by
    nlinarith only [hRecoilXFactor]

  have hMomentumY :=
    h_laws.totalMomentumConservation DiagramAxis.vertical
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  simp only [h_laws.momentumEqualsMassTimesVelocity] at hMomentumY
  rw [hAlphaMass, hGoldMass, hIncomingY, hInitialGoldY,
    hOutgoingY, hScatteredSpeed] at hMomentumY
  change
    4 * atomicMassReadout * 0 + 197 * atomicMassReadout * 0 =
      4 * atomicMassReadout *
          (14_900_000 * Real.sin setup.scatteringAngleRadians) +
        197 * atomicMassReadout * recoilY at hMomentumY
  have hMomentumYFactored :
      atomicMassReadout *
          (4 * (14_900_000 * Real.sin setup.scatteringAngleRadians) +
            197 * recoilY) = 0 := by
    nlinarith only [hMomentumY]
  have hRecoilYFactor :
      4 * (14_900_000 * Real.sin setup.scatteringAngleRadians) +
          197 * recoilY = 0 :=
    (mul_eq_zero.mp hMomentumYFactored).resolve_left
      (ne_of_gt hAtomicMassPositive)
  have hRecoilY :
      recoilY =
        -(4 / 197 : ℝ) *
          (14_900_000 * Real.sin setup.scatteringAngleRadians) := by
    nlinarith only [hRecoilYFactor]

  have hSpeedMagnitude :=
    h_laws.speedIsVelocityMagnitude ScatteringBody.gold197Nucleus
      ScatteringPhase.afterInteraction LengthUnit.meters TimeUnit.seconds
  change recoilSpeed = Real.sqrt (recoilX ^ 2 + recoilY ^ 2)
    at hSpeedMagnitude
  have hRecoilSpeedNonnegative : 0 ≤ recoilSpeed := by
    rw [hSpeedMagnitude]
    exact Real.sqrt_nonneg _
  have hRecoilSpeedSq :
      recoilSpeed ^ 2 = recoilX ^ 2 + recoilY ^ 2 := by
    rw [hSpeedMagnitude, Real.sq_sqrt]
    exact add_nonneg (sq_nonneg recoilX) (sq_nonneg recoilY)
  have hRecoilSpeedSqFormula :
      (197 : ℝ) ^ 2 * recoilSpeed ^ 2 =
        16 *
          (15_000_000 ^ 2 + 14_900_000 ^ 2 -
            2 * 15_000_000 * 14_900_000 *
              Real.cos setup.scatteringAngleRadians) := by
    rw [hRecoilX, hRecoilY] at hRecoilSpeedSq
    nlinarith only [hRecoilSpeedSq,
      Real.cos_sq_add_sin_sq setup.scatteringAngleRadians]

  have complexCosBoundSix {z : ℂ} (hz : ‖z‖ ≤ 1) :
      ‖Complex.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24)‖ ≤
        ‖z‖ ^ 6 * (7 / 4320) := by
    calc
      ‖Complex.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24)‖ =
          ‖(Complex.exp (-z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (-z * Complex.I) ^ n / n.factorial) / 2 +
            (Complex.exp (z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (z * Complex.I) ^ n / n.factorial) / 2‖ := by
        simp [Complex.cos, field, Finset.sum_range_succ, Nat.factorial]
        grind [Complex.I_sq, two_ne_zero]
      _ ≤ ‖Complex.exp (-z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (-z * Complex.I) ^ n / n.factorial‖ / 2 +
            ‖Complex.exp (z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (z * Complex.I) ^ n / n.factorial‖ / 2 := by
        grw [norm_add_le]
        simp
      _ ≤ ‖-z * Complex.I‖ ^ 6 *
                (Nat.succ 6 *
                  (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 +
            ‖z * Complex.I‖ ^ 6 *
                (Nat.succ 6 *
                  (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 := by
        grw [Complex.exp_bound (by simpa) (by simp),
          Complex.exp_bound (by simpa) (by simp)]
      _ ≤ ‖z‖ ^ 6 * (7 / 4320) := by
        norm_num
  have cosBoundSix {x : ℝ} (hx : |x| ≤ 1) :
      |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤
        |x| ^ 6 * (7 / 4320) := by
    simpa [← Complex.ofReal_cos, ← Real.norm_eq_abs,
      ← Complex.norm_real] using
      complexCosBoundSix (z := (x : ℂ)) (by simpa using hx)

  have hPiLower : (3141 / 1000 : ℝ) < Real.pi := by
    let x : ℝ := 1047 / 2000
    have hxAbs : |x| ≤ 1 := by
      norm_num [x, abs_of_nonneg]
    have hTaylor := abs_le.mp (cosBoundSix hxAbs)
    rw [abs_of_nonneg (by norm_num [x])] at hTaylor
    have hCosXLower : (86606 / 100000 : ℝ) ≤ Real.cos x := by
      norm_num [x] at hTaylor ⊢
      nlinarith only [hTaylor.1]
    have hCosXPositive : 0 < Real.cos x := by
      nlinarith only [hCosXLower]
    have hSumNonnegative :
        0 ≤ Real.cos x + 86606 / 100000 := by
      nlinarith only [hCosXLower]
    have hSquareLower :=
      mul_nonneg
        (sub_nonneg.mpr hCosXLower)
        hSumNonnegative
    have hTripleFactorPositive :
        0 < 4 * Real.cos x ^ 2 - 3 := by
      norm_num at hSquareLower ⊢
      nlinarith only [hSquareLower]
    have hCosTriplePositive :
        0 < Real.cos (3141 / 2000 : ℝ) := by
      rw [show (3141 / 2000 : ℝ) = 3 * x by norm_num [x],
        Real.cos_three_mul]
      have hProduct :=
        mul_pos hCosXPositive hTripleFactorPositive
      nlinarith only [hProduct]
    by_contra h
    have hOrder : Real.pi / 2 ≤ (3141 / 2000 : ℝ) := by
      norm_num at h ⊢
      linarith only [h]
    have hCosNonpositive :
        Real.cos (3141 / 2000 : ℝ) ≤ 0 := by
      have hle := Real.cos_le_cos_of_nonneg_of_le_pi
        (x := Real.pi / 2) (y := (3141 / 2000 : ℝ))
        (by linarith only [Real.pi_pos])
        (by linarith only [Real.two_le_pi])
        hOrder
      simpa using hle
    linarith only [hCosTriplePositive, hCosNonpositive]
  have hPiUpper : Real.pi < (1257 / 400 : ℝ) := by
    have hTaylor := abs_le.mp
      (cosBoundSix (x := (419 / 800 : ℝ))
        (by norm_num [abs_of_nonneg]))
    rw [abs_of_nonneg (by norm_num)] at hTaylor
    have hCosXUpper :
        Real.cos (419 / 800 : ℝ) ≤ (86602 / 100000 : ℝ) := by
      norm_num at hTaylor ⊢
      nlinarith only [hTaylor.2]
    have hCosXPositive :
        0 < Real.cos (419 / 800 : ℝ) :=
      Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])
    have hSumNonnegative :
        0 ≤ 86602 / 100000 + Real.cos (419 / 800 : ℝ) := by
      nlinarith only [hCosXPositive]
    have hSquareUpper :=
      mul_nonneg
        (sub_nonneg.mpr hCosXUpper)
        hSumNonnegative
    have hTripleFactorNegative :
        4 * Real.cos (419 / 800 : ℝ) ^ 2 - 3 < 0 := by
      norm_num at hSquareUpper ⊢
      nlinarith only [hSquareUpper]
    have hCosTripleNegative :
        Real.cos (1257 / 800 : ℝ) < 0 := by
      rw [show (1257 / 800 : ℝ) = 3 * (419 / 800) by norm_num,
        Real.cos_three_mul]
      have hProduct :=
        mul_neg_of_pos_of_neg hCosXPositive hTripleFactorNegative
      nlinarith only [hProduct]
    by_contra h
    have hOrder : (1257 / 800 : ℝ) ≤ Real.pi / 2 := by
      norm_num at h ⊢
      linarith only [h]
    have hCosNonnegative :
        0 ≤ Real.cos (1257 / 800 : ℝ) := by
      have hle := Real.cos_le_cos_of_nonneg_of_le_pi
        (x := (1257 / 800 : ℝ)) (y := Real.pi / 2)
        (by norm_num) (by linarith only [Real.pi_pos]) hOrder
      simpa using hle
    linarith only [hCosTripleNegative, hCosNonnegative]

  have hCosineBounds :
      (655 / 1000 : ℝ) ≤ Real.cos setup.scatteringAngleRadians ∧
        Real.cos setup.scatteringAngleRadians ≤ (6565 / 10000 : ℝ) := by
    let y : ℝ := 49 * Real.pi / 360
    have hyLower : (10688 / 25000 : ℝ) ≤ y := by
      dsimp [y]
      nlinarith only [hPiLower]
    have hyUpper : y ≤ (21387 / 50000 : ℝ) := by
      dsimp [y]
      nlinarith only [hPiUpper]
    have hyNonnegative : 0 ≤ y := by
      nlinarith only [hyLower]
    have hyAbs : |y| ≤ 1 := by
      rw [abs_of_nonneg hyNonnegative]
      linarith only [hyUpper]
    have hy2Lower :
        (10688 / 25000 : ℝ) ^ 2 ≤ y ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hyLower 2
    have hy2Upper :
        y ^ 2 ≤ (21387 / 50000 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hyNonnegative hyUpper 2
    have hy4Lower :
        (10688 / 25000 : ℝ) ^ 4 ≤ y ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hyLower 4
    have hy4Upper :
        y ^ 4 ≤ (21387 / 50000 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hyNonnegative hyUpper 4
    have hy6Upper :
        y ^ 6 ≤ (21387 / 50000 : ℝ) ^ 6 :=
      pow_le_pow_left₀ hyNonnegative hyUpper 6
    have hTaylor := abs_le.mp (cosBoundSix hyAbs)
    rw [abs_of_nonneg hyNonnegative] at hTaylor
    have hCosYLower : (9099 / 10000 : ℝ) ≤ Real.cos y := by
      nlinarith only [hTaylor.1, hy2Upper, hy4Lower, hy6Upper]
    have hCosYUpper : Real.cos y ≤ (45501 / 50000 : ℝ) := by
      nlinarith only [hTaylor.2, hy2Lower, hy4Upper, hy6Upper]
    have hCosYNonnegative : 0 ≤ Real.cos y := by
      nlinarith only [hCosYLower]
    have hCosYSqLower :
        (9099 / 10000 : ℝ) ^ 2 ≤ Real.cos y ^ 2 :=
      (sq_le_sq₀ (by norm_num) hCosYNonnegative).2 hCosYLower
    have hCosYSqUpper :
        Real.cos y ^ 2 ≤ (45501 / 50000 : ℝ) ^ 2 :=
      (sq_le_sq₀ hCosYNonnegative (by norm_num)).2 hCosYUpper
    rw [hAngle, show (49 : ℝ) * Real.pi / 180 = 2 * y by
      dsimp [y]
      ring, Real.cos_two_mul]
    constructor
    · nlinarith only [hCosYSqLower]
    · nlinarith only [hCosYSqUpper]

  have hRecoilSpeedSqLower :
      (251_500 : ℝ) ^ 2 ≤ recoilSpeed ^ 2 := by
    nlinarith only [hRecoilSpeedSqFormula, hCosineBounds.2]
  have hRecoilSpeedSqUpper :
      recoilSpeed ^ 2 ≤ (252_500 : ℝ) ^ 2 := by
    nlinarith only [hRecoilSpeedSqFormula, hCosineBounds.1]
  have hRecoilSpeedLower : (251_500 : ℝ) ≤ recoilSpeed :=
    (sq_le_sq₀ (by norm_num) hRecoilSpeedNonnegative).1
      hRecoilSpeedSqLower
  have hRecoilSpeedUpper : recoilSpeed ≤ (252_500 : ℝ) :=
    (sq_le_sq₀ hRecoilSpeedNonnegative (by norm_num)).1
      hRecoilSpeedSqUpper
  have hRounded : |recoilSpeed - 252_000| ≤ 500 := by
    rw [abs_le]
    constructor <;> linarith only [hRecoilSpeedLower, hRecoilSpeedUpper]

  change |recoilSpeed - 252_000| ≤ 500 ∧
    IsUniqueClosestDisplayedRecoilSpeed setup .B
  refine ⟨hRounded, ?_⟩
  intro other hOther
  cases other with
  | A =>
      change
        |recoilSpeed - 252_000| <
          |recoilSpeed - 248_000|
      have hRight :
          |recoilSpeed - 248_000| = recoilSpeed - 248_000 :=
        abs_of_nonneg (by linarith only [hRecoilSpeedLower])
      rw [hRight]
      linarith only [hRounded, hRecoilSpeedLower]
  | B =>
      exact (hOther rfl).elim
  | C =>
      change
        |recoilSpeed - 252_000| <
          |recoilSpeed - 256_000|
      have hRight :
          |recoilSpeed - 256_000| = -(recoilSpeed - 256_000) :=
        abs_of_nonpos (by linarith only [hRecoilSpeedUpper])
      rw [hRight]
      linarith only [hRounded, hRecoilSpeedUpper]
  | D =>
      change
        |recoilSpeed - 252_000| <
          |recoilSpeed - 262_000|
      have hRight :
          |recoilSpeed - 262_000| = -(recoilSpeed - 262_000) :=
        abs_of_nonpos (by linarith only [hRecoilSpeedUpper])
      rw [hRight]
      linarith only [hRounded, hRecoilSpeedUpper]

end PhyXMiniProblems.ProblemPhyXMini0641
