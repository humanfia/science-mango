import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.ClassicalMechanics.RigidBody.SolidSphere
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0789

open Dimension

/-!
# Translational speed of a boulder after rolling onto ice

A solid uniform spherical boulder starts from rest at the top of a `50.0 m`
hill.  The upper half is rough enough for rolling without slipping, while the
lower half is smooth ice and exerts no friction.  Total mechanical energy is
conserved and rolling friction is neglected.

The dimensionful physical quantities below use Physlib's unit-independent
`Dimensionful` interface.  Real numbers occur only as coherent-SI readouts,
dimensionless ratios, schematic figure data, and displayed answer values.
In particular, the bottom speed is an independent field of the setup; it is
not defined from `29.0 m/s` or from the formula to be proved.

Assumption/target split:

* governing laws: the solid-sphere inertia law, the translational and
  rotational kinetic-energy formulas, gravitational potential energy,
  segment-by-segment conservation of total mechanical energy, rolling without
  slipping at the rough/ice transition, and preservation of angular speed on
  the torque-free ice segment;
* previous-part results: none;
* figure/data readouts: a `50.0 m` total vertical drop, the rough and smooth
  labels, the boulder at the summit, the halfway transition, zero bottom
  height, rest at the summit, and standard gravity `9.8 m/s^2`;
* current target conclusions: the exact coherent-SI bottom-speed readout
  `sqrt 840`, agreement with the displayed `29.0 m/s`, and unique selection of
  answer B.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Angular speed has inverse-time dimension because radians are dimensionless. -/
def angularSpeedDimension : Dimension :=
  T𝓭⁻¹

/-- A scalar moment of inertia has physical dimension `M L²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative translational-speed magnitude. -/
abbrev SpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A nonnegative angular-speed magnitude about the boulder's rolling axis. -/
abbrev AngularSpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative scalar moment of inertia about an axis through the center. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Mechanical energy, with physical dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in coherent-SI kilograms as a nonnegative real. -/
def massInKilogramsNNReal (mass : MassQuantity) : NNReal :=
  (mass UnitChoices.SI).val

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (massInKilogramsNNReal mass : ℝ)

/-- Read a physical length in coherent-SI metres as a nonnegative real. -/
def lengthInMetersNNReal (length : LengthQuantity) : NNReal :=
  (length UnitChoices.SI).val

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (lengthInMetersNNReal length : ℝ)

/-- Read a speed magnitude in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitudeQuantity) : ℝ :=
  (((speed UnitChoices.SI).val : NNReal) : ℝ)

/-- Read an angular-speed magnitude in radians per coherent-SI second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedMagnitudeQuantity) : ℝ :=
  (((angularSpeed UnitChoices.SI).val : NNReal) : ℝ)

/-- Read an acceleration magnitude in coherent-SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  (((acceleration UnitChoices.SI).val : NNReal) : ℝ)

/-- Read a central moment of inertia in coherent-SI kilogram square metres. -/
def momentOfInertiaInKilogramSquareMeters
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  (((inertia UnitChoices.SI).val : NNReal) : ℝ)

/-- Read a physical mechanical energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Hill, surface, and primary-figure vocabulary -/

/-- The three states needed for the endpoint energy calculation. -/
inductive HillLocation where
  | summit
  | roughIceTransition
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- The two halves of the hill distinguished in the problem. -/
inductive HillSegment where
  | upperHalf
  | lowerHalf
  deriving DecidableEq, Fintype, Repr

/-- Physical contact regime assigned to a hill segment by the prose. -/
inductive SurfaceRegime where
  | roughEnoughForRollingWithoutSlip
  | frictionlessIce
  deriving DecidableEq, Repr

/-- The mass-distribution and shape idealization stated for the boulder. -/
inductive BoulderModel where
  | solidUniformSphere
  deriving DecidableEq, Repr

/-- Treatment of rolling resistance requested in the problem. -/
inductive RollingResistanceModel where
  | neglected
  deriving DecidableEq, Repr

/-- Literal words printed on the two portions of the slope. -/
inductive FigureSurfaceLabel where
  | rough
  | smooth
  deriving DecidableEq, Fintype, Repr

/-- Physical objects visibly represented in image `789.png`. -/
inductive FigureObject where
  | sphericalBoulder
  | hillSlope
  | verticalHeightArrow
  | dottedBottomReference
  deriving DecidableEq, Fintype, Repr

/-- Literal labels printed in image `789.png`. -/
inductive FigureLabel where
  | rough
  | smooth
  | heightFiftyPointZeroMeters
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and printed data transcribed from the primary bitmap.  The image
contains no numerical bottom-speed value.
-/
structure BoulderHillFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  surfaceLabel : HillSegment → FigureSurfaceLabel
  printedTotalHeight : LengthQuantity
  boulderLocation : HillLocation
  transitionBetweenSurfaceLabelsShown : Bool
  heightArrowRunsFromSummitToBottomReference : Bool
  dottedReferenceIsAtBottom : Bool
  containsNumericalBottomSpeed : Bool

/-! ## Independent physical setup -/

/-!
The boulder's parameters and observables at the three named locations.  The
SI rigid body and angular-velocity vectors provide a bridge to Physlib's
three-dimensional rigid-body mechanics.  No field is defined from an answer
choice or from the requested bottom-speed formula.
-/
structure RollingBoulderSetup where
  boulderModel : BoulderModel
  rollingResistanceModel : RollingResistanceModel
  surfaceRegime : HillSegment → SurfaceRegime
  boulderMass : MassQuantity
  boulderRadius : LengthQuantity
  centralMomentOfInertia : MomentOfInertiaQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  heightAboveBottom : HillLocation → LengthQuantity
  translationalSpeed : HillLocation → SpeedMagnitudeQuantity
  angularSpeed : HillLocation → AngularSpeedMagnitudeQuantity
  totalMechanicalEnergy : HillLocation → EnergyQuantity
  rigidBodySI : RigidBody 3
  rollingAxis : Fin 3
  angularVelocityVectorRadiansPerSecond : HillLocation → Fin 3 → ℝ
  figure : BoulderHillFigure

/-! ## Physical energy components -/

/-- Coherent-SI translational kinetic energy `1/2 m v²`. -/
def translationalKineticEnergyInJoules
    (setup : RollingBoulderSetup) (location : HillLocation) : ℝ :=
  (1 / 2 : ℝ) * massInKilograms setup.boulderMass *
    speedInMetersPerSecond (setup.translationalSpeed location) ^ 2

/-- Coherent-SI rotational kinetic energy `1/2 I ω²`. -/
def rotationalKineticEnergyInJoules
    (setup : RollingBoulderSetup) (location : HillLocation) : ℝ :=
  (1 / 2 : ℝ) *
    momentOfInertiaInKilogramSquareMeters setup.centralMomentOfInertia *
    angularSpeedInRadiansPerSecond (setup.angularSpeed location) ^ 2

/-- Coherent-SI gravitational potential energy `m g h`, with zero at the bottom. -/
def gravitationalPotentialEnergyInJoules
    (setup : RollingBoulderSetup) (location : HillLocation) : ℝ :=
  massInKilograms setup.boulderMass *
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
    lengthInMeters (setup.heightAboveBottom location)

/-- Sum of the translational, rotational, and gravitational energy components. -/
def mechanicalEnergyFromComponentsInJoules
    (setup : RollingBoulderSetup) (location : HillLocation) : ℝ :=
  translationalKineticEnergyInJoules setup location +
    rotationalKineticEnergyInJoules setup location +
    gravitationalPotentialEnergyInJoules setup location

/-! ## Scenario, data, figure evidence, and governing laws -/

/-- Qualitative physical scenario stated in the problem. -/
structure MatchesRollingBoulderScenario (setup : RollingBoulderSetup) : Prop where
  boulderIsSolidUniformSphere :
    setup.boulderModel = .solidUniformSphere
  upperHillIsRoughEnoughForNoSlip :
    setup.surfaceRegime .upperHalf = .roughEnoughForRollingWithoutSlip
  lowerHillIsFrictionlessIce :
    setup.surfaceRegime .lowerHalf = .frictionlessIce
  rollingResistanceIsNeglected :
    setup.rollingResistanceModel = .neglected

/-!
Numerical physical readouts from the prose.  Interpreting the top and lower
"halves" as equal vertical drops gives transition height `25 m`, the
interpretation selected by the recorded answer.  No bottom speed occurs here.
-/
structure MatchesProblemReadouts (setup : RollingBoulderSetup) : Prop where
  summitHeightMeters :
    lengthInMeters (setup.heightAboveBottom .summit) = 50
  halfwayTransitionHeightMeters :
    lengthInMeters (setup.heightAboveBottom .roughIceTransition) = 25
  bottomHeightMeters :
    lengthInMeters (setup.heightAboveBottom .bottom) = 0
  summitTranslationalSpeedIsZero :
    speedInMetersPerSecond (setup.translationalSpeed .summit) = 0
  summitAngularSpeedIsZero :
    angularSpeedInRadiansPerSecond (setup.angularSpeed .summit) = 0
  standardGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      (49 : ℝ) / 5

/-- Objects, labels, and qualitative geometry visible in the supplied image. -/
structure MatchesPrimaryFigure (setup : RollingBoulderSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  upperSegmentPrintedRough :
    setup.figure.surfaceLabel .upperHalf = .rough
  lowerSegmentPrintedSmooth :
    setup.figure.surfaceLabel .lowerHalf = .smooth
  printedHeightIsFiftyMeters :
    lengthInMeters setup.figure.printedTotalHeight = 50
  printedHeightMatchesPhysicalSummit :
    setup.figure.printedTotalHeight = setup.heightAboveBottom .summit
  boulderDrawnAtSummit :
    setup.figure.boulderLocation = .summit
  surfaceTransitionShown :
    setup.figure.transitionBetweenSurfaceLabelsShown = true
  heightArrowSpansWholeDrop :
    setup.figure.heightArrowRunsFromSummitToBottomReference = true
  dottedLineMarksBottom :
    setup.figure.dottedReferenceIsAtBottom = true
  noBottomSpeedPrinted :
    setup.figure.containsNumericalBottomSpeed = false

/-- Positivity and nondegeneracy of the material boulder and gravity. -/
structure HasPhysicalBoulderParameters (setup : RollingBoulderSetup) : Prop where
  massPositive : 0 < massInKilograms setup.boulderMass
  radiusPositive : 0 < lengthInMeters setup.boulderRadius
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-!
Solid-uniform-sphere mechanics and the bridge to Physlib.

The scalar inertia law is the axial consequence of
`RigidBody.solidSphere_inertiaTensor`.  `rigidBodyModel` identifies the
unit-aware problem object with Physlib's SI-coordinate solid sphere, while
`rotationalEnergyAgreesWithPhyslib` checks the scalar energy against
`RigidBody.rotationalKineticEnergy`.  These laws mention no target speed.
-/
structure SatisfiesSolidUniformSphereMechanics
    (setup : RollingBoulderSetup) : Prop where
  rigidBodyModel :
    setup.rigidBodySI =
      RigidBody.solidSphere 3
        (massInKilogramsNNReal setup.boulderMass)
        (lengthInMetersNNReal setup.boulderRadius)
  scalarCentralMomentOfInertia :
    momentOfInertiaInKilogramSquareMeters setup.centralMomentOfInertia =
      (2 / 5 : ℝ) * massInKilograms setup.boulderMass *
        lengthInMeters setup.boulderRadius ^ 2
  inertiaTensorIsIsotropic :
    setup.rigidBodySI.inertiaTensor =
      momentOfInertiaInKilogramSquareMeters setup.centralMomentOfInertia •
        (1 : Matrix (Fin 3) (Fin 3) ℝ)
  angularVelocityIsAlongRollingAxis :
    ∀ location coordinate,
      setup.angularVelocityVectorRadiansPerSecond location coordinate =
        if coordinate = setup.rollingAxis then
          angularSpeedInRadiansPerSecond (setup.angularSpeed location)
        else 0
  rotationalEnergyAgreesWithPhyslib :
    ∀ location,
      rotationalKineticEnergyInJoules setup location =
        RigidBody.rotationalKineticEnergy setup.rigidBodySI
          (setup.angularVelocityVectorRadiansPerSecond location)

/-!
Definition and conservation of total mechanical energy.  Static friction on
the no-slip segment and the frictionless ice segment do no dissipative work,
so the independently stored total energy agrees with the three components and
is conserved across each half of the hill.
-/
structure SatisfiesConservedMechanicalEnergy
    (setup : RollingBoulderSetup) : Prop where
  energyIsComponentSum : ∀ location,
    energyInJoules (setup.totalMechanicalEnergy location) =
      mechanicalEnergyFromComponentsInJoules setup location
  conservedAcrossRoughHalf :
    energyInJoules (setup.totalMechanicalEnergy .summit) =
      energyInJoules (setup.totalMechanicalEnergy .roughIceTransition)
  conservedAcrossIceHalf :
    energyInJoules (setup.totalMechanicalEnergy .roughIceTransition) =
      energyInJoules (setup.totalMechanicalEnergy .bottom)

/-!
Endpoint kinematics supplied by the two contact regimes.  The upper relation
is `v = R ω` at the moment the boulder reaches the ice.  With no friction on
the lower half, there is no torque about the center, so angular speed is
preserved from the transition to the bottom.
-/
structure SatisfiesPiecewiseContactKinematics
    (setup : RollingBoulderSetup) : Prop where
  rollingWithoutSlipAtTransition :
    speedInMetersPerSecond
        (setup.translationalSpeed .roughIceTransition) =
      lengthInMeters setup.boulderRadius *
        angularSpeedInRadiansPerSecond
          (setup.angularSpeed .roughIceTransition)
  angularSpeedPreservedOnIce :
    angularSpeedInRadiansPerSecond
        (setup.angularSpeed .bottom) =
      angularSpeedInRadiansPerSecond
        (setup.angularSpeed .roughIceTransition)

/-! ## Multiple-choice target -/

/-- Labels of the four answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Translational-speed readout in metres per second printed by each choice. -/
def AnswerChoice.speedMetersPerSecond : AnswerChoice → ℝ
  | .A => 31
  | .B => 29
  | .C => 16
  | .D => 22

/-- Dataset metadata: the recorded answer is B; this is never a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
Agreement with a value printed to the nearest tenth of a metre per second.
The half-tenth tolerance represents the precision of `29.0 m/s`.
-/
def MatchesDisplayedPrecision
    (setup : RollingBoulderSetup) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond (setup.translationalSpeed .bottom) -
      choice.speedMetersPerSecond| ≤ 1 / 20

/-- A displayed answer is uniquely closest to the independently derived speed. -/
def IsUniqueClosestAnswer
    (setup : RollingBoulderSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |speedInMetersPerSecond (setup.translationalSpeed .bottom) -
        choice.speedMetersPerSecond| <
      |speedInMetersPerSecond (setup.translationalSpeed .bottom) -
        other.speedMetersPerSecond|

/-!
For a solid sphere, the first `25 m` drop is split between translation and
rotation in the ratio forced by `I = 2/5 mR²`.  The torque-free ice segment
keeps that rotational energy fixed while the remaining `25 m` of potential
energy becomes translational energy.  Consequently the bottom translational
speed is `sqrt 840 m/s`, which rounds to `29.0 m/s` and uniquely selects B.
-/
theorem problem_phyx_mini_0789
    (setup : RollingBoulderSetup)
    (hScenario : MatchesRollingBoulderScenario setup)
    (hData : MatchesProblemReadouts setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalBoulderParameters setup)
    (hSphere : SatisfiesSolidUniformSphereMechanics setup)
    (hEnergy : SatisfiesConservedMechanicalEnergy setup)
    (hContact : SatisfiesPiecewiseContactKinematics setup) :
    speedInMetersPerSecond (setup.translationalSpeed .bottom) =
        Real.sqrt 840 ∧
      MatchesDisplayedPrecision setup .B ∧
      IsUniqueClosestAnswer setup .B := by
  have hBoundaryEnergy := hEnergy.conservedAcrossRoughHalf
  rw [hEnergy.energyIsComponentSum .summit,
    hEnergy.energyIsComponentSum .roughIceTransition] at hBoundaryEnergy
  simp only [mechanicalEnergyFromComponentsInJoules,
    translationalKineticEnergyInJoules,
    rotationalKineticEnergyInJoules,
    gravitationalPotentialEnergyInJoules] at hBoundaryEnergy
  rw [hData.summitTranslationalSpeedIsZero,
    hData.summitAngularSpeedIsZero,
    hData.summitHeightMeters,
    hData.halfwayTransitionHeightMeters,
    hData.standardGravity,
    hSphere.scalarCentralMomentOfInertia,
    hContact.rollingWithoutSlipAtTransition] at hBoundaryEnergy
  have hBoundarySpeedSquared :
      speedInMetersPerSecond
          (setup.translationalSpeed .roughIceTransition) ^ 2 = 350 := by
    rw [hContact.rollingWithoutSlipAtTransition]
    nlinarith [hPhysical.massPositive]
  have hRadiusOmegaSquared :
      (lengthInMeters setup.boulderRadius *
          angularSpeedInRadiansPerSecond
            (setup.angularSpeed .roughIceTransition)) ^ 2 = 350 := by
    rw [← hContact.rollingWithoutSlipAtTransition]
    exact hBoundarySpeedSquared
  have hBottomEnergy :
      energyInJoules (setup.totalMechanicalEnergy .summit) =
        energyInJoules (setup.totalMechanicalEnergy .bottom) :=
    hEnergy.conservedAcrossRoughHalf.trans hEnergy.conservedAcrossIceHalf
  rw [hEnergy.energyIsComponentSum .summit,
    hEnergy.energyIsComponentSum .bottom] at hBottomEnergy
  simp only [mechanicalEnergyFromComponentsInJoules,
    translationalKineticEnergyInJoules,
    rotationalKineticEnergyInJoules,
    gravitationalPotentialEnergyInJoules] at hBottomEnergy
  rw [hData.summitTranslationalSpeedIsZero,
    hData.summitAngularSpeedIsZero,
    hData.summitHeightMeters,
    hData.bottomHeightMeters,
    hData.standardGravity,
    hSphere.scalarCentralMomentOfInertia,
    hContact.angularSpeedPreservedOnIce] at hBottomEnergy
  have hBottomSpeedSquared :
      speedInMetersPerSecond (setup.translationalSpeed .bottom) ^ 2 = 840 := by
    nlinarith [hPhysical.massPositive, hRadiusOmegaSquared]
  have hBottomSpeedNonnegative :
      0 ≤ speedInMetersPerSecond (setup.translationalSpeed .bottom) := by
    exact NNReal.coe_nonneg _
  have hSqrtSquared : Real.sqrt (840 : ℝ) ^ 2 = 840 := by
    norm_num
  have hSqrtNonnegative : 0 ≤ Real.sqrt (840 : ℝ) :=
    Real.sqrt_nonneg _
  have hExact :
      speedInMetersPerSecond (setup.translationalSpeed .bottom) =
        Real.sqrt (840 : ℝ) := by
    nlinarith
  have hSqrtLower : (579 : ℝ) / 20 < Real.sqrt (840 : ℝ) := by
    nlinarith [hSqrtSquared]
  have hSqrtUpper : Real.sqrt (840 : ℝ) < 29 := by
    nlinarith [hSqrtSquared]
  have hRounds :
      |Real.sqrt (840 : ℝ) - 29| < (1 / 20 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hNearestB : IsUniqueClosestAnswer setup .B := by
    intro other hOther
    rw [hExact]
    fin_cases other
    · simp only [AnswerChoice.speedMetersPerSecond]
      rw [abs_of_neg (by nlinarith : Real.sqrt (840 : ℝ) - 29 < 0),
        abs_of_neg (by nlinarith : Real.sqrt (840 : ℝ) - 31 < 0)]
      linarith
    · exact (hOther rfl).elim
    · simp only [AnswerChoice.speedMetersPerSecond]
      rw [abs_of_neg (by nlinarith : Real.sqrt (840 : ℝ) - 29 < 0),
        abs_of_pos (by nlinarith : 0 < Real.sqrt (840 : ℝ) - 16)]
      linarith
    · simp only [AnswerChoice.speedMetersPerSecond]
      rw [abs_of_neg (by nlinarith : Real.sqrt (840 : ℝ) - 29 < 0),
        abs_of_pos (by nlinarith : 0 < Real.sqrt (840 : ℝ) - 22)]
      linarith
  refine ⟨hExact, ?_, hNearestB⟩
  simpa [MatchesDisplayedPrecision, AnswerChoice.speedMetersPerSecond, hExact]
    using le_of_lt hRounds

end PhyXMiniProblems.ProblemPhyXMini0789
