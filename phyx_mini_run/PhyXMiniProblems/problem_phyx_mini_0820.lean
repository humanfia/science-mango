import Mathlib
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0820

open Dimension

/-!
# Cable unwinding from a solid cylinder

A light, nonstretching cable is wrapped around a uniform solid cylinder whose
axis is fixed in frictionless bearings.  A constant tangential force pulls the
cable through a measured distance, starting from rest.  The requested
observable is the cable's final speed.

Physical masses, lengths, force magnitudes, speeds, angular speeds, moments of
inertia, and work are represented by unit-independent Physlib quantities.
Real numbers occur only at explicit unit-readout boundaries, in Physlib's
coherent-SI rigid-body model, and in the values printed in the figure and
answer choices.

Assumption/target boundary:

* `MatchesSuppliedFigure` records only primary-image readouts and geometry.
* `MatchesPhysicalScenario` records the prose idealizations and initial rest.
* the governing `Satisfies...` predicates state generic geometry, solid-
  cylinder inertia, no-slip, constant-force work, and work-energy laws.
* there are no previous-part results.
* the final cable speed and choice `B` occur only in the theorem conclusion
  and in the separate displayed-answer table.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- Force has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Moment of inertia about an axis has physical dimension `M L²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent linear speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative angular speed; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative axial moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Work is represented by Physlib's dimensionful energy type. -/
abbrev WorkQuantity : Type := DimEnergy

/-- Read a mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in coherent-SI newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read a speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Read an axial moment of inertia in kilogram square metres. -/
def momentOfInertiaInKilogramSquareMeters
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read work in coherent-SI joules. -/
def workInJoules (work : WorkQuantity) : ℝ :=
  (work UnitChoices.SI).val

/-! ## Physical setup and primary-image labels -/

/-- The two instants compared by the work-energy calculation. -/
inductive MotionStage where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- The mass-distribution model named in the prose. -/
inductive CylinderMassDistribution where
  | uniformSolidCylinder
  | other
  deriving DecidableEq, Repr

/-- The idealization used for the cable's mass. -/
inductive CableMassModel where
  | negligible
  | massive
  deriving DecidableEq, Repr

/-- Whether the cable changes length while it is pulled. -/
inductive CableStretchModel where
  | nonstretching
  | extensible
  deriving DecidableEq, Repr

/-- The bearing idealization at the cylinder axle. -/
inductive BearingModel where
  | frictionless
  | dissipative
  deriving DecidableEq, Repr

/-- The geometric constraint imposed on the rotation axis. -/
inductive AxisModel where
  | stationaryHorizontal
  | other
  deriving DecidableEq, Repr

/-- The time profile of the external pull. -/
inductive PullForceProfile where
  | constant
  | variable
  deriving DecidableEq, Repr

/-- The kinematic relation between cable and cylinder rim. -/
inductive CableRimContactModel where
  | unwindsWithoutSlipping
  | slips
  deriving DecidableEq, Repr

/-!
Presentation data visible in primary image `820.png`.  The vertical `0.120 m`
dimension arrow spans the full top-to-bottom extent of the cylinder, so it is
modeled as a diameter label rather than as the erroneous radius description in
the auxiliary generated caption.
-/
structure CylinderCableFigure where
  printedForceMagnitudeInNewtons : ℝ
  printedPulledDistanceInMeters : ℝ
  printedCylinderMassInKilograms : ℝ
  printedVerticalCylinderSpanInMeters : ℝ
  forceArrowPointsLeftAlongCable : Bool
  cableIsHorizontalAndTangentAtTop : Bool
  bearingShownAtCylinderCenter : Bool
  axleSupportIsFixedToBase : Bool
  verticalDimensionSpansFullDiameter : Bool

/-!
Independent physical and presentation data for the experiment.  In
particular, `cableSpeed .final` is an observable field, not a definition in
terms of an answer choice or the requested numerical result.

`rigidBodyModelSI` and `angularVelocityVectorSI` supply the coherent-SI data
used by Physlib's rotational kinetic-energy definition.
-/
structure PulledCableCylinderSetup where
  cylinderMass : MassQuantity
  cylinderDiameter : LengthQuantity
  cylinderRadius : LengthQuantity
  appliedForceMagnitude : ForceMagnitudeQuantity
  pulledCableDistance : LengthQuantity
  cableSpeed : MotionStage → SpeedQuantity
  cylinderAngularSpeed : MotionStage → AngularSpeedQuantity
  angularVelocityVectorSI : MotionStage → Fin 3 → ℝ
  axialMomentOfInertia : MomentOfInertiaQuantity
  workDoneByPull : WorkQuantity
  rigidBodyModelSI : RigidBody 3
  massDistribution : CylinderMassDistribution
  cableMassModel : CableMassModel
  cableStretchModel : CableStretchModel
  bearingModel : BearingModel
  axisModel : AxisModel
  pullForceProfile : PullForceProfile
  contactModel : CableRimContactModel
  figure : CylinderCableFigure

/-- The cylinder's horizontal symmetry axis is coordinate axis `2` in the SI model. -/
def cylinderAxis : Fin 3 := 2

/-!
Primary-image evidence and its connection to the physical fields.  This
contains the four displayed inputs and qualitative geometry, but no final
speed or answer-choice value.
-/
structure MatchesSuppliedFigure (setup : PulledCableCylinderSetup) : Prop where
  forceLabel : setup.figure.printedForceMagnitudeInNewtons = 9
  pulledDistanceLabel : setup.figure.printedPulledDistanceInMeters = 2
  massLabel : setup.figure.printedCylinderMassInKilograms = 50
  diameterLabel : setup.figure.printedVerticalCylinderSpanInMeters = 3 / 25
  forceMatchesLabel :
    forceMagnitudeInNewtons setup.appliedForceMagnitude =
      setup.figure.printedForceMagnitudeInNewtons
  pulledDistanceMatchesLabel :
    lengthInMeters setup.pulledCableDistance =
      setup.figure.printedPulledDistanceInMeters
  massMatchesLabel :
    massInKilograms setup.cylinderMass =
      setup.figure.printedCylinderMassInKilograms
  diameterMatchesLabel :
    lengthInMeters setup.cylinderDiameter =
      setup.figure.printedVerticalCylinderSpanInMeters
  pullDirectionIsShown : setup.figure.forceArrowPointsLeftAlongCable = true
  cableTangencyIsShown : setup.figure.cableIsHorizontalAndTangentAtTop = true
  centralBearingIsShown : setup.figure.bearingShownAtCylinderCenter = true
  fixedSupportIsShown : setup.figure.axleSupportIsFixedToBase = true
  dimensionIsDiameter : setup.figure.verticalDimensionSpansFullDiameter = true

/-!
Qualitative problem data and the initial-rest condition.  Frictionless
bearings and a negligible-mass cable identify the cylinder as the only body
whose kinetic energy changes in the work-energy law below.
-/
structure MatchesPhysicalScenario (setup : PulledCableCylinderSetup) : Prop where
  cylinderIsUniformAndSolid :
    setup.massDistribution = .uniformSolidCylinder
  cableIsLight : setup.cableMassModel = .negligible
  cableDoesNotStretch : setup.cableStretchModel = .nonstretching
  bearingsAreFrictionless : setup.bearingModel = .frictionless
  axisIsStationaryAndHorizontal : setup.axisModel = .stationaryHorizontal
  pullIsConstant : setup.pullForceProfile = .constant
  cableUnwindsWithoutSlipping :
    setup.contactModel = .unwindsWithoutSlipping
  initialCableSpeedIsZero :
    speedInMetersPerSecond (setup.cableSpeed .initial) = 0
  initialAngularSpeedIsZero :
    angularSpeedInRadiansPerSecond
      (setup.cylinderAngularSpeed .initial) = 0

/-! ## Geometry and governing mechanics -/

/-- The radius is half the full diameter marked by the vertical figure arrow. -/
structure SatisfiesCylinderGeometry (setup : PulledCableCylinderSetup) : Prop where
  diameterIsTwiceRadius :
    lengthInMeters setup.cylinderDiameter =
      2 * lengthInMeters setup.cylinderRadius

/-!
For a uniform solid cylinder about its symmetry axis,
`I = (1/2) m r²`.  Physlib supplies the general inertia tensor but no theorem
specializing its defining integral to a solid cylinder, so the standard
mass-distribution law is stated explicitly and connected to the SI model.
-/
structure SatisfiesSolidCylinderInertiaLaw
    (setup : PulledCableCylinderSetup) : Prop where
  axialInertiaFormula :
    momentOfInertiaInKilogramSquareMeters setup.axialMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms setup.cylinderMass *
        lengthInMeters setup.cylinderRadius ^ 2
  axialInertiaMatchesRigidBodyModel :
    momentOfInertiaInKilogramSquareMeters setup.axialMomentOfInertia =
      setup.rigidBodyModelSI.inertiaTensor cylinderAxis cylinderAxis

/-!
No slip makes cable speed equal to rim speed `r ω`.  The vector supplied to
Physlib is aligned with the cylinder axis at both stages.
-/
structure SatisfiesNoSlipUnwindingLaw
    (setup : PulledCableCylinderSetup) : Prop where
  cableSpeedEqualsRimSpeed : ∀ stage,
    speedInMetersPerSecond (setup.cableSpeed stage) =
      lengthInMeters setup.cylinderRadius *
        angularSpeedInRadiansPerSecond
          (setup.cylinderAngularSpeed stage)
  angularVelocityAlongCylinderAxis : ∀ stage,
    setup.angularVelocityVectorSI stage = fun i ↦
      if i = cylinderAxis then
        angularSpeedInRadiansPerSecond
          (setup.cylinderAngularSpeed stage)
      else 0

/-!
For a constant force parallel to the cable displacement, the work magnitude is
`F d`.  This is a governing law and does not constrain the requested speed.
-/
structure SatisfiesConstantPullWorkLaw
    (setup : PulledCableCylinderSetup) : Prop where
  workEqualsForceTimesDistance :
    workInJoules setup.workDoneByPull =
      forceMagnitudeInNewtons setup.appliedForceMagnitude *
        lengthInMeters setup.pulledCableDistance

/-!
Because the axis is stationary, the bearings are frictionless, and the cable
is light, the external work becomes the cylinder's increase in rotational
kinetic energy.  The energy is computed by Physlib from the full inertia tensor
and angular-velocity vector.
-/
structure SatisfiesRotationalWorkEnergyLaw
    (setup : PulledCableCylinderSetup) : Prop where
  workIsRotationalKineticEnergyIncrease :
    workInJoules setup.workDoneByPull =
      setup.rigidBodyModelSI.rotationalKineticEnergy
          (setup.angularVelocityVectorSI .final) -
        setup.rigidBodyModelSI.rotationalKineticEnergy
          (setup.angularVelocityVectorSI .initial)

/-! ## Displayed answers and target -/

/-- Labels printed beside the four candidate cable speeds. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside each answer label. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 4 / 5
  | .B => 6 / 5
  | .C => 21 / 10
  | .D => 3

/-- Answer label recorded in the source dataset; it is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed choice exactly matches the physical final cable speed. -/
def IsCorrectDisplayedSpeed
    (setup : PulledCableCylinderSetup) (choice : AnswerChoice) : Prop :=
  speedInMetersPerSecond (setup.cableSpeed .final) =
    displayedSpeedInMetersPerSecond choice

/-!
The constant pull performs `18 J` of work.  With
`I = (1/2) m r²`, `v = r ω`, and zero initial kinetic energy, the work
equation becomes `18 = (1/4) (50) v²`; nonnegativity of `DimSpeed` selects
`v = 6/5 m/s`.  Thus displayed choice B is the unique exact match.

This formalizes `thm:physics:phyx_mini_0820:target`.
-/
theorem problem_phyx_mini_0820
    (setup : PulledCableCylinderSetup)
    (_figure : MatchesSuppliedFigure setup)
    (_scenario : MatchesPhysicalScenario setup)
    (_geometry : SatisfiesCylinderGeometry setup)
    (_inertia : SatisfiesSolidCylinderInertiaLaw setup)
    (_noSlip : SatisfiesNoSlipUnwindingLaw setup)
    (_work : SatisfiesConstantPullWorkLaw setup)
    (_workEnergy : SatisfiesRotationalWorkEnergyLaw setup) :
    speedInMetersPerSecond (setup.cableSpeed .final) = (6 : ℝ) / 5 ∧
      IsCorrectDisplayedSpeed setup .B ∧
      ∀ choice : AnswerChoice,
        IsCorrectDisplayedSpeed setup choice → choice = .B := by
  have hforce :
      forceMagnitudeInNewtons setup.appliedForceMagnitude = 9 :=
    _figure.forceMatchesLabel.trans _figure.forceLabel
  have hdistance :
      lengthInMeters setup.pulledCableDistance = 2 :=
    _figure.pulledDistanceMatchesLabel.trans _figure.pulledDistanceLabel
  have hmass : massInKilograms setup.cylinderMass = 50 :=
    _figure.massMatchesLabel.trans _figure.massLabel
  have hkinetic (stage : MotionStage) :
      setup.rigidBodyModelSI.rotationalKineticEnergy
          (setup.angularVelocityVectorSI stage) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramSquareMeters
            setup.axialMomentOfInertia *
          angularSpeedInRadiansPerSecond
            (setup.cylinderAngularSpeed stage) ^ 2 := by
    rw [RigidBody.rotationalKineticEnergy]
    simp only [dotProduct, Matrix.mulVec]
    simp_rw [_noSlip.angularVelocityAlongCylinderAxis]
    simp [_inertia.axialInertiaMatchesRigidBodyModel]
    ring
  have henergy :=
    _workEnergy.workIsRotationalKineticEnergyIncrease
  rw [_work.workEqualsForceTimesDistance, hforce, hdistance,
    hkinetic, hkinetic, _scenario.initialAngularSpeedIsZero,
    _inertia.axialInertiaFormula, hmass] at henergy
  norm_num at henergy
  have hnoSlipSq := congrArg (fun x : ℝ => x ^ 2)
    (_noSlip.cableSpeedEqualsRimSpeed .final)
  have hspeedNonnegative :
      0 ≤ speedInMetersPerSecond (setup.cableSpeed .final) := by
    unfold speedInMetersPerSecond
    positivity
  have hspeed :
      speedInMetersPerSecond (setup.cableSpeed .final) =
        (6 : ℝ) / 5 := by
    nlinarith [hnoSlipSq]
  refine ⟨hspeed, ?_, ?_⟩
  · simpa [IsCorrectDisplayedSpeed, displayedSpeedInMetersPerSecond]
      using hspeed
  · intro choice hchoice
    cases choice with
    | A =>
        norm_num [IsCorrectDisplayedSpeed,
          displayedSpeedInMetersPerSecond, hspeed] at hchoice
    | B => rfl
    | C =>
        norm_num [IsCorrectDisplayedSpeed,
          displayedSpeedInMetersPerSecond, hspeed] at hchoice
    | D =>
        norm_num [IsCorrectDisplayedSpeed,
          displayedSpeedInMetersPerSecond, hspeed] at hchoice

end PhyXMiniProblems.ProblemPhyXMini0820
