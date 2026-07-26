import Mathlib
import Physlib.Units.WithDim.Energy

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Average force exerted by a pile-driver hammerhead

A `200 kg` steel hammerhead is released from rest at point 1, `3.00 m` above
the top of a vertical I-beam at point 2.  It falls between vertical guide
rails whose constant friction force has magnitude `60 N`, strikes the beam,
and drives its top down by `7.4 cm` to point 3.  Air resistance is neglected.

Mass, length, acceleration, force magnitude, work, and kinetic energy remain
unit-independent dimensionful quantities.  Real numbers are used only for
coherent-SI readouts, the printed answer choices, and the final numerical
relation.

Assumption/target split:

* `MatchesPileDriverScenario` records the steel hammerhead, vertical beam and
  rails, the motion states at points 1--3, constant rail friction, contact
  only during the driving leg, force directions, and the neglected air force.
* `MatchesPileDriverProblemReadouts` records only the supplied mass and guide-
  rail friction readouts.
* `MatchesPrimaryPileDriverFigure` records the three point labels and the two
  distance markers read from image `808.png`.
* `UsesStandardTerrestrialGravity`, `HasPhysicalPileDriverParameters`, and
  `SatisfiesPileDriverWorkEnergyLaws` state parameter conditions and governing
  mechanics laws.  In particular, Newton's third law relates the two contact-
  force magnitudes, while signed work and the work--energy theorem determine
  their value.
* There are no previous-part results.
* The exact average contact force and the selection of answer B occur only in
  the conclusion of `averageForceHammerheadExertsOnBeam`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0808

open Dimension

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Acceleration has dimension length divided by time squared. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has dimension mass times length divided by time squared. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical distance. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude.  Signed effects are represented as work. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Signed physical work and kinetic energy have Physlib's energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Centimetre readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout force

/-- Joule readout of signed physical work or kinetic energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Motion stages, agents, and primary-figure vocabulary -/

/-- The three labels printed beside the pile-driver motion in the image. -/
inductive PileDriverPoint where
  | pointOne
  | pointTwo
  | pointThree
  deriving DecidableEq, Fintype, Repr

/-- The fall to the beam and the subsequent beam-driving motion. -/
inductive MotionLeg where
  | dropToBeam
  | drivingBeam
  deriving DecidableEq, Fintype, Repr

/-- Initial point of each motion leg. -/
def MotionLeg.startPoint : MotionLeg → PileDriverPoint
  | .dropToBeam => .pointOne
  | .drivingBeam => .pointTwo

/-- Final point of each motion leg. -/
def MotionLeg.endPoint : MotionLeg → PileDriverPoint
  | .dropToBeam => .pointTwo
  | .drivingBeam => .pointThree

/-- The three force agents whose work enters the hammerhead energy balance. -/
inductive ForceSource where
  | gravity
  | guideRailFriction
  | beamContact
  deriving DecidableEq, Fintype, Repr

/-- The qualitative instantaneous motion state at a labeled point. -/
inductive HammerheadMotionState where
  | atRest
  | movingDownward
  deriving DecidableEq, Repr

/-- Vertical directions used for motion and force arrows. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Material model stated for the hammerhead. -/
inductive HammerheadMaterial where
  | steel
  | other
  deriving DecidableEq, Repr

/-- Orientation of the I-beam and guide rails. -/
inductive ApparatusOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-!
Literal information transcribed from the primary raster.  The physical
distances attached to the printed markers remain independent of their
numerical readouts in `MatchesPrimaryPileDriverFigure`.
-/
structure PileDriverFigure where
  pointLabelShown : PileDriverPoint → Bool
  hammerheadShownAtPointOne : Bool
  beamTopShownAtPointTwo : Bool
  beamTopShownAtPointThree : Bool
  guideRailsShown : Bool
  downwardMotionArrowShown : Bool
  dropHeightMarker : LengthQuantity
  penetrationDepthMarker : LengthQuantity
  dropMarkerRunsFromPointOneToPointTwo : Bool
  penetrationMarkerRunsFromPointTwoToPointThree : Bool
  pointOneDrawnAbovePointTwo : Bool
  pointTwoDrawnAbovePointThree : Bool

/-! ## Independent pile-driver setup -/

/-!
All unknown observables, especially the two average contact-force magnitudes,
are independent fields.  Work and kinetic energy are likewise not defined
from the requested answer; the governing-law predicate below relates them.
-/
structure PileDriverSetup where
  hammerheadMaterial : HammerheadMaterial
  hammerheadMass : MassQuantity
  dropHeight : LengthQuantity
  beamPenetrationDepth : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  guideRailFrictionMagnitude : ForceMagnitudeQuantity
  averageForceBeamOnHammer : ForceMagnitudeQuantity
  averageForceHammerOnBeam : ForceMagnitudeQuantity
  kineticEnergy : PileDriverPoint → EnergyQuantity
  work : MotionLeg → ForceSource → EnergyQuantity
  motionState : PileDriverPoint → HammerheadMotionState
  motionDirection : MotionLeg → VerticalDirection
  gravityDirection : VerticalDirection
  guideRailFrictionDirection : MotionLeg → VerticalDirection
  beamForceOnHammerDirection : VerticalDirection
  hammerForceOnBeamDirection : VerticalDirection
  beamContactPresent : MotionLeg → Bool
  guideRailFrictionIsConstant : Bool
  airResistanceNeglected : Bool
  beamOrientation : ApparatusOrientation
  guideRailOrientation : ApparatusOrientation
  figure : PileDriverFigure

/-- Physical distance traveled by the hammerhead on either motion leg. -/
def PileDriverSetup.travelDistance
    (setup : PileDriverSetup) : MotionLeg → LengthQuantity
  | .dropToBeam => setup.dropHeight
  | .drivingBeam => setup.beamPenetrationDepth

/-! ## Scenario, numerical data, and figure assumptions -/

/-- Qualitative apparatus, motion, and force information stated in the problem. -/
structure MatchesPileDriverScenario (setup : PileDriverSetup) : Prop where
  steelHammerhead : setup.hammerheadMaterial = .steel
  beamIsVertical : setup.beamOrientation = .vertical
  guideRailsAreVertical : setup.guideRailOrientation = .vertical
  releasedFromRestAtPointOne :
    setup.motionState .pointOne = .atRest
  movingDownwardAtImpactPointTwo :
    setup.motionState .pointTwo = .movingDownward
  stoppedAfterDrivingAtPointThree :
    setup.motionState .pointThree = .atRest
  downwardMotionOnBothLegs :
    ∀ leg, setup.motionDirection leg = .downward
  gravityActsDownward : setup.gravityDirection = .downward
  railFrictionOpposesMotion :
    ∀ leg, setup.guideRailFrictionDirection leg = .upward
  beamForceOnHammerIsUpward :
    setup.beamForceOnHammerDirection = .upward
  hammerForceOnBeamIsDownward :
    setup.hammerForceOnBeamDirection = .downward
  noBeamContactDuringDrop :
    setup.beamContactPresent .dropToBeam = false
  beamContactDuringDriving :
    setup.beamContactPresent .drivingBeam = true
  constantGuideRailFriction :
    setup.guideRailFrictionIsConstant = true
  ignoresAirResistance : setup.airResistanceNeglected = true

/-- Scalar readouts supplied in the prose, excluding the two figure distances. -/
structure MatchesPileDriverProblemReadouts
    (setup : PileDriverSetup) : Prop where
  hammerheadMassKilograms :
    massInKilograms setup.hammerheadMass = 200
  guideRailFrictionNewtons :
    forceInNewtons setup.guideRailFrictionMagnitude = 60

/-- Standard terrestrial gravitational acceleration used by the answer data. -/
structure UsesStandardTerrestrialGravity
    (setup : PileDriverSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-- Labels, alignments, and distance readouts visible in image `808.png`. -/
structure MatchesPrimaryPileDriverFigure
    (setup : PileDriverSetup) : Prop where
  allPointLabelsShown :
    ∀ point, setup.figure.pointLabelShown point = true
  hammerheadAtPointOne : setup.figure.hammerheadShownAtPointOne = true
  initialBeamTopAtPointTwo : setup.figure.beamTopShownAtPointTwo = true
  finalBeamTopAtPointThree : setup.figure.beamTopShownAtPointThree = true
  guideRailsVisible : setup.figure.guideRailsShown = true
  downwardArrowVisible : setup.figure.downwardMotionArrowShown = true
  dropMarkerEndpoints :
    setup.figure.dropMarkerRunsFromPointOneToPointTwo = true
  penetrationMarkerEndpoints :
    setup.figure.penetrationMarkerRunsFromPointTwoToPointThree = true
  pointOneAbovePointTwo : setup.figure.pointOneDrawnAbovePointTwo = true
  pointTwoAbovePointThree : setup.figure.pointTwoDrawnAbovePointThree = true
  dropMarkerMatchesSetup : setup.figure.dropHeightMarker = setup.dropHeight
  penetrationMarkerMatchesSetup :
    setup.figure.penetrationDepthMarker = setup.beamPenetrationDepth
  printedDropHeightMeters :
    lengthInMeters setup.figure.dropHeightMarker = 3
  printedPenetrationDepthCentimeters :
    lengthInCentimeters setup.figure.penetrationDepthMarker = 37 / 5

/-- Positivity and nondegeneracy of the supplied physical magnitudes. -/
structure HasPhysicalPileDriverParameters
    (setup : PileDriverSetup) : Prop where
  hammerheadMassPositive : 0 < massInKilograms setup.hammerheadMass
  dropHeightPositive : 0 < lengthInMeters setup.dropHeight
  penetrationDepthPositive :
    0 < lengthInMeters setup.beamPenetrationDepth
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  guideRailFrictionNonnegative :
    0 ≤ forceInNewtons setup.guideRailFrictionMagnitude

/-!
Governing mechanics laws for the hammerhead:

* at-rest states have zero kinetic energy;
* gravity does positive work `m g s` on each downward leg;
* constant guide-rail friction does negative work `-f s`;
* the I-beam does no work before contact and average work `-F d` while it is
  driven downward;
* the net work on each leg equals the change in hammerhead kinetic energy;
* Newton's third law gives equal magnitudes for the beam-on-hammer and
  hammer-on-beam average contact forces.

These laws contain no numerical value or answer choice for the unknown force.
-/
structure SatisfiesPileDriverWorkEnergyLaws
    (setup : PileDriverSetup) : Prop where
  atRestHasZeroKineticEnergy :
    ∀ point,
      setup.motionState point = .atRest →
        energyInJoules (setup.kineticEnergy point) = 0
  gravitationalWork :
    ∀ leg,
      energyInJoules (setup.work leg .gravity) =
        massInKilograms setup.hammerheadMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters (setup.travelDistance leg)
  guideRailFrictionWork :
    ∀ leg,
      energyInJoules (setup.work leg .guideRailFriction) =
        -(forceInNewtons setup.guideRailFrictionMagnitude *
          lengthInMeters (setup.travelDistance leg))
  beamDoesNoWorkBeforeImpact :
    energyInJoules (setup.work .dropToBeam .beamContact) = 0
  averageBeamContactWorkWhileDriving :
    energyInJoules (setup.work .drivingBeam .beamContact) =
      -(forceInNewtons setup.averageForceBeamOnHammer *
        lengthInMeters setup.beamPenetrationDepth)
  workEnergyTheorem :
    ∀ leg,
      energyInJoules (setup.kineticEnergy leg.endPoint) -
          energyInJoules (setup.kineticEnergy leg.startPoint) =
        energyInJoules (setup.work leg .gravity) +
          energyInJoules (setup.work leg .guideRailFriction) +
          energyInJoules (setup.work leg .beamContact)
  newtonThirdLawContactMagnitude :
    setup.averageForceHammerOnBeam = setup.averageForceBeamOnHammer

/-! ## Displayed choices and target -/

/-- The answer-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The four displayed force magnitudes, in newtons. -/
def displayedForceInNewtons : AnswerChoice → ℝ
  | .A => 39_000
  | .B => 79_000
  | .C => 46_000
  | .D => 35_000

/-- A choice is strictly closer than every other displayed force value. -/
def IsUniqueClosestDisplayedAnswer
    (forceNewtons : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |forceNewtons - displayedForceInNewtons choice| <
      |forceNewtons - displayedForceInNewtons other|

/-!
The exact model value is `2_920_300 / 37 N`, approximately `7.89 × 10⁴ N`.
Consequently the unique closest displayed value is `79_000 N`, answer B.

Blueprint: `thm:physics:phyx_mini_0808:target`.
-/
theorem averageForceHammerheadExertsOnBeam
    (setup : PileDriverSetup)
    (scenario : MatchesPileDriverScenario setup)
    (data : MatchesPileDriverProblemReadouts setup)
    (gravity : UsesStandardTerrestrialGravity setup)
    (figure : MatchesPrimaryPileDriverFigure setup)
    (physical : HasPhysicalPileDriverParameters setup)
    (laws : SatisfiesPileDriverWorkEnergyLaws setup) :
    forceInNewtons setup.averageForceHammerOnBeam =
        (2_920_300 : ℝ) / 37 ∧
      IsUniqueClosestDisplayedAnswer
        (forceInNewtons setup.averageForceHammerOnBeam) .B := by
  have kineticEnergyAtPointOne :
      energyInJoules (setup.kineticEnergy .pointOne) = 0 :=
    laws.atRestHasZeroKineticEnergy .pointOne
      scenario.releasedFromRestAtPointOne
  have kineticEnergyAtPointThree :
      energyInJoules (setup.kineticEnergy .pointThree) = 0 :=
    laws.atRestHasZeroKineticEnergy .pointThree
      scenario.stoppedAfterDrivingAtPointThree
  have dropHeightMeters :
      lengthInMeters setup.dropHeight = 3 := by
    calc
      lengthInMeters setup.dropHeight =
          lengthInMeters setup.figure.dropHeightMarker :=
        congrArg lengthInMeters figure.dropMarkerMatchesSetup.symm
      _ = 3 := figure.printedDropHeightMeters
  have penetrationDepthMeters :
      lengthInMeters setup.beamPenetrationDepth = 37 / 500 := by
    have printedDepth := figure.printedPenetrationDepthCentimeters
    rw [lengthInCentimeters, figure.penetrationMarkerMatchesSetup] at printedDepth
    linarith
  have dropBalance := laws.workEnergyTheorem .dropToBeam
  have drivingBalance := laws.workEnergyTheorem .drivingBeam
  simp only [MotionLeg.endPoint, MotionLeg.startPoint] at dropBalance drivingBalance
  rw [kineticEnergyAtPointOne, laws.gravitationalWork,
    laws.guideRailFrictionWork, laws.beamDoesNoWorkBeforeImpact] at dropBalance
  rw [kineticEnergyAtPointThree, laws.gravitationalWork,
    laws.guideRailFrictionWork, laws.averageBeamContactWorkWhileDriving] at drivingBalance
  simp only [PileDriverSetup.travelDistance] at dropBalance drivingBalance
  have beamForce :
      forceInNewtons setup.averageForceBeamOnHammer =
        (2_920_300 : ℝ) / 37 := by
    rw [data.hammerheadMassKilograms, data.guideRailFrictionNewtons,
      gravity.gravitationalAccelerationSI, dropHeightMeters] at dropBalance
    rw [data.hammerheadMassKilograms, data.guideRailFrictionNewtons,
      gravity.gravitationalAccelerationSI, penetrationDepthMeters] at drivingBalance
    norm_num at dropBalance drivingBalance ⊢
    linarith
  have hammerForce :
      forceInNewtons setup.averageForceHammerOnBeam =
        (2_920_300 : ℝ) / 37 := by
    rw [laws.newtonThirdLawContactMagnitude]
    exact beamForce
  refine ⟨hammerForce, ?_⟩
  rw [hammerForce]
  intro other other_ne
  cases other <;>
    simp_all [displayedForceInNewtons] <;>
    norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0808
