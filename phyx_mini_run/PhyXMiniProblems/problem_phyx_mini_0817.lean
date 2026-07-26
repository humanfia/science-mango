import Mathlib.Analysis.Convex.Combination
import Physlib.Units.WithDim.Basic

/-!
# Pulling on a light rope on a frozen pond

James and Ramon begin on opposite sides of the mug labelled `P` in the
primary figure.  Their masses, positions, the initial separation, and the
distance James has moved retain their physical dimensions through Physlib.
Real numbers occur only as readouts in kilograms or metres.

Assumption/target boundary:

* `MatchesProblemAndPrimaryFigure` records the textual and bitmap data;
* `WhenJamesHasMovedSixMetersTowardMug` records the observation named in the
  question;
* `SatisfiesIsolatedHorizontalCenterOfMassLaw` states the governing
  center-of-mass conservation law for the idealized horizontal system; and
* `ramon_distanceMoved_eq_nine_meters_and_choiceB` derives Ramon's distance
  and the corresponding displayed answer choice.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0817

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical mass, independent of the chosen unit system. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A signed physical coordinate on the horizontal axis in the figure. -/
abbrev AxialPosition : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a signed horizontal position. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  (position UnitChoices.SI).val

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-! ## People, figure labels, and the mechanical setup -/

/-- The two people named in the problem and primary figure. -/
inductive Person where
  | james
  | ramon
  deriving DecidableEq, Repr

/-- The two instants compared in the question. -/
inductive ObservationTime where
  | initial
  | whenJamesMovedSixMeters
  deriving DecidableEq, Repr

/-- Labels printed on the horizontal axis of the primary figure. -/
inductive AxisMarker where
  /-- The point at the mug, printed as `P`. -/
  | P
  /-- The location printed as `x_cm`; the image gives no numerical readout. -/
  | xCM
  deriving DecidableEq, Repr

/-- The light-rope idealization used in the mechanics model. -/
inductive RopeMassModel where
  | negligibleComparedWithPeople
  deriving DecidableEq, Repr

/-- The rope configuration described and drawn in the problem. -/
inductive RopeConfiguration where
  | stretchedBetweenJamesAndRamon
  deriving DecidableEq, Repr

/-- The interaction described by “they pull on the ends of a light rope.” -/
inductive RopeInteraction where
  | eachPersonPullsOneEnd
  deriving DecidableEq, Repr

/-- The horizontal idealization of motion on the frozen pond. -/
inductive PondSurfaceModel where
  | negligibleHorizontalFriction
  deriving DecidableEq, Repr

/-- The initial motion state implicit before James and Ramon begin pulling. -/
inductive InitialMotionModel where
  | atRestRelativeToPond
  deriving DecidableEq, Repr

/--
All independent physical quantities and qualitative labels in the pictured
two-person system.  In particular, Ramon's later position is an independent
field and is not assigned its requested value here.
-/
structure FrozenPondRopeSetup where
  personMass : Person → MassQuantity
  position : ObservationTime → Person → AxialPosition
  mugPosition : AxialPosition
  axisMarkerPosition : AxisMarker → AxialPosition
  initialSeparation : LengthQuantity
  ropeMassModel : RopeMassModel
  ropeConfiguration : RopeConfiguration
  ropeInteraction : RopeInteraction
  pondSurfaceModel : PondSurfaceModel
  initialMotionModel : InitialMotionModel

/-! ## Center of mass and traveled distance -/

/--
The center-of-mass coordinate of James and Ramon at one observation time,
using their kilogram and metre readouts.  This is Mathlib's finite weighted
center of mass specialized to the two named people.
-/
def twoPersonCenterOfMassInMeters
    (setup : FrozenPondRopeSetup) (time : ObservationTime) : ℝ :=
  ({.james, .ramon} : Finset Person).centerMass
    (fun person => massInKilograms (setup.personMass person))
    (fun person => positionInMeters (setup.position time person))

/-- The ordinary nonnegative distance a named person travels, in metres. -/
def distanceMovedInMeters
    (setup : FrozenPondRopeSetup) (person : Person) : ℝ :=
  |positionInMeters (setup.position .whenJamesMovedSixMeters person) -
    positionInMeters (setup.position .initial person)|

/-! ## Given data and governing physics -/

/--
Numerical and qualitative readouts supplied by the prose and primary image.
The midpoint equation records that the mug is midway between the initial
positions.  The `x_cm` marker is identified with the initial center of mass
without assigning it an extra numerical value.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : FrozenPondRopeSetup) : Prop where
  jamesMassKilograms :
    massInKilograms (setup.personMass .james) = 90
  ramonMassKilograms :
    massInKilograms (setup.personMass .ramon) = 60
  jamesInitialPositionMeters :
    positionInMeters (setup.position .initial .james) = -10
  ramonInitialPositionMeters :
    positionInMeters (setup.position .initial .ramon) = 10
  initialSeparationMeters :
    lengthInMeters setup.initialSeparation = 20
  separationMatchesInitialCoordinates :
    lengthInMeters setup.initialSeparation =
      positionInMeters (setup.position .initial .ramon) -
        positionInMeters (setup.position .initial .james)
  mugIsAtPointP : setup.mugPosition = setup.axisMarkerPosition .P
  pointPPositionMeters :
    positionInMeters (setup.axisMarkerPosition .P) = 0
  mugIsInitiallyMidway :
    2 * positionInMeters setup.mugPosition =
      positionInMeters (setup.position .initial .james) +
        positionInMeters (setup.position .initial .ramon)
  xCMMarkerIdentifiesInitialCenterOfMass :
    positionInMeters (setup.axisMarkerPosition .xCM) =
      twoPersonCenterOfMassInMeters setup .initial
  ropeIsLight :
    setup.ropeMassModel = .negligibleComparedWithPeople
  ropeIsStretchedBetweenThem :
    setup.ropeConfiguration = .stretchedBetweenJamesAndRamon
  bothPullOnRopeEnds :
    setup.ropeInteraction = .eachPersonPullsOneEnd
  frozenPondHasNegligibleHorizontalFriction :
    setup.pondSurfaceModel = .negligibleHorizontalFriction

/--
The observation specified in the question: James has moved six metres in the
positive-axis direction from his pictured location toward `P`, without
passing the mug.  This contains no condition on Ramon's later position.
-/
structure WhenJamesHasMovedSixMetersTowardMug
    (setup : FrozenPondRopeSetup) : Prop where
  jamesSignedDisplacementMeters :
    positionInMeters
          (setup.position .whenJamesMovedSixMeters .james) -
        positionInMeters (setup.position .initial .james) = 6
  jamesHasNotPassedMug :
    positionInMeters
        (setup.position .whenJamesMovedSixMeters .james) ≤
      positionInMeters setup.mugPosition

/--
For the light-rope system on the frictionless horizontal pond, all horizontal
pulls are internal.  Starting from rest gives zero initial total horizontal
momentum, so the two-person center of mass is unchanged between the two
observation times.
-/
structure SatisfiesIsolatedHorizontalCenterOfMassLaw
    (setup : FrozenPondRopeSetup) : Prop where
  initiallyAtRest :
    setup.initialMotionModel = .atRestRelativeToPond
  centerOfMassConserved :
    twoPersonCenterOfMassInMeters setup .initial =
      twoPersonCenterOfMassInMeters setup .whenJamesMovedSixMeters

/-! ## Derived relations and displayed answers -/

/--
Center-of-mass conservation gives the mass-weighted balance of the two signed
axial displacements.  This intermediate relation is derived rather than
included in the governing-law premise.
-/
theorem massWeightedDisplacements_balance
    (setup : FrozenPondRopeSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_law : SatisfiesIsolatedHorizontalCenterOfMassLaw setup) :
    massInKilograms (setup.personMass .james) *
          (positionInMeters
                (setup.position .whenJamesMovedSixMeters .james) -
            positionInMeters (setup.position .initial .james)) +
        massInKilograms (setup.personMass .ramon) *
          (positionInMeters
                (setup.position .whenJamesMovedSixMeters .ramon) -
            positionInMeters (setup.position .initial .ramon)) = 0 := by
  have hcom := _law.centerOfMassConserved
  simp only [twoPersonCenterOfMassInMeters, Finset.centerMass,
    Finset.sum_pair (by decide : Person.james ≠ Person.ramon)] at hcom
  rw [_figure.jamesMassKilograms, _figure.ramonMassKilograms] at hcom ⊢
  norm_num at hcom ⊢
  linarith

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance in metres printed beside each displayed answer label. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 6
  | .B => 9
  | .C => 4
  | .D => 3

/--
Ramon moves `9 m`, so the matching displayed answer is choice B.

Blueprint: `thm:physics:phyx_mini_0817:target`.
-/
theorem ramon_distanceMoved_eq_nine_meters_and_choiceB
    (setup : FrozenPondRopeSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_jamesObservation : WhenJamesHasMovedSixMetersTowardMug setup)
    (_law : SatisfiesIsolatedHorizontalCenterOfMassLaw setup) :
    distanceMovedInMeters setup .ramon = 9 ∧
      distanceMovedInMeters setup .ramon =
        AnswerChoice.distanceInMeters .B := by
  have hbalance := massWeightedDisplacements_balance setup _figure _law
  rw [_figure.jamesMassKilograms, _figure.ramonMassKilograms,
    _jamesObservation.jamesSignedDisplacementMeters] at hbalance
  have hramonDisplacement :
      positionInMeters
            (setup.position .whenJamesMovedSixMeters .ramon) -
          positionInMeters (setup.position .initial .ramon) = -9 := by
    linarith
  norm_num [distanceMovedInMeters, hramonDisplacement,
    AnswerChoice.distanceInMeters]

end PhyXMiniProblems.ProblemPhyXMini0817
