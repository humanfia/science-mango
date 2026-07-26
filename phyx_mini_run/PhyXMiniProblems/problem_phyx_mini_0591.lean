import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0591

open Dimension

/-!
# Cosmic rays approaching opposite geographic poles

The primary image shows one cosmic-ray particle above the geographic north
pole moving southward at `0.80c`, and a second below the geographic south pole
moving northward at `0.60c`.  Thus their Earth-frame velocities have opposite
signs along the common north--south axis.  The requested quantity is the
nonnegative speed of either particle relative to the other.

Signed velocities and nonnegative speeds below are unit-independent Physlib
quantities carrying length-per-time dimension.  Real numbers occur only as
unit readouts, dimensionless ratios to vacuum `c`, qualitative drawing
coordinates, and displayed multiple-choice values.
-/

/-! ## Dimensionful velocities, speeds, and normalized readouts -/

/-- A signed one-dimensional physical velocity along Earth's rotation axis. -/
abbrev SignedAxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative physical speed, independent of a choice of units. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a signed axial velocity in selected units of length and time. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedAxialVelocity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a nonnegative speed in selected units of length and time. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read Physlib's exact dimensionful vacuum speed of light in named units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  signedVelocityReadout lengthUnit timeUnit DimSpeed.speedOfLight

/-- A signed axial velocity as the dimensionless ratio `beta = v / c`. -/
def velocityInLightSpeedUnits (velocity : SignedAxialVelocity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-- A nonnegative speed as a dimensionless multiple of vacuum `c`. -/
def speedInLightSpeedUnits (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-! ## Frames and primary-image labels -/

/-- The inertial frames used for the Earth-frame data and requested speed. -/
inductive ReferenceFrameLabel where
  | earthRest
  | southEntryParticleRest
  deriving DecidableEq, Repr

/-- The two geographic pole labels printed beside the Earth. -/
inductive GeographicPole where
  | north
  | south
  deriving DecidableEq, Repr

/-- The two particles distinguished by the pole through which each approaches. -/
inductive CosmicRayParticle where
  | northEntry
  | southEntry
  deriving DecidableEq, Repr

/-- Signed directions along the geographic north--south axis. -/
inductive AxialDirection where
  | northward
  | southward
  deriving DecidableEq, Repr

/-!
Typed evidence carried by the primary image.  The vertical coordinates encode
only the top-to-bottom order in the drawing and are not physical distances.
-/
structure CosmicRayAxisFigure where
  showsEarth : Bool
  showsNorthSouthAxis : Bool
  showsRotationArrowAboutAxis : Bool
  poleVerticalCoordinate : GeographicPole → ℝ
  poleText : GeographicPole → String
  entryPole : CosmicRayParticle → GeographicPole
  velocityArrowDirection : CosmicRayParticle → AxialDirection
  velocityArrowMagnitudeInLightSpeedUnits : CosmicRayParticle → ℝ

/-!
All physical quantities in the scenario.  The transformed north-entry
particle velocity and the relative approach speed are independent unknown
observables; neither is defined from the recorded answer.
-/
structure CosmicRayApproachSetup where
  figure : CosmicRayAxisFigure
  earthFrame : ReferenceFrameLabel
  relativeSpeedObserverFrame : ReferenceFrameLabel
  northEntryVelocityInEarthFrame : SignedAxialVelocity
  southEntryVelocityInEarthFrame : SignedAxialVelocity
  northEntryVelocityInSouthEntryFrame : SignedAxialVelocity
  relativeApproachSpeed : SpeedQuantity

/-! ## Figure evidence and stated physical data -/

/-!
The Earth, axial rotation marker, pole labels, inward velocity arrows, and
their `0.80c` and `0.60c` magnitudes as read from the supplied bitmap.
-/
structure MatchesPrimaryFigure (setup : CosmicRayApproachSetup) : Prop where
  earthIsShown : setup.figure.showsEarth = true
  northSouthAxisIsShown : setup.figure.showsNorthSouthAxis = true
  axialRotationMarkerIsShown :
    setup.figure.showsRotationArrowAboutAxis = true
  southPoleBelowNorthPole :
    setup.figure.poleVerticalCoordinate .south <
      setup.figure.poleVerticalCoordinate .north
  northPoleText : setup.figure.poleText .north = "Geographic north pole"
  southPoleText : setup.figure.poleText .south = "Geographic south pole"
  northParticleEntersAtNorthPole :
    setup.figure.entryPole .northEntry = .north
  southParticleEntersAtSouthPole :
    setup.figure.entryPole .southEntry = .south
  northParticleArrowPointsSouth :
    setup.figure.velocityArrowDirection .northEntry = .southward
  southParticleArrowPointsNorth :
    setup.figure.velocityArrowDirection .southEntry = .northward
  northParticleArrowMagnitude :
    setup.figure.velocityArrowMagnitudeInLightSpeedUnits .northEntry = 4 / 5
  southParticleArrowMagnitude :
    setup.figure.velocityArrowMagnitudeInLightSpeedUnits .southEntry = 3 / 5

/-!
Earth-frame velocity readouts.  Positive is chosen northward, so the particle
above the north pole has velocity `-0.80c` and the particle below the south
pole has velocity `+0.60c`.  No relative velocity or relative speed is given.
-/
structure MatchesEarthFrameVelocityReadouts
    (setup : CosmicRayApproachSetup) : Prop where
  earthFrameLabel : setup.earthFrame = .earthRest
  requestedObserverFrameLabel :
    setup.relativeSpeedObserverFrame = .southEntryParticleRest
  northEntryVelocity :
    velocityInLightSpeedUnits setup.northEntryVelocityInEarthFrame =
      (-4 / 5 : ℝ)
  southEntryVelocity :
    velocityInLightSpeedUnits setup.southEntryVelocityInEarthFrame =
      (3 / 5 : ℝ)

/-!
Physical domain conditions for the given velocities and the unknown relative
speed.  These impose signs and subluminality but no solved numerical result.
-/
structure HasPhysicalCosmicRayParameters
    (setup : CosmicRayApproachSetup) : Prop where
  lightSpeedReadoutPositive :
    0 < vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds
  northEntryVelocitySubluminal :
    |velocityInLightSpeedUnits setup.northEntryVelocityInEarthFrame| < 1
  southEntryVelocitySubluminal :
    |velocityInLightSpeedUnits setup.southEntryVelocityInEarthFrame| < 1
  northEntryMovesSouth :
    velocityInLightSpeedUnits setup.northEntryVelocityInEarthFrame < 0
  southEntryMovesNorth :
    0 < velocityInLightSpeedUnits setup.southEntryVelocityInEarthFrame
  relativeApproachSpeedPositive :
    0 < speedInLightSpeedUnits setup.relativeApproachSpeed
  relativeApproachSpeedSubluminal :
    speedInLightSpeedUnits setup.relativeApproachSpeed < 1

/-! ## Governing special-relativistic laws -/

/-!
The one-dimensional Lorentz velocity transformation from Earth's frame `E`
to the south-entry particle's rest frame `S`:

`beta_(N|S) = (beta_(N|E) - beta_(S|E)) /
  (1 - beta_(S|E) * beta_(N|E))`.

The law relates an unknown transformed velocity to the two observations.  It
contains neither the solved fraction `-35/37` nor an answer-choice value.
-/
structure ObeysCollinearLorentzVelocityTransformation
    (setup : CosmicRayApproachSetup) : Prop where
  northVelocityInSouthFrame :
    velocityInLightSpeedUnits setup.northEntryVelocityInSouthEntryFrame =
      (velocityInLightSpeedUnits setup.northEntryVelocityInEarthFrame -
          velocityInLightSpeedUnits setup.southEntryVelocityInEarthFrame) /
        (1 -
          velocityInLightSpeedUnits setup.southEntryVelocityInEarthFrame *
            velocityInLightSpeedUnits setup.northEntryVelocityInEarthFrame)

/-!
Operational meaning of the requested nonnegative approach speed: it is the
magnitude of the north-entry particle's signed velocity in the other
particle's rest frame.
-/
structure RelativeApproachSpeedIsMagnitude
    (setup : CosmicRayApproachSetup) : Prop where
  speedIsMagnitude :
    speedInLightSpeedUnits setup.relativeApproachSpeed =
      |velocityInLightSpeedUnits setup.northEntryVelocityInSouthEntryFrame|

/-! ## Displayed answers and current target -/

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed candidate approach speeds, as dimensionless multiples of `c`. -/
def displayedSpeedInLightSpeedUnits : AnswerChoice → ℝ
  | .A => 35 / 100
  | .B => 60 / 100
  | .C => 95 / 100
  | .D => 65 / 100

/-- The answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Nearest-hundredth agreement, with a half-open convention at exact ties. -/
def RoundsToNearestHundredth (value displayed : ℝ) : Prop :=
  displayed - 1 / 200 ≤ value ∧ value < displayed + 1 / 200

/-- A displayed choice agrees with the modeled relative approach speed. -/
def MatchesAnswerChoice
    (setup : CosmicRayApproachSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredth
    (speedInLightSpeedUnits setup.relativeApproachSpeed)
    (displayedSpeedInLightSpeedUnits choice)

/-- The selected choice is the unique displayed rounded value. -/
def IsUniqueMatchingAnswerChoice
    (setup : CosmicRayApproachSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Substitution of the two Earth-frame readouts into the Lorentz transformation
gives the north-entry particle's exact signed velocity `(-35/37)c` in the
south-entry particle's rest frame.  This is a derived result, not a premise.
-/
lemma northEntryVelocityInSouthEntryFrame_exact
    (setup : CosmicRayApproachSetup)
    (hReadouts : MatchesEarthFrameVelocityReadouts setup)
    (hLorentz : ObeysCollinearLorentzVelocityTransformation setup) :
    velocityInLightSpeedUnits setup.northEntryVelocityInSouthEntryFrame =
      (-35 / 37 : ℝ) := by
  rw [hLorentz.northVelocityInSouthFrame, hReadouts.northEntryVelocity,
    hReadouts.southEntryVelocity]
  norm_num

/-!
The exact relative approach speed is `(35/37)c`, approximately `0.945946c`.
It therefore rounds to the displayed value `0.95c`, uniquely selecting choice
C rather than asserting the rounded decimal as an exact physical equality.

Blueprint label: `thm:physics:phyx_mini_0591:target`.
-/
theorem problem_phyx_mini_0591
    (setup : CosmicRayApproachSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hReadouts : MatchesEarthFrameVelocityReadouts setup)
    (hPhysical : HasPhysicalCosmicRayParameters setup)
    (hLorentz : ObeysCollinearLorentzVelocityTransformation setup)
    (hMagnitude : RelativeApproachSpeedIsMagnitude setup) :
    velocityInLightSpeedUnits setup.northEntryVelocityInSouthEntryFrame =
        (-35 / 37 : ℝ) ∧
      speedInLightSpeedUnits setup.relativeApproachSpeed = (35 / 37 : ℝ) ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hVelocity :=
    northEntryVelocityInSouthEntryFrame_exact setup hReadouts hLorentz
  have hSpeed :
      speedInLightSpeedUnits setup.relativeApproachSpeed = (35 / 37 : ℝ) := by
    rw [hMagnitude.speedIsMagnitude, hVelocity]
    norm_num
  refine ⟨hVelocity, hSpeed, ?_⟩
  refine ⟨?_, ?_⟩
  · simp only [MatchesAnswerChoice, hSpeed]
    norm_num [RoundsToNearestHundredth, displayedSpeedInLightSpeedUnits,
      recordedDatasetAnswer]
  · intro other hOther
    simp only [MatchesAnswerChoice, hSpeed] at hOther
    cases other with
    | A =>
        norm_num [RoundsToNearestHundredth, displayedSpeedInLightSpeedUnits]
          at hOther
    | B =>
        norm_num [RoundsToNearestHundredth, displayedSpeedInLightSpeedUnits]
          at hOther
    | C => rfl
    | D =>
        norm_num [RoundsToNearestHundredth, displayedSpeedInLightSpeedUnits]
          at hOther

end PhyXMiniProblems.ProblemPhyXMini0591
