import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0558

open Dimension

/-!
# Oppositely directed cosmic-ray protons

Two cosmic-ray protons approach Earth along the same horizontal line from
opposite sides.  In Earth's inertial frame their signed velocity components
are `0.6 c` and `-0.8 c`.  The question asks for the velocity of each proton
in the other proton's rest frame, so the relevant law is the collinear
Einstein velocity transformation rather than subtraction of the two
Earth-frame components.

Signed velocity components below are genuine, unit-independent Physlib
quantities.  Real numbers occur only as named-unit readouts, dimensionless
fractions of the vacuum speed of light, qualitative drawing coordinates, and
the coefficients printed in the multiple-choice table.
-/

/-! ## Dimensionful signed velocities and scalar readouts -/

/-- A signed one-dimensional physical velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a signed velocity component in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Meter-per-second readout of a signed physical velocity component. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Physlib's exact dimensionful vacuum speed of light, read in SI units. -/
def vacuumLightSpeedInMetersPerSecond : ℝ :=
  signedVelocityInMetersPerSecond DimSpeed.speedOfLight

/-- A signed axial velocity expressed as a dimensionless fraction of `c`. -/
def velocityFractionOfLight (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityInMetersPerSecond velocity /
    vacuumLightSpeedInMetersPerSecond

/-! ## Physical, frame, and figure labels -/

/-- The three physical objects distinguished in the supplied bitmap. -/
inductive FigureObject where
  | proton1
  | earth
  | proton2
  deriving DecidableEq, Fintype, Repr

/-- The physical kind of an object in the scenario. -/
inductive PhysicalObjectKind where
  | cosmicRayProton
  | earth
  deriving DecidableEq, Repr

/-- The two proton labels used by the prose and figure. -/
inductive ProtonLabel where
  | proton1
  | proton2
  deriving DecidableEq, Fintype, Repr

/-- Inertial frames needed to interpret all four velocity measurements. -/
inductive InertialFrameLabel where
  | earthFrame
  | proton1RestFrame
  | proton2RestFrame
  deriving DecidableEq, Fintype, Repr

/-- Horizontal direction relative to the left-to-right orientation of the image. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-!
Typed qualitative evidence from the primary image.  The horizontal
coordinates preserve only visual ordering and have no interpretation as
physical distances or simultaneous spacetime positions.
-/
structure OpposingProtonsFigure where
  objectHorizontalCoordinate : FigureObject → ℝ
  objectText : FigureObject → String
  objectDrawnAsCircle : FigureObject → Bool
  velocityArrowDirection : ProtonLabel → HorizontalDirection
  velocityArrowText : ProtonLabel → String
  showsDashedLineAcrossEarth : Bool
  hasQuantitativePositionScale : Bool

/-!
The physical quantities of the problem.  In particular, the two requested
relative velocities are independent dimensionful fields; they are not
defined from an answer choice or from a solved numerical formula.
-/
structure OpposingCosmicRayProtonsSetup where
  earthMeasurementFrame : InertialFrameLabel
  proton1ObserverFrame : InertialFrameLabel
  proton2ObserverFrame : InertialFrameLabel
  objectKind : FigureObject → PhysicalObjectKind
  proton1MotionInEarthFrame : HorizontalDirection
  proton2MotionInEarthFrame : HorizontalDirection
  proton1VelocityRelativeToEarth : SignedVelocityQuantity
  proton2VelocityRelativeToEarth : SignedVelocityQuantity
  proton1VelocityRelativeToProton2 : SignedVelocityQuantity
  proton2VelocityRelativeToProton1 : SignedVelocityQuantity
  figure : OpposingProtonsFigure

/-! ## Figure evidence and numerical problem data -/

/-!
Facts read from the primary bitmap: proton 1 is left of Earth and its `v₁`
arrow points right, while proton 2 is right of Earth and its `v₂` arrow
points left.  The dashed mark across Earth and the visible text are retained,
but the drawing contributes no quantitative position scale.
-/
structure MatchesPrimaryFigure
    (setup : OpposingCosmicRayProtonsSetup) : Prop where
  proton1LeftOfEarth :
    setup.figure.objectHorizontalCoordinate .proton1 <
      setup.figure.objectHorizontalCoordinate .earth
  earthLeftOfProton2 :
    setup.figure.objectHorizontalCoordinate .earth <
      setup.figure.objectHorizontalCoordinate .proton2
  proton1Text : setup.figure.objectText .proton1 = "1"
  earthText : setup.figure.objectText .earth = "Earth"
  proton2Text : setup.figure.objectText .proton2 = "2"
  proton1DrawnAsCircle : setup.figure.objectDrawnAsCircle .proton1 = true
  earthDrawnAsCircle : setup.figure.objectDrawnAsCircle .earth = true
  proton2DrawnAsCircle : setup.figure.objectDrawnAsCircle .proton2 = true
  proton1ArrowPointsRight :
    setup.figure.velocityArrowDirection .proton1 = .rightward
  proton2ArrowPointsLeft :
    setup.figure.velocityArrowDirection .proton2 = .leftward
  proton1ArrowText : setup.figure.velocityArrowText .proton1 = "v₁"
  proton2ArrowText : setup.figure.velocityArrowText .proton2 = "v₂"
  dashedEarthLineShown : setup.figure.showsDashedLineAcrossEarth = true
  noQuantitativePositionScale :
    setup.figure.hasQuantitativePositionScale = false

/-!
Frame assignments, object kinds, directions, and the two Earth-frame
velocity readouts stated in the problem.  Neither requested relative velocity
is assigned a value here.
-/
structure MatchesProblemData
    (setup : OpposingCosmicRayProtonsSetup) : Prop where
  measurementsUseEarthFrame :
    setup.earthMeasurementFrame = .earthFrame
  proton1VelocityObservedFromProton2Frame :
    setup.proton1ObserverFrame = .proton2RestFrame
  proton2VelocityObservedFromProton1Frame :
    setup.proton2ObserverFrame = .proton1RestFrame
  firstObjectIsCosmicRayProton :
    setup.objectKind .proton1 = .cosmicRayProton
  centerObjectIsEarth : setup.objectKind .earth = .earth
  secondObjectIsCosmicRayProton :
    setup.objectKind .proton2 = .cosmicRayProton
  proton1ApproachesEarthFromLeft :
    setup.proton1MotionInEarthFrame = .rightward
  proton2ApproachesEarthFromRight :
    setup.proton2MotionInEarthFrame = .leftward
  proton1EarthVelocityFraction :
    velocityFractionOfLight setup.proton1VelocityRelativeToEarth = 3 / 5
  proton2EarthVelocityFraction :
    velocityFractionOfLight setup.proton2VelocityRelativeToEarth = -(4 / 5)

/-!
Physical domain conditions on the supplied Earth-frame inputs.  They select
the ordinary subluminal branch but do not determine either requested relative
velocity.
-/
structure HasPhysicalInputParameters
    (setup : OpposingCosmicRayProtonsSetup) : Prop where
  lightSpeedPositive : 0 < vacuumLightSpeedInMetersPerSecond
  proton1EarthVelocitySubluminal :
    |velocityFractionOfLight setup.proton1VelocityRelativeToEarth| < 1
  proton2EarthVelocitySubluminal :
    |velocityFractionOfLight setup.proton2VelocityRelativeToEarth| < 1

/-! ## Governing special-relativistic law -/

/-!
The one-dimensional Einstein velocity transformation is applied in both
directions.  If `βa` and `βb` are signed Earth-frame velocity fractions, then
the velocity of `a` in `b`'s rest frame is

`(βa - βb) / (1 - βa * βb)`.

These are unsolved governing relations among physical quantities.  They
contain no exact result, rounded answer value, or answer-choice label.
-/
structure SatisfiesReciprocalEinsteinVelocityTransformations
    (setup : OpposingCosmicRayProtonsSetup) : Prop where
  proton1VelocityInProton2Frame :
    velocityFractionOfLight setup.proton1VelocityRelativeToProton2 =
      (velocityFractionOfLight setup.proton1VelocityRelativeToEarth -
          velocityFractionOfLight setup.proton2VelocityRelativeToEarth) /
        (1 -
          velocityFractionOfLight setup.proton1VelocityRelativeToEarth *
            velocityFractionOfLight setup.proton2VelocityRelativeToEarth)
  proton2VelocityInProton1Frame :
    velocityFractionOfLight setup.proton2VelocityRelativeToProton1 =
      (velocityFractionOfLight setup.proton2VelocityRelativeToEarth -
          velocityFractionOfLight setup.proton1VelocityRelativeToEarth) /
        (1 -
          velocityFractionOfLight setup.proton2VelocityRelativeToEarth *
            velocityFractionOfLight setup.proton1VelocityRelativeToEarth)

/-! ## Displayed choices and current target -/

/-- The signed requested velocity fraction for the named moving proton. -/
def relativeVelocityFraction
    (setup : OpposingCosmicRayProtonsSetup) : ProtonLabel → ℝ
  | .proton1 =>
      velocityFractionOfLight setup.proton1VelocityRelativeToProton2
  | .proton2 =>
      velocityFractionOfLight setup.proton2VelocityRelativeToProton1

/-- Labels of the four relative-speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The positive coefficient of `c` printed beside each answer label. -/
def displayedRelativeSpeedFraction : AnswerChoice → ℝ
  | .A => 91 / 100
  | .B => 82 / 100
  | .C => 68 / 100
  | .D => 95 / 100

/-- The answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a positive speed coefficient printed to two decimal places. -/
def RoundsToNearestHundredth
    (actualFraction displayedFraction : ℝ) : Prop :=
  |actualFraction - displayedFraction| < 1 / 200

/-!
A displayed choice matches only when it is the two-decimal rounding of the
speed magnitude of each proton relative to the other.
-/
def MatchesAnswerChoice
    (setup : OpposingCosmicRayProtonsSetup) (choice : AnswerChoice) : Prop :=
  ∀ proton : ProtonLabel,
    RoundsToNearestHundredth
      |relativeVelocityFraction setup proton|
      (displayedRelativeSpeedFraction choice)

/-- The choice is the unique displayed match for both relative speeds. -/
def IsUniqueMatchingAnswerChoice
    (setup : OpposingCosmicRayProtonsSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Substitution of `β₁ = 3/5` and `β₂ = -4/5` into the two Einstein
transformations yields equal-and-opposite signed relative velocities:
`β₁|₂ = 35/37` and `β₂|₁ = -35/37`.
-/
lemma velocity_of_each_proton_relative_to_other_exact
    (setup : OpposingCosmicRayProtonsSetup)
    (hData : MatchesProblemData setup)
    (hRelativity : SatisfiesReciprocalEinsteinVelocityTransformations setup) :
    relativeVelocityFraction setup .proton1 = 35 / 37 ∧
      relativeVelocityFraction setup .proton2 = -(35 / 37) := by
  constructor
  · change
      velocityFractionOfLight setup.proton1VelocityRelativeToProton2 =
        35 / 37
    rw [hRelativity.proton1VelocityInProton2Frame,
      hData.proton1EarthVelocityFraction,
      hData.proton2EarthVelocityFraction]
    norm_num
  · change
      velocityFractionOfLight setup.proton2VelocityRelativeToProton1 =
        -(35 / 37)
    rw [hRelativity.proton2VelocityInProton1Frame,
      hData.proton1EarthVelocityFraction,
      hData.proton2EarthVelocityFraction]
    norm_num

/-!
Each proton therefore sees the other approach with speed magnitude
`35/37 c ≈ 0.945946 c`, which rounds to `0.95 c` and uniquely selects D.

This formalizes `thm:physics:phyx_mini_0558:target`.
-/
theorem problem_phyx_mini_0558
    (setup : OpposingCosmicRayProtonsSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hRelativity : SatisfiesReciprocalEinsteinVelocityTransformations setup) :
    relativeVelocityFraction setup .proton1 = 35 / 37 ∧
      relativeVelocityFraction setup .proton2 = -(35 / 37) ∧
      IsUniqueMatchingAnswerChoice setup .D := by
  obtain ⟨hProton1, hProton2⟩ :=
    velocity_of_each_proton_relative_to_other_exact setup hData hRelativity
  refine ⟨hProton1, hProton2, ?_⟩
  constructor
  · intro proton
    fin_cases proton
    · rw [hProton1]
      norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction]
    · rw [hProton2]
      norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction]
  · intro other hOther
    fin_cases other
    · have h := hOther .proton1
      rw [hProton1] at h
      norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction] at h
    · have h := hOther .proton1
      rw [hProton1] at h
      norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction] at h
    · have h := hOther .proton1
      rw [hProton1] at h
      norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction] at h
    · rfl

end PhyXMiniProblems.ProblemPhyXMini0558
