import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0624

open Dimension

/-!
# Relative speed of the Enterprise and an alien vessel

In Earth's inertial frame an alien vessel and the Enterprise both move
leftward, directly toward Earth, at `0.60 c` and `0.90 c`, respectively. The
Enterprise is drawn behind the alien vessel and overtakes it. The requested
quantity is the speed of either vessel measured in the other vessel's rest
frame, so ordinary subtraction of the two Earth-frame speeds is replaced by
the one-dimensional Einstein velocity transformation.

Signed velocity components below are genuine, unit-independent Physlib
dimensionful quantities. Real numbers occur only as named-unit readouts,
dimensionless fractions of the vacuum speed of light, qualitative image
coordinates, and the coefficients printed in the answer choices. In
particular, neither requested inter-vessel velocity is defined from the
recorded answer or from the solved fraction `15/23`.
-/

/-! ## Dimensionful signed velocities and scalar readouts -/

/-!
A signed one-dimensional physical velocity component. The real carrier is
needed because Physlib's `DimSpeed` represents a nonnegative speed magnitude.
-/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a signed velocity component in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metres-per-second readout of a signed physical velocity component. -/
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

/-! ## Physical, frame, and primary-figure labels -/

/-- The three physical objects visible in image `624.png`. -/
inductive FigureObject where
  | earth
  | aliens
  | enterprise
  deriving DecidableEq, Fintype, Repr

/-- The two spacecraft whose relative speed is requested. -/
inductive VesselLabel where
  | aliens
  | enterprise
  deriving DecidableEq, Fintype, Repr

/-- The inertial frames needed to interpret all four velocity measurements. -/
inductive InertialFrameLabel where
  | earthFrame
  | alienVesselRestFrame
  | enterpriseRestFrame
  deriving DecidableEq, Fintype, Repr

/-- Horizontal direction relative to the orientation of the supplied image. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Fintype, Repr

/-!
Typed qualitative evidence present in the primary bitmap. Horizontal
coordinates encode only the visual left-to-right ordering; they are not
physical distances or simultaneous spacetime positions.
-/
structure EnterpriseRescueFigure where
  objectHorizontalCoordinate : FigureObject → ℝ
  objectShown : FigureObject → Bool
  vesselText : VesselLabel → String
  velocityArrowDirection : VesselLabel → HorizontalDirection
  velocityArrowText : VesselLabel → String
  velocityArrowIsGreen : VesselLabel → Bool
  hasQuantitativePositionScale : Bool

/-!
The four physical velocity components and their observer frames. The two
requested relative velocities are independent dimensionful fields, rather
than definitions containing an answer value.
-/
structure EnterpriseAlienRelativeSpeedSetup where
  earthMeasurementFrame : InertialFrameLabel
  alienObserverFrame : InertialFrameLabel
  enterpriseObserverFrame : InertialFrameLabel
  positiveAxisDirection : HorizontalDirection
  alienMotionInEarthFrame : HorizontalDirection
  enterpriseMotionInEarthFrame : HorizontalDirection
  alienVelocityRelativeToEarth : SignedVelocityQuantity
  enterpriseVelocityRelativeToEarth : SignedVelocityQuantity
  alienVelocityRelativeToEnterprise : SignedVelocityQuantity
  enterpriseVelocityRelativeToAliens : SignedVelocityQuantity
  figure : EnterpriseRescueFigure

/-! ## Scenario, figure evidence, and stated numerical data -/

/-!
Facts read from image `624.png`: Earth is leftmost, the alien vessel lies
between Earth and the Enterprise, both green velocity arrows point left, and
the displayed velocity annotations are `0.60c` and `0.90c`.
-/
structure MatchesPrimaryFigure
    (setup : EnterpriseAlienRelativeSpeedSetup) : Prop where
  earthIsShown : setup.figure.objectShown .earth = true
  alienVesselIsShown : setup.figure.objectShown .aliens = true
  enterpriseIsShown : setup.figure.objectShown .enterprise = true
  earthIsLeftOfAlienVessel :
    setup.figure.objectHorizontalCoordinate .earth <
      setup.figure.objectHorizontalCoordinate .aliens
  alienVesselIsLeftOfEnterprise :
    setup.figure.objectHorizontalCoordinate .aliens <
      setup.figure.objectHorizontalCoordinate .enterprise
  alienVesselText : setup.figure.vesselText .aliens = ""
  enterpriseText : setup.figure.vesselText .enterprise = "Enterprise"
  alienArrowPointsLeft :
    setup.figure.velocityArrowDirection .aliens = .leftward
  enterpriseArrowPointsLeft :
    setup.figure.velocityArrowDirection .enterprise = .leftward
  alienVelocityText :
    setup.figure.velocityArrowText .aliens = "v = 0.60c"
  enterpriseVelocityText :
    setup.figure.velocityArrowText .enterprise = "v = 0.90c"
  alienArrowIsGreen : setup.figure.velocityArrowIsGreen .aliens = true
  enterpriseArrowIsGreen :
    setup.figure.velocityArrowIsGreen .enterprise = true
  noQuantitativePositionScale :
    setup.figure.hasQuantitativePositionScale = false

/-!
Frame assignments, sign convention, directions, and the two numerical
Earth-frame velocity readouts stated in the question. The positive axis is
chosen leftward, toward Earth, so both signed fractions are positive. No
inter-vessel velocity is supplied here.
-/
structure MatchesProblemData
    (setup : EnterpriseAlienRelativeSpeedSetup) : Prop where
  earthVelocitiesMeasuredInEarthFrame :
    setup.earthMeasurementFrame = .earthFrame
  alienVelocityObservedFromEnterpriseFrame :
    setup.alienObserverFrame = .enterpriseRestFrame
  enterpriseVelocityObservedFromAlienFrame :
    setup.enterpriseObserverFrame = .alienVesselRestFrame
  positiveAxisPointsTowardEarth :
    setup.positiveAxisDirection = .leftward
  alienMovesTowardEarth :
    setup.alienMotionInEarthFrame = .leftward
  enterpriseMovesTowardEarth :
    setup.enterpriseMotionInEarthFrame = .leftward
  alienEarthVelocityFraction :
    velocityFractionOfLight setup.alienVelocityRelativeToEarth = 3 / 5
  enterpriseEarthVelocityFraction :
    velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth = 9 / 10

/-!
Physical-domain conditions on the supplied Earth-frame inputs. They select
the same-direction, subluminal overtaking branch without assigning either
unknown inter-vessel velocity a numerical value.
-/
structure HasPhysicalInputParameters
    (setup : EnterpriseAlienRelativeSpeedSetup) : Prop where
  lightSpeedPositive : 0 < vacuumLightSpeedInMetersPerSecond
  alienEarthVelocityPositive :
    0 < velocityFractionOfLight setup.alienVelocityRelativeToEarth
  alienEarthVelocitySubluminal :
    velocityFractionOfLight setup.alienVelocityRelativeToEarth < 1
  enterpriseEarthVelocityPositive :
    0 < velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth
  enterpriseEarthVelocitySubluminal :
    velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth < 1
  enterpriseOvertakesAliens :
    velocityFractionOfLight setup.alienVelocityRelativeToEarth <
      velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth

/-! ## Governing special-relativistic law -/

/-!
The one-dimensional Einstein velocity transformation is applied in both
directions. If `βa` and `βb` are signed Earth-frame velocity fractions,
then the velocity of `a` in `b`'s rest frame is

`(βa - βb) / (1 - βa * βb)`.

These are governing relations among independent physical quantities. They
contain neither the derived fraction `15/23`, the rounded value `0.65`, nor
an answer-choice label.
-/
structure SatisfiesReciprocalEinsteinVelocityTransformations
    (setup : EnterpriseAlienRelativeSpeedSetup) : Prop where
  alienVelocityInEnterpriseFrame :
    velocityFractionOfLight setup.alienVelocityRelativeToEnterprise =
      (velocityFractionOfLight setup.alienVelocityRelativeToEarth -
          velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth) /
        (1 -
          velocityFractionOfLight setup.alienVelocityRelativeToEarth *
            velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth)
  enterpriseVelocityInAlienFrame :
    velocityFractionOfLight setup.enterpriseVelocityRelativeToAliens =
      (velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth -
          velocityFractionOfLight setup.alienVelocityRelativeToEarth) /
        (1 -
          velocityFractionOfLight setup.enterpriseVelocityRelativeToEarth *
            velocityFractionOfLight setup.alienVelocityRelativeToEarth)

/-! ## Displayed choices and current target -/

/-- The requested signed velocity fraction for each named moving vessel. -/
def relativeVelocityFraction
    (setup : EnterpriseAlienRelativeSpeedSetup) : VesselLabel → ℝ
  | .aliens =>
      velocityFractionOfLight setup.alienVelocityRelativeToEnterprise
  | .enterprise =>
      velocityFractionOfLight setup.enterpriseVelocityRelativeToAliens

/-- Labels of the four relative-speed choices printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The positive coefficient of `c` printed beside each answer label. -/
def displayedRelativeSpeedFraction : AnswerChoice → ℝ
  | .A => 17 / 20
  | .B => 3 / 4
  | .C => 13 / 20
  | .D => 11 / 20

/-- The answer label recorded by the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a positive speed coefficient printed to two decimal places. -/
def RoundsToNearestHundredth
    (actualFraction displayedFraction : ℝ) : Prop :=
  |actualFraction - displayedFraction| < 1 / 200

/-!
A displayed choice matches when it is the two-decimal rounding of the speed
magnitude of each vessel relative to the other.
-/
def MatchesAnswerChoice
    (setup : EnterpriseAlienRelativeSpeedSetup)
    (choice : AnswerChoice) : Prop :=
  ∀ vessel : VesselLabel,
    RoundsToNearestHundredth
      |relativeVelocityFraction setup vessel|
      (displayedRelativeSpeedFraction choice)

/-- The selected choice is the unique displayed match for both vessels. -/
def IsUniqueMatchingAnswerChoice
    (setup : EnterpriseAlienRelativeSpeedSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Substitution of the two Earth-frame speed fractions into the reciprocal
Einstein transformations gives equal-and-opposite signed velocities: the
aliens move at `-15/23 c` in the Enterprise frame, while the Enterprise moves
at `15/23 c` in the alien-vessel frame.
-/
lemma reciprocal_relative_velocities_exact
    (setup : EnterpriseAlienRelativeSpeedSetup)
    (hData : MatchesProblemData setup)
    (hRelativity : SatisfiesReciprocalEinsteinVelocityTransformations setup) :
    relativeVelocityFraction setup .aliens = -(15 / 23) ∧
      relativeVelocityFraction setup .enterprise = 15 / 23 := by
  constructor <;>
    simp [relativeVelocityFraction,
      hRelativity.alienVelocityInEnterpriseFrame,
      hRelativity.enterpriseVelocityInAlienFrame,
      hData.alienEarthVelocityFraction,
      hData.enterpriseEarthVelocityFraction] <;>
    norm_num

/-!
Both observers therefore measure the same relative speed magnitude
`15/23 c ≈ 0.65217 c`. This rounds to `0.65 c`, uniquely selecting choice C.

This formalizes `thm:physics:phyx_mini_0624:target`.
-/
theorem problem_phyx_mini_0624
    (setup : EnterpriseAlienRelativeSpeedSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hRelativity : SatisfiesReciprocalEinsteinVelocityTransformations setup) :
    |relativeVelocityFraction setup .aliens| = 15 / 23 ∧
      |relativeVelocityFraction setup .enterprise| = 15 / 23 ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  rcases reciprocal_relative_velocities_exact setup hData hRelativity with
    ⟨hAlien, hEnterprise⟩
  have hSpeedAlien :
      |relativeVelocityFraction setup .aliens| = 15 / 23 := by
    rw [hAlien, abs_neg, abs_of_pos]
    norm_num
  have hSpeedEnterprise :
      |relativeVelocityFraction setup .enterprise| = 15 / 23 := by
    rw [hEnterprise, abs_of_pos]
    norm_num
  refine ⟨hSpeedAlien, hSpeedEnterprise, ?_⟩
  constructor
  · intro vessel
    cases vessel
    · rw [hSpeedAlien]
      norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction,
        recordedDatasetAnswer]
    · rw [hSpeedEnterprise]
      norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction,
        recordedDatasetAnswer]
  · intro other hOther
    have hMatch := hOther .enterprise
    rw [hSpeedEnterprise] at hMatch
    cases other with
    | A =>
        norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction] at hMatch
    | B =>
        norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction] at hMatch
    | C => rfl
    | D =>
        norm_num [RoundsToNearestHundredth, displayedRelativeSpeedFraction] at hMatch

end PhyXMiniProblems.ProblemPhyXMini0624
