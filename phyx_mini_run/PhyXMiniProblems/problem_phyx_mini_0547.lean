import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0547

open Dimension

/-!
# Oppositely moving relativistic spacecraft

The supplied figure shows spacecraft `A` moving left and spacecraft `B`
moving right along a common horizontal axis.  Ground observers measure both
speed magnitudes as `0.85 c`.  The requested quantity is the speed of `A`
relative to `B`, so the two ground-frame velocities must be combined with the
one-dimensional Lorentz velocity transformation rather than subtracted
Galilei-wise.

Signed velocities and nonnegative speeds below are unit-independent Physlib
quantities carrying length-per-time dimension.  Real numbers occur only as
unit readouts, ratios to the vacuum speed of light, and displayed
multiple-choice values.
-/

/-! ## Dimensionful velocities, speeds, and scalar readouts -/

/-- A signed one-dimensional physical velocity. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative physical speed, independent of a choice of units. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a signed velocity in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a nonnegative speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Physlib's exact vacuum speed of light in the selected units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  signedVelocityReadout lengthUnit timeUnit DimSpeed.speedOfLight

/-- A signed velocity as the dimensionless ratio `beta = v / c`. -/
def velocityInLightSpeedUnits (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-- A nonnegative speed as a dimensionless multiple of `c`. -/
def speedInLightSpeedUnits (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-! ## Frames and primary-image labels -/

/-- The inertial frames needed to interpret the observations. -/
inductive ReferenceFrameLabel where
  | ground
  | spacecraftBRest
  deriving DecidableEq, Repr

/-- The two spacecraft labels printed in the image. -/
inductive SpacecraftLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The coordinate-origin labels printed in the image. -/
inductive OriginLabel where
  | O
  | OPrime
  deriving DecidableEq, Repr

/-- The four coordinate-axis labels printed in the image. -/
inductive CoordinateAxisLabel where
  | x
  | y
  | xPrime
  | yPrime
  deriving DecidableEq, Repr

/-- Horizontal or vertical orientation of a printed coordinate axis. -/
inductive AxisOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Orientation along the common horizontal motion axis. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-!
Qualitative and numerical evidence from `phyx_data/test_image/547.png`.
The image places `A` at `O'`, prints the `x,y` axes there and the `x',y'`
axes at `O`, and shows equal `0.85 c` arrows pointing left for `A` and right
for `B`.
-/
structure OpposingSpacecraftFigure where
  objectAtOrigin : OriginLabel → Option SpacecraftLabel
  horizontalAxisAtOrigin : OriginLabel → CoordinateAxisLabel
  verticalAxisAtOrigin : OriginLabel → CoordinateAxisLabel
  axisOrientation : CoordinateAxisLabel → AxisOrientation
  velocityArrowDirection : SpacecraftLabel → AxialDirection
  velocityArrowMagnitudeInLightSpeedUnits : SpacecraftLabel → ℝ

/-!
All physical quantities in the problem.  In particular,
`spacecraftAVelocityInBFrame` and `spacecraftARelativeToBSpeed` are unknown
observables: no field assigns either one a numerical value or answer label.
-/
structure OpposingSpacecraftSetup where
  figure : OpposingSpacecraftFigure
  groundFrame : ReferenceFrameLabel
  spacecraftBFrame : ReferenceFrameLabel
  spacecraftAVelocityInGroundFrame : SignedVelocityQuantity
  spacecraftBVelocityInGroundFrame : SignedVelocityQuantity
  spacecraftAVelocityInBFrame : SignedVelocityQuantity
  spacecraftARelativeToBSpeed : SpeedQuantity

/-! ## Figure/data readouts and governing physics -/

/-- The labels, axes, arrow directions, and arrow magnitudes read from the image. -/
def MatchesSuppliedFigure (setup : OpposingSpacecraftSetup) : Prop :=
  setup.figure.objectAtOrigin .O = none ∧
    setup.figure.objectAtOrigin .OPrime = some .A ∧
    setup.figure.horizontalAxisAtOrigin .O = .xPrime ∧
    setup.figure.verticalAxisAtOrigin .O = .yPrime ∧
    setup.figure.horizontalAxisAtOrigin .OPrime = .x ∧
    setup.figure.verticalAxisAtOrigin .OPrime = .y ∧
    setup.figure.axisOrientation .x = .horizontal ∧
    setup.figure.axisOrientation .xPrime = .horizontal ∧
    setup.figure.axisOrientation .y = .vertical ∧
    setup.figure.axisOrientation .yPrime = .vertical ∧
    setup.figure.velocityArrowDirection .A = .left ∧
    setup.figure.velocityArrowDirection .B = .right ∧
    setup.figure.velocityArrowMagnitudeInLightSpeedUnits .A = (17 / 20 : ℝ) ∧
    setup.figure.velocityArrowMagnitudeInLightSpeedUnits .B = (17 / 20 : ℝ)

/-!
Ground-frame numerical observations from the problem and figure.  Positive is
chosen to point right, so `A` has velocity `-0.85 c` and `B` has velocity
`+0.85 c`.
-/
def MatchesGroundFrameReadouts (setup : OpposingSpacecraftSetup) : Prop :=
  setup.groundFrame = .ground ∧
    setup.spacecraftBFrame = .spacecraftBRest ∧
    velocityInLightSpeedUnits setup.spacecraftAVelocityInGroundFrame =
      (-17 / 20 : ℝ) ∧
    velocityInLightSpeedUnits setup.spacecraftBVelocityInGroundFrame =
      (17 / 20 : ℝ)

/-!
Positivity of `c`, subluminality, and the opposing signs of the given
ground-frame velocities.  This predicate places no restriction on either
unknown B-frame observable.
-/
def HasPhysicalOpposingSpacecraftParameters
    (setup : OpposingSpacecraftSetup) : Prop :=
  0 < vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds ∧
    |velocityInLightSpeedUnits setup.spacecraftAVelocityInGroundFrame| < 1 ∧
    |velocityInLightSpeedUnits setup.spacecraftBVelocityInGroundFrame| < 1 ∧
    velocityInLightSpeedUnits setup.spacecraftAVelocityInGroundFrame < 0 ∧
    0 < velocityInLightSpeedUnits setup.spacecraftBVelocityInGroundFrame

/-!
The governing one-dimensional Lorentz velocity transformation

`beta_(A|B) = (beta_(A|G) - beta_(B|G)) /
  (1 - beta_(B|G) * beta_(A|G))`.

Its left-hand side remains an unknown signed velocity, and the law contains no
problem-specific B-frame result or multiple-choice value.
-/
def ObeysCollinearRelativisticVelocityTransformation
    (setup : OpposingSpacecraftSetup) : Prop :=
  velocityInLightSpeedUnits setup.spacecraftAVelocityInBFrame =
    (velocityInLightSpeedUnits setup.spacecraftAVelocityInGroundFrame -
      velocityInLightSpeedUnits setup.spacecraftBVelocityInGroundFrame) /
      (1 - velocityInLightSpeedUnits setup.spacecraftBVelocityInGroundFrame *
        velocityInLightSpeedUnits setup.spacecraftAVelocityInGroundFrame)

/-!
Operational meaning of the requested nonnegative relative speed: it is the
magnitude of `A`'s signed velocity component in spacecraft `B`'s rest frame.
-/
def RelativeSpeedIsMagnitudeOfBFrameVelocity
    (setup : OpposingSpacecraftSetup) : Prop :=
  speedInLightSpeedUnits setup.spacecraftARelativeToBSpeed =
    |velocityInLightSpeedUnits setup.spacecraftAVelocityInBFrame|

/-! ## Multiple-choice target -/

/-- Labels of the four choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed candidate speeds, as dimensionless multiples of `c`. -/
def answerChoiceInLightSpeedUnits : AnswerChoice → ℝ
  | .A => 135 / 1000
  | .B => 1301 / 1000
  | .C => 1700 / 1000
  | .D => 987 / 1000

/-- Nearest-thousandth agreement, using a half-open convention at ties. -/
def RoundsToNearestThousandth (value displayed : ℝ) : Prop :=
  displayed - 1 / 2000 ≤ value ∧ value < displayed + 1 / 2000

/-!
The Lorentz transformation gives `beta_(A|B) = -680/689`; hence the relative
speed is `(680/689)c`, which rounds to `0.987c`, answer choice D.  The exact
ratio is retained so the displayed three-decimal answer is not asserted as an
incorrect exact equality.

Blueprint label: `thm:physics:phyx_mini_0547:target`.
-/
theorem spacecraftARelativeToBSpeed_eq_choiceD
    (setup : OpposingSpacecraftSetup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesGroundFrameReadouts setup)
    (hPhysical : HasPhysicalOpposingSpacecraftParameters setup)
    (hLorentz : ObeysCollinearRelativisticVelocityTransformation setup)
    (hMagnitude : RelativeSpeedIsMagnitudeOfBFrameVelocity setup) :
    velocityInLightSpeedUnits setup.spacecraftAVelocityInBFrame =
        (-680 / 689 : ℝ) ∧
      speedInLightSpeedUnits setup.spacecraftARelativeToBSpeed =
        (680 / 689 : ℝ) ∧
      RoundsToNearestThousandth
        (speedInLightSpeedUnits setup.spacecraftARelativeToBSpeed)
        (answerChoiceInLightSpeedUnits .D) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0547
