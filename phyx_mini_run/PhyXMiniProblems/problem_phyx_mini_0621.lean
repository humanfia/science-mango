import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0621

/-!
# Speed of rocket 2 relative to Earth

The primary figure shows rocket 1 moving away from Earth at `0.60 c` and
rocket 2 moving in the same direction at `0.60 c` relative to rocket 1.  The
unknown is rocket 2's speed in Earth's rest frame.  Hence the relevant law is
same-direction, one-dimensional Einstein velocity addition rather than
Galilean addition.

Physical speeds are represented by Physlib's nonnegative, unit-independent
`DimSpeed`.  Real numbers below are used only for SI readouts, dimensionless
fractions of the vacuum speed of light, qualitative figure coordinates, and
the coefficients printed in the multiple-choice answers.

Assumption/target split:

* `MatchesSuppliedRocketFigure` transcribes the object labels, qualitative
  layout, motion cues, and the two `0.60c` annotations in image `621.png`;
* `MatchesFigureVelocityReadouts` connects only those two annotations to the
  corresponding independent physical relative speeds;
* `MatchesCollinearRocketScenario` records the positive common-axis directions;
* `HasPhysicalInputSpeeds` records positivity and subluminality only for the
  two supplied input speeds;
* `SatisfiesCollinearEinsteinVelocityAddition` is the generic governing law;
* the Earth-frame speed of rocket 2, the fraction `15/17`, its rounding to
  `0.88c`, and the correctness of choice C occur only in the final conclusion.
-/

/-! ## Dimensionful speeds and scalar readouts -/

/-- A nonnegative physical speed with length-per-time dimension. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Physical, frame, and primary-figure labels -/

/-- The three physical bodies named in the supplied diagram. -/
inductive BodyLabel where
  | earth
  | rocket1
  | rocket2
  deriving DecidableEq, Fintype, Repr

/-- Rest frames carried by the three named bodies. -/
inductive InertialFrameLabel where
  | earthRest
  | rocket1Rest
  | rocket2Rest
  deriving DecidableEq, Fintype, Repr

/-- The rest frame canonically associated to a body label. -/
def restFrame : BodyLabel → InertialFrameLabel
  | .earth => .earthRest
  | .rocket1 => .rocket1Rest
  | .rocket2 => .rocket2Rest

/-- The two rockets whose orientation is visible in the image. -/
inductive RocketLabel where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- Associate each printed rocket number to its physical body. -/
def rocketBody : RocketLabel → BodyLabel
  | .one => .rocket1
  | .two => .rocket2

/-- Positive means outward from Earth along the common motion axis. -/
inductive AxisDirection where
  | positiveAwayFromEarth
  | negativeTowardEarth
  | stationary
  deriving DecidableEq, Fintype, Repr

/-- Coarse regions used only to transcribe the qualitative bitmap layout. -/
inductive FigureRegion where
  | lowerLeft
  | center
  | upperRight
  deriving DecidableEq, Fintype, Repr

/-- Literal labels printed next to the bodies. -/
inductive PrintedBodyLabel where
  | earthText
  | numeralOne
  | numeralTwo
  deriving DecidableEq, Fintype, Repr

/-- The two velocity symbols printed in the figure. -/
inductive VelocityAnnotation where
  | v
  | uPrime
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and textual information carried by the `298 × 280` primary
raster.  Regions are presentation data, not physical positions.  Likewise,
`annotationCoefficientOfC` is the dimensionless number printed next to an
annotation, not a definition of any physical speed.
-/
structure RocketVelocityFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  bodyShown : BodyLabel → Bool
  bodyRegion : BodyLabel → FigureRegion
  printedBodyLabel : BodyLabel → PrintedBodyLabel
  annotationMovingBody : VelocityAnnotation → BodyLabel
  annotationReferenceBody : VelocityAnnotation → BodyLabel
  annotationCoefficientOfC : VelocityAnnotation → ℝ
  annotationSaysWithRespectTo : VelocityAnnotation → Bool
  rocketPointsAlongPositiveAxis : RocketLabel → Bool
  rocketExhaustTrailShown : RocketLabel → Bool
  outwardDottedPathShown : Bool
  rocketsHaveParallelOrientation : Bool

/-!
The speed of each body relative to each named rest frame is independent data.
In particular, the `.rocket2`/`.earthRest` entry is not defined from an answer
choice or from the Einstein-addition expression.
-/
structure CollinearRocketSetup where
  figure : RocketVelocityFigure
  relativeSpeed : BodyLabel → InertialFrameLabel → SpeedQuantity
  relativeDirection : BodyLabel → InertialFrameLabel → AxisDirection

/-- A physical relative speed expressed as a dimensionless fraction of `c`. -/
def speedFractionOfLight
    (setup : CollinearRocketSetup)
    (movingBody : BodyLabel) (observerFrame : InertialFrameLabel) : ℝ :=
  speedInMetersPerSecond (setup.relativeSpeed movingBody observerFrame) /
    vacuumSpeedOfLightInMetersPerSecond

/-! ## Figure evidence, supplied readouts, and physical regime -/

/-- Literal and qualitative facts read from the primary image `621.png`. -/
structure MatchesSuppliedRocketFigure
    (figure : RocketVelocityFigure) : Prop where
  rasterWidthIs298 : figure.rasterWidthPixels = 298
  rasterHeightIs280 : figure.rasterHeightPixels = 280
  earthIsShown : figure.bodyShown .earth = true
  rocketOneIsShown : figure.bodyShown .rocket1 = true
  rocketTwoIsShown : figure.bodyShown .rocket2 = true
  earthIsAtLowerLeft : figure.bodyRegion .earth = .lowerLeft
  rocketOneIsAtCenter : figure.bodyRegion .rocket1 = .center
  rocketTwoIsAtUpperRight : figure.bodyRegion .rocket2 = .upperRight
  earthLabelIsPrinted : figure.printedBodyLabel .earth = .earthText
  rocketOneLabelIsPrinted : figure.printedBodyLabel .rocket1 = .numeralOne
  rocketTwoLabelIsPrinted : figure.printedBodyLabel .rocket2 = .numeralTwo
  vLabelsRocketOne : figure.annotationMovingBody .v = .rocket1
  vIsRelativeToEarth : figure.annotationReferenceBody .v = .earth
  vCoefficientIsPointSix : figure.annotationCoefficientOfC .v = 3 / 5
  vSaysWithRespectTo : figure.annotationSaysWithRespectTo .v = true
  uPrimeLabelsRocketTwo : figure.annotationMovingBody .uPrime = .rocket2
  uPrimeIsRelativeToRocketOne :
    figure.annotationReferenceBody .uPrime = .rocket1
  uPrimeCoefficientIsPointSix :
    figure.annotationCoefficientOfC .uPrime = 3 / 5
  uPrimeSaysWithRespectTo :
    figure.annotationSaysWithRespectTo .uPrime = true
  rocketOnePointsOutward :
    figure.rocketPointsAlongPositiveAxis .one = true
  rocketTwoPointsOutward :
    figure.rocketPointsAlongPositiveAxis .two = true
  rocketOneHasExhaustTrail : figure.rocketExhaustTrailShown .one = true
  rocketTwoHasExhaustTrail : figure.rocketExhaustTrailShown .two = true
  outwardPathIsDotted : figure.outwardDottedPathShown = true
  rocketsAreParallelInTheDrawing :
    figure.rocketsHaveParallelOrientation = true

/-!
The two same-direction relations needed to compose the supplied speeds.  The
unknown direction of rocket 2 relative to Earth is deliberately absent.
-/
structure MatchesCollinearRocketScenario
    (setup : CollinearRocketSetup) : Prop where
  rocketOneMovesPositivelyInEarthFrame :
    setup.relativeDirection .rocket1 (restFrame .earth) =
      .positiveAwayFromEarth
  rocketTwoMovesPositivelyInRocketOneFrame :
    setup.relativeDirection .rocket2 (restFrame .rocket1) =
      .positiveAwayFromEarth

/-!
Connect the printed annotations to physical speeds.  Their numerical values
remain in `MatchesSuppliedRocketFigure`; no Earth-frame readout for rocket 2
is supplied here.
-/
structure MatchesFigureVelocityReadouts
    (setup : CollinearRocketSetup) : Prop where
  rocketOneRelativeToEarthMatchesV :
    speedFractionOfLight setup .rocket1 (restFrame .earth) =
      setup.figure.annotationCoefficientOfC .v
  rocketTwoRelativeToRocketOneMatchesUPrime :
    speedFractionOfLight setup .rocket2 (restFrame .rocket1) =
      setup.figure.annotationCoefficientOfC .uPrime

/-!
Physical-domain conditions only on the two supplied input speeds.  No field
constrains the requested speed of rocket 2 in Earth's frame.
-/
structure HasPhysicalInputSpeeds
    (setup : CollinearRocketSetup) : Prop where
  vacuumSpeedOfLightPositive : 0 < vacuumSpeedOfLightInMetersPerSecond
  rocketOneEarthSpeedNonnegative :
    0 ≤ speedFractionOfLight setup .rocket1 (restFrame .earth)
  rocketOneEarthSpeedSubluminal :
    speedFractionOfLight setup .rocket1 (restFrame .earth) < 1
  rocketTwoRocketOneSpeedNonnegative :
    0 ≤ speedFractionOfLight setup .rocket2 (restFrame .rocket1)
  rocketTwoRocketOneSpeedSubluminal :
    speedFractionOfLight setup .rocket2 (restFrame .rocket1) < 1

/-! ## Governing special-relativistic law -/

/-!
For any three named bodies with successive positive, subluminal collinear
speeds `β₁` and `β₂`, special relativity gives

`(β₁ + β₂) / (1 + β₁ β₂)`.

This is quantified as a governing law.  It contains no `0.88`, `15/17`, or
answer label and is not specialized to the current target triple.
-/
structure SatisfiesCollinearEinsteinVelocityAddition
    (setup : CollinearRocketSetup) : Prop where
  velocityAdditionLaw :
    ∀ moving intermediate reference,
      setup.relativeDirection intermediate (restFrame reference) =
          .positiveAwayFromEarth →
      setup.relativeDirection moving (restFrame intermediate) =
          .positiveAwayFromEarth →
      0 ≤ speedFractionOfLight setup intermediate (restFrame reference) →
      speedFractionOfLight setup intermediate (restFrame reference) < 1 →
      0 ≤ speedFractionOfLight setup moving (restFrame intermediate) →
      speedFractionOfLight setup moving (restFrame intermediate) < 1 →
      speedFractionOfLight setup moving (restFrame reference) =
        (speedFractionOfLight setup intermediate (restFrame reference) +
            speedFractionOfLight setup moving (restFrame intermediate)) /
          (1 +
            speedFractionOfLight setup intermediate (restFrame reference) *
              speedFractionOfLight setup moving (restFrame intermediate))

/-! ## Printed choices and current target -/

/-- Labels of the four speed choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless coefficient of `c` printed beside each answer label. -/
def displayedAnswerFractionOfC : AnswerChoice → ℝ
  | .A => 33 / 50
  | .B => 77 / 100
  | .C => 22 / 25
  | .D => 99 / 100

/-!
Generic half-open nearest-hundredth rounding.  The existential integer ensures
that the displayed value itself lies on the hundredth grid; this definition
contains no distinguished answer value or label.
-/
def RoundsToNearestHundredth
    (exactFraction displayedFraction : ℝ) : Prop :=
  ∃ hundredths : ℤ,
    displayedFraction = (hundredths : ℝ) / 100 ∧
      ((hundredths : ℝ) - 1 / 2) / 100 ≤ exactFraction ∧
      exactFraction < ((hundredths : ℝ) + 1 / 2) / 100

/-- A choice matches the computed Earth-frame speed to two decimal places. -/
def MatchesRocketTwoEarthSpeedChoice
    (setup : CollinearRocketSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredth
    (speedFractionOfLight setup .rocket2 (restFrame .earth))
    (displayedAnswerFractionOfC choice)

/-- The selected answer is the unique printed choice matching that speed. -/
def IsUniqueMatchingAnswerChoice
    (setup : CollinearRocketSetup) (choice : AnswerChoice) : Prop :=
  MatchesRocketTwoEarthSpeedChoice setup choice ∧
    ∀ other : AnswerChoice,
      MatchesRocketTwoEarthSpeedChoice setup other → other = choice

/-!
Applying the general Einstein law to rocket 2, rocket 1, and Earth gives

`(3/5 + 3/5) / (1 + (3/5)(3/5)) = 15/17`.

This is approximately `0.88235`, which rounds to the displayed `0.88c` and
uniquely selects choice C.

Blueprint: `thm:physics:phyx_mini_0621:target`.
-/
theorem problem_phyx_mini_0621
    (setup : CollinearRocketSetup)
    (hFigure : MatchesSuppliedRocketFigure setup.figure)
    (hScenario : MatchesCollinearRocketScenario setup)
    (hReadouts : MatchesFigureVelocityReadouts setup)
    (hPhysical : HasPhysicalInputSpeeds setup)
    (hRelativity : SatisfiesCollinearEinsteinVelocityAddition setup) :
    speedFractionOfLight setup .rocket2 (restFrame .earth) = 15 / 17 ∧
      IsUniqueMatchingAnswerChoice setup .C := by
  have hRocketOne :
      speedFractionOfLight setup .rocket1 (restFrame .earth) = 3 / 5 := by
    calc
      speedFractionOfLight setup .rocket1 (restFrame .earth) =
          setup.figure.annotationCoefficientOfC .v :=
        hReadouts.rocketOneRelativeToEarthMatchesV
      _ = 3 / 5 := hFigure.vCoefficientIsPointSix
  have hRocketTwo :
      speedFractionOfLight setup .rocket2 (restFrame .rocket1) = 3 / 5 := by
    calc
      speedFractionOfLight setup .rocket2 (restFrame .rocket1) =
          setup.figure.annotationCoefficientOfC .uPrime :=
        hReadouts.rocketTwoRelativeToRocketOneMatchesUPrime
      _ = 3 / 5 := hFigure.uPrimeCoefficientIsPointSix
  have hSpeed :
      speedFractionOfLight setup .rocket2 (restFrame .earth) = 15 / 17 := by
    calc
      speedFractionOfLight setup .rocket2 (restFrame .earth) =
          (speedFractionOfLight setup .rocket1 (restFrame .earth) +
              speedFractionOfLight setup .rocket2 (restFrame .rocket1)) /
            (1 +
              speedFractionOfLight setup .rocket1 (restFrame .earth) *
                speedFractionOfLight setup .rocket2 (restFrame .rocket1)) :=
        hRelativity.velocityAdditionLaw
          .rocket2 .rocket1 .earth
          hScenario.rocketOneMovesPositivelyInEarthFrame
          hScenario.rocketTwoMovesPositivelyInRocketOneFrame
          hPhysical.rocketOneEarthSpeedNonnegative
          hPhysical.rocketOneEarthSpeedSubluminal
          hPhysical.rocketTwoRocketOneSpeedNonnegative
          hPhysical.rocketTwoRocketOneSpeedSubluminal
      _ = 15 / 17 := by
        rw [hRocketOne, hRocketTwo]
        norm_num
  refine ⟨hSpeed, ?_⟩
  constructor
  · unfold MatchesRocketTwoEarthSpeedChoice RoundsToNearestHundredth
    refine ⟨88, ?_, ?_, ?_⟩
    · norm_num [displayedAnswerFractionOfC]
    · rw [hSpeed]
      norm_num
    · rw [hSpeed]
      norm_num
  · intro other hOther
    cases other with
    | A =>
        simp only [MatchesRocketTwoEarthSpeedChoice,
          RoundsToNearestHundredth, displayedAnswerFractionOfC] at hOther
        rcases hOther with ⟨hundredths, hDisplayed, _hLower, hUpper⟩
        have hHundredths : (hundredths : ℝ) = 66 := by
          norm_num at hDisplayed
          linarith
        rw [hSpeed, hHundredths] at hUpper
        norm_num at hUpper
    | B =>
        simp only [MatchesRocketTwoEarthSpeedChoice,
          RoundsToNearestHundredth, displayedAnswerFractionOfC] at hOther
        rcases hOther with ⟨hundredths, hDisplayed, _hLower, hUpper⟩
        have hHundredths : (hundredths : ℝ) = 77 := by
          norm_num at hDisplayed
          linarith
        rw [hSpeed, hHundredths] at hUpper
        norm_num at hUpper
    | C => rfl
    | D =>
        simp only [MatchesRocketTwoEarthSpeedChoice,
          RoundsToNearestHundredth, displayedAnswerFractionOfC] at hOther
        rcases hOther with ⟨hundredths, hDisplayed, hLower, _hUpper⟩
        have hHundredths : (hundredths : ℝ) = 99 := by
          norm_num at hDisplayed
          linarith
        rw [hSpeed, hHundredths] at hLower
        norm_num at hLower

end PhyXMiniProblems.ProblemPhyXMini0621
