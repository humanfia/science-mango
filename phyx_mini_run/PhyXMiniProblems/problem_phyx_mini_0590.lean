import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0590

open Dimension

/-!
# Three spaceships in a relativistic chase

Ships `A`, `B`, and `C` move rightward along the displayed `x`-axis.  An
Earth-frame observer measures `v_A = 0.900 c`, an unknown `v_B`, and
`v_C = 0.800 c`.  The required `v_B` makes `A` close on `B` from behind at
the same speed that `C` closes on `B` from ahead, with both speeds measured
in the rest frame of `B`.

Signed velocity components are represented by genuine dimensionful Physlib
quantities.  Real numbers below are used only for readouts in named units,
dimensionless fractions of the vacuum speed of light, qualitative image
coordinates, and the dimensionless coefficients printed in the answer table.
-/

/-! ## Dimensionful signed velocities and scalar readouts -/

/-- A signed physical velocity component along the common `x`-axis. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a signed velocity component using chosen length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Meter-per-second readout of a signed velocity component. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Physlib's dimensionful vacuum speed of light, read in SI units. -/
def vacuumLightSpeedInMetersPerSecond : ℝ :=
  signedVelocityInMetersPerSecond DimSpeed.speedOfLight

/-- A signed axial velocity component expressed as a dimensionless fraction of `c`. -/
def velocityFractionOfLight (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityInMetersPerSecond velocity /
    vacuumLightSpeedInMetersPerSecond

/-! ## Physical, frame, direction, and primary-figure labels -/

/-- The three physical spaceships named by the problem and shown in the image. -/
inductive ShipLabel where
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- The two inertial frames needed for the given and relative velocities. -/
inductive InertialFrameLabel where
  | earthFrame
  | shipBRestFrame
  deriving DecidableEq, Fintype, Repr

/-- Direction along the horizontal `x`-axis in the primary image. -/
inductive HorizontalDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Body colors that distinguish the three ships in the supplied raster. -/
inductive FigureColor where
  | red
  | blue
  | purple
  deriving DecidableEq, Repr

/-- The velocity-vector labels printed above the three ships. -/
inductive FigureVelocityLabel where
  | vA
  | vB
  | vC
  deriving DecidableEq, Repr

/-- The coordinate-axis label visible at the right end of the baseline. -/
inductive FigureAxisLabel where
  | x
  deriving DecidableEq, Repr

/-!
Typed qualitative evidence from image 590.  Horizontal coordinates preserve
only the left-to-right ordering in the drawing and are not physical distances
or simultaneous spacetime positions.
-/
structure ThreeSpaceshipChaseFigure where
  shipIsShown : ShipLabel → Bool
  shipHorizontalCoordinate : ShipLabel → ℝ
  shipBodyColor : ShipLabel → FigureColor
  shipBodyDirection : ShipLabel → HorizontalDirection
  velocityArrowIsShown : ShipLabel → Bool
  velocityArrowDirection : ShipLabel → HorizontalDirection
  velocityArrowLabel : ShipLabel → FigureVelocityLabel
  velocityArrowIsMagenta : ShipLabel → Bool
  baselineIsShown : Bool
  baselineLabel : FigureAxisLabel
  hasQuantitativePositionOrVelocityScale : Bool

/-!
The physical setup.  In particular, the Earth-frame velocity of ship `B`
and all velocities measured in `B`'s rest frame are independent physical
quantities; none is defined from a solved expression or answer choice.
-/
structure ThreeSpaceshipChaseSetup where
  givenVelocityFrame : InertialFrameLabel
  equalApproachSpeedFrame : InertialFrameLabel
  earthFrameMotionDirection : ShipLabel → HorizontalDirection
  velocityMeasuredIn : ShipLabel → InertialFrameLabel → SignedVelocityQuantity
  figure : ThreeSpaceshipChaseFigure

/-! ## Figure evidence and stated problem data -/

/-- Qualitative facts transcribed from the primary bitmap. -/
structure MatchesPrimaryFigure
    (setup : ThreeSpaceshipChaseSetup) : Prop where
  everyShipShown : ∀ ship, setup.figure.shipIsShown ship = true
  shipALeftOfShipB :
    setup.figure.shipHorizontalCoordinate .A <
      setup.figure.shipHorizontalCoordinate .B
  shipBLeftOfShipC :
    setup.figure.shipHorizontalCoordinate .B <
      setup.figure.shipHorizontalCoordinate .C
  shipAIsRed : setup.figure.shipBodyColor .A = .red
  shipBIsBlue : setup.figure.shipBodyColor .B = .blue
  shipCIsPurple : setup.figure.shipBodyColor .C = .purple
  everyShipBodyPointsRight :
    ∀ ship, setup.figure.shipBodyDirection ship = .positiveX
  everyVelocityArrowShown :
    ∀ ship, setup.figure.velocityArrowIsShown ship = true
  everyVelocityArrowPointsRight :
    ∀ ship, setup.figure.velocityArrowDirection ship = .positiveX
  shipAArrowLabel : setup.figure.velocityArrowLabel .A = .vA
  shipBArrowLabel : setup.figure.velocityArrowLabel .B = .vB
  shipCArrowLabel : setup.figure.velocityArrowLabel .C = .vC
  everyVelocityArrowIsMagenta :
    ∀ ship, setup.figure.velocityArrowIsMagenta ship = true
  horizontalBaselineShown : setup.figure.baselineIsShown = true
  horizontalBaselineLabel : setup.figure.baselineLabel = .x
  noQuantitativeScale :
    setup.figure.hasQuantitativePositionOrVelocityScale = false

/-!
Frame assignments, rightward Earth-frame motion, and the two given numerical
velocity readouts.  The unknown Earth-frame velocity of `B` is deliberately
not assigned a value here.
-/
structure MatchesProblemData
    (setup : ThreeSpaceshipChaseSetup) : Prop where
  givenVelocitiesUseEarthFrame :
    setup.givenVelocityFrame = .earthFrame
  comparisonUsesShipBRestFrame :
    setup.equalApproachSpeedFrame = .shipBRestFrame
  everyShipMovesRightInEarthFrame :
    ∀ ship, setup.earthFrameMotionDirection ship = .positiveX
  shipAEarthVelocityFraction :
    velocityFractionOfLight
        (setup.velocityMeasuredIn .A .earthFrame) = 9 / 10
  shipCEarthVelocityFraction :
    velocityFractionOfLight
        (setup.velocityMeasuredIn .C .earthFrame) = 4 / 5

/-!
Physical domain conditions.  They state positivity of `c`, that the three
Earth-frame velocity fractions are subluminal, and that `B` is at rest in its
own frame; they do not determine the unknown Earth-frame velocity of `B`.
-/
structure HasPhysicalVelocityParameters
    (setup : ThreeSpaceshipChaseSetup) : Prop where
  lightSpeedPositive : 0 < vacuumLightSpeedInMetersPerSecond
  everyEarthFrameVelocitySubluminal :
    ∀ ship,
      |velocityFractionOfLight
        (setup.velocityMeasuredIn ship .earthFrame)| < 1
  shipBAtRestInOwnFrame :
    velocityFractionOfLight
        (setup.velocityMeasuredIn .B .shipBRestFrame) = 0

/-! ## Governing special-relativistic law and equal-approach requirement -/

/-!
The one-dimensional Einstein velocity transformation from the Earth frame to
ship `B`'s rest frame.  For each ship with Earth-frame velocity fraction
`β_ship` and `B` with fraction `β_B`, the transformed signed fraction is

`(β_ship - β_B) / (1 - β_ship * β_B)`.

This is an unsolved governing law and contains neither the requested value of
`β_B` nor an answer-choice label.
-/
structure SatisfiesCollinearEinsteinVelocityTransformation
    (setup : ThreeSpaceshipChaseSetup) : Prop where
  velocityInShipBRestFrame :
    ∀ ship,
      velocityFractionOfLight
          (setup.velocityMeasuredIn ship .shipBRestFrame) =
        (velocityFractionOfLight
              (setup.velocityMeasuredIn ship .earthFrame) -
            velocityFractionOfLight
              (setup.velocityMeasuredIn .B .earthFrame)) /
          (1 -
            velocityFractionOfLight
                (setup.velocityMeasuredIn ship .earthFrame) *
              velocityFractionOfLight
                (setup.velocityMeasuredIn .B .earthFrame))

/-- The speed magnitude of a ship relative to `B`, expressed as a fraction of `c`. -/
def speedRelativeToShipBFraction
    (setup : ThreeSpaceshipChaseSetup) (ship : ShipLabel) : ℝ :=
  |velocityFractionOfLight
    (setup.velocityMeasuredIn ship .shipBRestFrame)|

/-!
The condition imposed by the question: in `B`'s frame, `A` closes from the
negative-`x` side, `C` closes from the positive-`x` side, and their approach
speed magnitudes are equal.  This constrains the unknown but does not state
its requested Earth-frame value.
-/
structure ApproachesShipBWithEqualSpeed
    (setup : ThreeSpaceshipChaseSetup) : Prop where
  shipAClosesFromBehind :
    0 < velocityFractionOfLight
      (setup.velocityMeasuredIn .A .shipBRestFrame)
  shipCClosesFromAhead :
    velocityFractionOfLight
        (setup.velocityMeasuredIn .C .shipBRestFrame) < 0
  equalApproachSpeedMagnitudes :
    speedRelativeToShipBFraction setup .A =
      speedRelativeToShipBFraction setup .C

/-! ## Displayed choices and current target -/

/-- Labels of the four velocity choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless coefficient multiplying `c` beside each choice. -/
def displayedShipBVelocityFraction : AnswerChoice → ℝ
  | .A => 4 / 5
  | .B => 17 / 20
  | .C => 429 / 500
  | .D => 7 / 8

/-- The source dataset records choice C; this is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a velocity fraction displayed to the nearest thousandth. -/
def RoundsToNearestThousandth
    (actualFraction displayedFraction : ℝ) : Prop :=
  |actualFraction - displayedFraction| < 1 / 2000

/-- A displayed choice agrees with the modeled Earth-frame velocity of `B`. -/
def MatchesAnswerChoice
    (setup : ThreeSpaceshipChaseSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestThousandth
    (velocityFractionOfLight
      (setup.velocityMeasuredIn .B .earthFrame))
    (displayedShipBVelocityFraction choice)

/-- The selected choice is the unique displayed rounding of `B`'s velocity. -/
def IsUniqueMatchingAnswerChoice
    (setup : ThreeSpaceshipChaseSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Equal approach speeds, the two given Earth-frame fractions, and Einstein's
velocity transformation determine the physical root

`v_B / c = (86 - 3 * √19) / 85`.

The second algebraic root is superluminal and is excluded by the physical
domain condition.  The exact result is a conclusion, not a data or law field.
-/
lemma shipB_velocity_fraction_exact
    (setup : ThreeSpaceshipChaseSetup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalVelocityParameters setup)
    (hRelativity : SatisfiesCollinearEinsteinVelocityTransformation setup)
    (hEqualApproach : ApproachesShipBWithEqualSpeed setup) :
    velocityFractionOfLight
        (setup.velocityMeasuredIn .B .earthFrame) =
      (86 - 3 * Real.sqrt 19) / 85 := by
  let x :=
    velocityFractionOfLight
      (setup.velocityMeasuredIn .B .earthFrame)
  have hx_abs : |x| < 1 :=
    hPhysical.everyEarthFrameVelocitySubluminal .B
  have hx_lt : x < 1 := (abs_lt.mp hx_abs).2
  have hdenA : 0 < 1 - (9 / 10 : ℝ) * x := by
    nlinarith
  have hdenC : 0 < 1 - (4 / 5 : ℝ) * x := by
    nlinarith
  have hA :=
    hRelativity.velocityInShipBRestFrame .A
  have hC :=
    hRelativity.velocityInShipBRestFrame .C
  rw [hData.shipAEarthVelocityFraction] at hA
  rw [hData.shipCEarthVelocityFraction] at hC
  change
    velocityFractionOfLight
        (setup.velocityMeasuredIn .A .shipBRestFrame) =
      ((9 / 10 : ℝ) - x) / (1 - (9 / 10 : ℝ) * x) at hA
  change
    velocityFractionOfLight
        (setup.velocityMeasuredIn .C .shipBRestFrame) =
      ((4 / 5 : ℝ) - x) / (1 - (4 / 5 : ℝ) * x) at hC
  have hEqual :=
    hEqualApproach.equalApproachSpeedMagnitudes
  unfold speedRelativeToShipBFraction at hEqual
  rw [abs_of_pos hEqualApproach.shipAClosesFromBehind,
    abs_of_neg hEqualApproach.shipCClosesFromAhead] at hEqual
  rw [hA, hC] at hEqual
  have hdenA' : 10 - 9 * x ≠ 0 := by
    nlinarith
  have hdenC' : 5 - 4 * x ≠ 0 := by
    nlinarith
  have hdenC'' : 5 - x * 4 ≠ 0 := by
    nlinarith
  field_simp [hdenA', hdenC', hdenC''] at hEqual
  have hquadratic : 85 * x ^ 2 - 172 * x + 85 = 0 := by
    nlinarith [hEqual]
  have hsqrt_sq : (Real.sqrt 19) ^ 2 = (19 : ℝ) := by
    norm_num
  have hfactor :
      (85 * x - 86 - 3 * Real.sqrt 19) *
          (85 * x - 86 + 3 * Real.sqrt 19) = 0 := by
    nlinarith [hquadratic, hsqrt_sq]
  rcases mul_eq_zero.mp hfactor with hLargerRoot | hPhysicalRoot
  · have hsqrt_nonneg : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg 19
    exfalso
    nlinarith
  · change x = (86 - 3 * Real.sqrt 19) / 85
    field_simp
    linarith

/-!
The exact fraction is approximately `0.857921`, so its nearest-thousandth
display is `0.858 c`, uniquely selecting choice C.

This formalizes `thm:physics:phyx_mini_0590:target`.
-/
theorem problem_phyx_mini_0590
    (setup : ThreeSpaceshipChaseSetup)
    (_hFigure : MatchesPrimaryFigure setup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalVelocityParameters setup)
    (hRelativity : SatisfiesCollinearEinsteinVelocityTransformation setup)
    (hEqualApproach : ApproachesShipBWithEqualSpeed setup) :
    velocityFractionOfLight
          (setup.velocityMeasuredIn .B .earthFrame) =
        (86 - 3 * Real.sqrt 19) / 85 ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hx :=
    shipB_velocity_fraction_exact setup hData hPhysical hRelativity
      hEqualApproach
  have hsqrt_lower : (4358 / 1000 : ℝ) < Real.sqrt 19 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num),
      Real.sqrt_nonneg 19]
  have hsqrt_upper : Real.sqrt 19 < (4359 / 1000 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num),
      Real.sqrt_nonneg 19]
  constructor
  · exact hx
  · unfold IsUniqueMatchingAnswerChoice
    constructor
    · unfold MatchesAnswerChoice RoundsToNearestThousandth
      rw [hx, abs_lt]
      norm_num [recordedDatasetAnswer, displayedShipBVelocityFraction]
      constructor <;> nlinarith
    · intro other hOther
      unfold MatchesAnswerChoice RoundsToNearestThousandth at hOther
      rw [hx, abs_lt] at hOther
      cases other with
      | A =>
          norm_num [displayedShipBVelocityFraction] at hOther
          exfalso
          nlinarith
      | B =>
          norm_num [displayedShipBVelocityFraction] at hOther
          exfalso
          nlinarith
      | C => rfl
      | D =>
          norm_num [displayedShipBVelocityFraction] at hOther
          exfalso
          nlinarith

end PhyXMiniProblems.ProblemPhyXMini0590
