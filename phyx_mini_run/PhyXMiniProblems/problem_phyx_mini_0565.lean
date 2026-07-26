import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Apply
import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0565

/-!
# A rocket velocity seen from a boosted frame

Observer `O` measures a rocket speed of `0.60 c` at an angle of `45°` above
the positive `x`-axis. Observer `O'` moves at `0.80 c` in the positive
`x`-direction relative to `O`. The requested quantity is the magnitude of
the rocket's velocity measured by `O'`.

Physlib's `Lorentz.Velocity 2` represents a future-directed, unit-normalized
four-velocity in two spatial dimensions. Its spatial component divided by
its time component is the corresponding three-velocity component in units
where `c = 1`. All scalar speeds below are explicitly dimensionless fractions
of the vacuum speed of light.

The supplied raster depicts two rockets `A` and `B` in Earth and rocket-A
views rather than the oblique single-rocket scenario in the prose. Its labels
and arrow directions are retained as auxiliary figure evidence, but the
uncalibrated drawing is not used as numerical velocity data.
-/

/-! ## Planar velocity readouts -/

/-- The two spatial axes used for the physical velocity calculation. -/
inductive PlanarAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- The `Fin 2` coordinate associated with a named planar axis. -/
def planarAxisIndex : PlanarAxis → Fin 2
  | .x => 0
  | .y => 1

/-- Interpret a real-valued degree reading as a mathematical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  (value * Real.pi / 180 : ℝ)

/-!
The measured three-velocity component `vᵢ/c = Uᵢ/U⁰` obtained from a
Physlib four-velocity. This is a scalar readout of a physical Lorentz
velocity, not a scalar replacement for the velocity itself.
-/
def velocityComponentFractionOfC
    (velocity : Lorentz.Velocity 2) (axis : PlanarAxis) : ℝ :=
  (Lorentz.Vector.spatialPart velocity.1) (planarAxisIndex axis) /
    Lorentz.Vector.timeComponent velocity.1

/-- Euclidean speed magnitude as a dimensionless fraction of `c`. -/
def speedFractionOfC (velocity : Lorentz.Velocity 2) : ℝ :=
  Real.sqrt
    (∑ axis : PlanarAxis,
      (velocityComponentFractionOfC velocity axis) ^ 2)

/-! ## Physical frames and motion roles -/

/-- The two inertial observers distinguished in the prose problem. -/
inductive InertialFrameLabel where
  | observerO
  | observerOPrime
  deriving DecidableEq, Fintype, Repr

/-- Orientation along a named coordinate axis. -/
inductive AxisDirection where
  | negative
  | positive
  deriving DecidableEq, Repr

/-! ## Auxiliary primary-raster vocabulary -/

/-- The two panels visible in the supplied image. -/
inductive FigurePanel where
  | earthObserverView
  | rocketAObserverView
  deriving DecidableEq, Fintype, Repr

/-- Observer labels printed beside the red stick figures. -/
inductive FigureObserverLabel where
  | Oearth
  | OA
  deriving DecidableEq, Fintype, Repr

/-- Frame-origin labels printed under the vertical rocket-frame axes. -/
inductive FigureOriginLabel where
  | OA
  | OB
  deriving DecidableEq, Fintype, Repr

/-- The two rockets labeled in the supplied image. -/
inductive FigureRocketLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Coordinate labels occurring in the two panels. -/
inductive FigureAxisLabel where
  | x
  | xA
  | xB
  | y
  | yA
  | yB
  deriving DecidableEq, Fintype, Repr

/-- Velocity-arrow symbols printed in the raster. -/
inductive FigureVelocityArrow where
  | VA
  | VB
  | VAB
  deriving DecidableEq, Fintype, Repr

/-- Horizontal arrow direction in the drawing. -/
inductive FigureArrowDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-!
Typed evidence carried by image 565. The common-axis relation is recorded as
a displayed symbolic relation because the drawing supplies no calibrated
position or velocity scale.
-/
structure TwoRocketAuxiliaryFigure where
  observerShown : FigureObserverLabel → Bool
  observerPanel : FigureObserverLabel → FigurePanel
  originShown : FigurePanel → FigureOriginLabel → Bool
  rocketShown : FigurePanel → FigureRocketLabel → Bool
  axisLabelShown : FigureAxisLabel → Bool
  velocityArrowShown : FigureVelocityArrow → Bool
  velocityArrowPanel : FigureVelocityArrow → FigurePanel
  velocityArrowDirection : FigureVelocityArrow → FigureArrowDirection
  showsCommonAxisRelation_x_eq_xA_eq_neg_xB : Bool
  hasQuantitativePositionOrVelocityScale : Bool

/-!
Independent physical data for the prose scenario. The rocket has a separate
Physlib four-velocity in each frame. The requested `O'` velocity is not
defined from a numerical answer or from the expected closed form below.
-/
structure ObliqueRocketBoostSetup where
  givenMeasurementFrame : InertialFrameLabel
  requestedMeasurementFrame : InertialFrameLabel
  observerOPrimeMotionAxisInO : PlanarAxis
  observerOPrimeMotionDirectionInO : AxisDirection
  /-- The dimensionless frame speed `v_{O'}/c` measured by `O`. -/
  observerOPrimeSpeedFractionOfCInO : ℝ
  rocketFourVelocityMeasuredIn : InertialFrameLabel → Lorentz.Velocity 2
  rocketDirectionAngleInO : Real.Angle
  figure : TwoRocketAuxiliaryFigure

/-! ## Scenario, source data, and figure evidence -/

/-- Qualitative frame and boost-axis assignments stated in the question. -/
structure MatchesObliqueRocketScenario
    (setup : ObliqueRocketBoostSetup) : Prop where
  initialMeasurementIsByO :
    setup.givenMeasurementFrame = .observerO
  requestedMeasurementIsByOPrime :
    setup.requestedMeasurementFrame = .observerOPrime
  observerOPrimeMovesAlongCommonX :
    setup.observerOPrimeMotionAxisInO = .x
  observerOPrimeMovesInPositiveX :
    setup.observerOPrimeMotionDirectionInO = .positive

/-!
The numerical readouts given in the prose. They constrain only the velocity
measured by `O`, its direction, and the relative frame speed; no `O'` rocket
speed or answer choice occurs here.
-/
structure MatchesProblemReadouts
    (setup : ObliqueRocketBoostSetup) : Prop where
  rocketSpeedMeasuredByOIsPointSix :
    speedFractionOfC
        (setup.rocketFourVelocityMeasuredIn .observerO) = 3 / 5
  rocketDirectionMeasuredByOIsFortyFiveDegrees :
    setup.rocketDirectionAngleInO = degrees 45
  observerOPrimeSpeedMeasuredByOIsPointEight :
    setup.observerOPrimeSpeedFractionOfCInO = 4 / 5

/-!
Facts transcribed from the supplied two-panel raster. In the Earth view,
`V_A` points right and `V_B` points left; in the `O_A` view, `V_AB` points
left. The displayed relation `x ≡ x_A ≡ -x_B` is schematic only.
-/
structure MatchesSuppliedTwoRocketFigure
    (setup : ObliqueRocketBoostSetup) : Prop where
  earthObserverShown : setup.figure.observerShown .Oearth = true
  rocketAObserverShown : setup.figure.observerShown .OA = true
  earthObserverInLeftPanel :
    setup.figure.observerPanel .Oearth = .earthObserverView
  rocketAObserverInRightPanel :
    setup.figure.observerPanel .OA = .rocketAObserverView
  bothOriginsShownInBothPanels :
    ∀ panel origin, setup.figure.originShown panel origin = true
  bothRocketsShownInBothPanels :
    ∀ panel rocket, setup.figure.rocketShown panel rocket = true
  everyAxisLabelShown :
    ∀ axis, setup.figure.axisLabelShown axis = true
  everyVelocityArrowShown :
    ∀ arrow, setup.figure.velocityArrowShown arrow = true
  VAIsInEarthPanel :
    setup.figure.velocityArrowPanel .VA = .earthObserverView
  VBIsInEarthPanel :
    setup.figure.velocityArrowPanel .VB = .earthObserverView
  VABIsInRocketAPanel :
    setup.figure.velocityArrowPanel .VAB = .rocketAObserverView
  VAPointsRight :
    setup.figure.velocityArrowDirection .VA = .right
  VBPointsLeft :
    setup.figure.velocityArrowDirection .VB = .left
  VABPointsLeft :
    setup.figure.velocityArrowDirection .VAB = .left
  commonAxisRelationShown :
    setup.figure.showsCommonAxisRelation_x_eq_xA_eq_neg_xB = true
  noQuantitativeScale :
    setup.figure.hasQuantitativePositionOrVelocityScale = false

/-!
Physical domain conditions on the two supplied speeds. The
`Lorentz.Velocity` type already enforces unit Minkowski norm and future
direction for both rocket four-velocities.
-/
structure HasPhysicalInputParameters
    (setup : ObliqueRocketBoostSetup) : Prop where
  observerFrameSpeedIsPositive :
    0 < setup.observerOPrimeSpeedFractionOfCInO
  observerFrameSpeedIsSubluminal :
    |setup.observerOPrimeSpeedFractionOfCInO| < 1
  rocketSpeedMeasuredByOIsNonnegative :
    0 ≤ speedFractionOfC
      (setup.rocketFourVelocityMeasuredIn .observerO)
  rocketSpeedMeasuredByOIsSubluminal :
    speedFractionOfC
        (setup.rocketFourVelocityMeasuredIn .observerO) < 1

/-! ## Governing geometry and special-relativistic law -/

/-!
The standard polar decomposition of the rocket's measured planar velocity.
This is a general relation using the setup's independent speed and angle
readouts; it does not contain the requested transformed speed.
-/
structure SatisfiesPlanarVelocityGeometry
    (setup : ObliqueRocketBoostSetup) : Prop where
  xComponentFromSpeedAndAngle :
    velocityComponentFractionOfC
        (setup.rocketFourVelocityMeasuredIn .observerO) .x =
      speedFractionOfC
          (setup.rocketFourVelocityMeasuredIn .observerO) *
        Real.Angle.cos setup.rocketDirectionAngleInO
  yComponentFromSpeedAndAngle :
    velocityComponentFractionOfC
        (setup.rocketFourVelocityMeasuredIn .observerO) .y =
      speedFractionOfC
          (setup.rocketFourVelocityMeasuredIn .observerO) *
        Real.Angle.sin setup.rocketDirectionAngleInO

/-!
The governing frame-change law. Physlib's standard Lorentz boost along the
first spatial coordinate acts on the rocket four-velocity measured by `O` to
give the independent four-velocity measured by `O'`. The subluminality proof
is the explicit parameter required by `LorentzGroup.boost`.
-/
structure SatisfiesLorentzBoostVelocityLaw
    (setup : ObliqueRocketBoostSetup)
    (hObserverSubluminal :
      |setup.observerOPrimeSpeedFractionOfCInO| < 1) : Prop where
  rocketFourVelocityTransformsByXBoost :
    (setup.rocketFourVelocityMeasuredIn .observerOPrime).1 =
      LorentzGroup.boost
          (planarAxisIndex .x)
          setup.observerOPrimeSpeedFractionOfCInO
          hObserverSubluminal •
        (setup.rocketFourVelocityMeasuredIn .observerO).1

/-! ## Exact transformed value, displayed choices, and current target -/

/-!
The closed-form speed fraction obtained from the longitudinal and transverse
velocity-transformation formulas. It is built only from the supplied `0.60`,
`45°`, and `0.80` inputs. Equality of the independently stored `O'` speed
with this expression remains a theorem, not a definition.
-/
def expectedRocketSpeedFractionInOPrime : ℝ :=
  let rocketSpeed : ℝ := 3 / 5
  let rocketAngle : Real.Angle := degrees 45
  let frameSpeed : ℝ := 4 / 5
  let initialX : ℝ := rocketSpeed * Real.Angle.cos rocketAngle
  let initialY : ℝ := rocketSpeed * Real.Angle.sin rocketAngle
  let denominator : ℝ := 1 - frameSpeed * initialX
  let transformedX : ℝ :=
    (initialX - frameSpeed) / denominator
  let transformedY : ℝ :=
    initialY / (LorentzGroup.γ frameSpeed * denominator)
  Real.sqrt (transformedX ^ 2 + transformedY ^ 2)

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed speed coefficient multiplying `c` for each choice. -/
def displayedSpeedFraction : AnswerChoice → ℝ
  | .A => 11 / 20
  | .B => 69 / 100
  | .C => 19 / 20
  | .D => 51 / 5

/-- The source dataset records choice B; this is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a speed fraction displayed to the nearest hundredth. -/
def RoundsToNearestHundredth
    (actualFraction displayedFraction : ℝ) : Prop :=
  |actualFraction - displayedFraction| < 1 / 200

/-- A displayed choice agrees with the modeled speed measured by `O'`. -/
def MatchesAnswerChoice
    (setup : ObliqueRocketBoostSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredth
    (speedFractionOfC
      (setup.rocketFourVelocityMeasuredIn .observerOPrime))
    (displayedSpeedFraction choice)

/-- The selected choice is the unique displayed rounding of the speed. -/
def IsUniqueMatchingAnswerChoice
    (setup : ObliqueRocketBoostSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
The Lorentz boost and polar input data determine the exact transformed speed
fraction represented by `expectedRocketSpeedFractionInOPrime`.
-/
lemma rocket_speed_fraction_in_OPrime_exact
    (setup : ObliqueRocketBoostSetup)
    (hData : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hGeometry : SatisfiesPlanarVelocityGeometry setup)
    (hRelativity : SatisfiesLorentzBoostVelocityLaw setup
      hPhysical.observerFrameSpeedIsSubluminal) :
    speedFractionOfC
        (setup.rocketFourVelocityMeasuredIn .observerOPrime) =
      expectedRocketSpeedFractionInOPrime := by
  classical
  let u := setup.rocketFourVelocityMeasuredIn .observerO
  let u' := setup.rocketFourVelocityMeasuredIn .observerOPrime
  let β := setup.observerOPrimeSpeedFractionOfCInO
  have hTransform : (u').1 =
      LorentzGroup.boost (planarAxisIndex .x) β
          hPhysical.observerFrameSpeedIsSubluminal • u.1 := by
    exact hRelativity.rocketFourVelocityTransformsByXBoost
  have hTime : Lorentz.Vector.timeComponent (u').1 =
      LorentzGroup.γ β *
        (Lorentz.Vector.timeComponent u.1 -
          β * (Lorentz.Vector.spatialPart u.1) (planarAxisIndex .x)) := by
    rw [hTransform]
    exact Lorentz.Vector.boost_time_eq
      (planarAxisIndex .x) β
      hPhysical.observerFrameSpeedIsSubluminal u.1
  have hXCoord :
      (Lorentz.Vector.spatialPart (u').1) (planarAxisIndex .x) =
        LorentzGroup.γ β *
          ((Lorentz.Vector.spatialPart u.1) (planarAxisIndex .x) -
            β * Lorentz.Vector.timeComponent u.1) := by
    rw [hTransform]
    exact Lorentz.Vector.boost_inr_self_eq
      (planarAxisIndex .x) β
      hPhysical.observerFrameSpeedIsSubluminal u.1
  have hYCoord :
      (Lorentz.Vector.spatialPart (u').1) (planarAxisIndex .y) =
        (Lorentz.Vector.spatialPart u.1) (planarAxisIndex .y) := by
    rw [hTransform]
    exact Lorentz.Vector.boost_inr_other_eq
      (planarAxisIndex .x) (planarAxisIndex .y) (by decide) β
      hPhysical.observerFrameSpeedIsSubluminal u.1
  have huTime : Lorentz.Vector.timeComponent u.1 ≠ 0 :=
    ne_of_gt (Lorentz.Velocity.timeComponent_pos u)
  have hu'Time : Lorentz.Vector.timeComponent (u').1 ≠ 0 :=
    ne_of_gt (Lorentz.Velocity.timeComponent_pos u')
  have hGamma : LorentzGroup.γ β ≠ 0 := by
    intro hZero
    apply hu'Time
    rw [hTime, hZero, zero_mul]
  have hBoostDenominator :
      Lorentz.Vector.timeComponent u.1 -
          β * (Lorentz.Vector.spatialPart u.1) (planarAxisIndex .x) ≠ 0 := by
    intro hZero
    apply hu'Time
    rw [hTime, hZero, mul_zero]
  have hX :
      velocityComponentFractionOfC u' .x =
        (velocityComponentFractionOfC u .x - β) /
          (1 - β * velocityComponentFractionOfC u .x) := by
    unfold velocityComponentFractionOfC
    rw [hXCoord, hTime]
    field_simp [huTime, hGamma, hBoostDenominator]
  have hY :
      velocityComponentFractionOfC u' .y =
        velocityComponentFractionOfC u .y /
          (LorentzGroup.γ β *
            (1 - β * velocityComponentFractionOfC u .x)) := by
    unfold velocityComponentFractionOfC
    rw [hYCoord, hTime]
    field_simp [huTime, hGamma, hBoostDenominator]
  have hInitialX :
      velocityComponentFractionOfC u .x =
        (3 / 5 : ℝ) * Real.Angle.cos (degrees 45) := by
    simpa [u, hData.rocketSpeedMeasuredByOIsPointSix,
      hData.rocketDirectionMeasuredByOIsFortyFiveDegrees] using
      hGeometry.xComponentFromSpeedAndAngle
  have hInitialY :
      velocityComponentFractionOfC u .y =
        (3 / 5 : ℝ) * Real.Angle.sin (degrees 45) := by
    simpa [u, hData.rocketSpeedMeasuredByOIsPointSix,
      hData.rocketDirectionMeasuredByOIsFortyFiveDegrees] using
      hGeometry.yComponentFromSpeedAndAngle
  have hAxes : (Finset.univ : Finset PlanarAxis) = {.x, .y} := by
    decide
  simp only [speedFractionOfC, hAxes,
    Finset.sum_pair (by decide : PlanarAxis.x ≠ .y)]
  rw [hX, hY, hInitialX, hInitialY]
  simp only [β, hData.observerOPrimeSpeedMeasuredByOIsPointEight]
  rfl

/-!
The exact transformed speed is approximately `0.687 c`, so it rounds to
`0.69 c` and uniquely selects choice B. The displayed `0.69 c` is not
asserted as an exact physical equality.

This formalizes `thm:physics:phyx_mini_0565:target`.
-/
theorem problem_phyx_mini_0565
    (setup : ObliqueRocketBoostSetup)
    (hScenario : MatchesObliqueRocketScenario setup)
    (hData : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedTwoRocketFigure setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hGeometry : SatisfiesPlanarVelocityGeometry setup)
    (hRelativity : SatisfiesLorentzBoostVelocityLaw setup
      hPhysical.observerFrameSpeedIsSubluminal) :
    speedFractionOfC
        (setup.rocketFourVelocityMeasuredIn .observerOPrime) =
        expectedRocketSpeedFractionInOPrime ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hExact := rocket_speed_fraction_in_OPrime_exact
    setup hData hPhysical hGeometry hRelativity
  constructor
  · exact hExact
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := by
    norm_num
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2_lower : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hsqrt2_upper : Real.sqrt 2 < (99 / 70 : ℝ) := by
    nlinarith
  have hFirstDenominator :
      5 ^ 2 * 2 - 3 * Real.sqrt 2 * 4 ≠ 0 := by
    nlinarith
  have hRadicandDenominator :
      697 - Real.sqrt 2 * 300 ≠ 0 := by
    nlinarith
  have hGamma : LorentzGroup.γ (4 / 5 : ℝ) = 5 / 3 := by
    norm_num [LorentzGroup.γ]
  have hAngle :
      (45 : ℝ) * Real.pi / 180 = Real.pi / 4 := by
    ring
  have hExpectedFormula :
      expectedRocketSpeedFractionInOPrime =
        Real.sqrt
          ((553 - 300 * Real.sqrt 2) /
            (697 - 300 * Real.sqrt 2)) := by
    rw [expectedRocketSpeedFractionInOPrime]
    simp only [degrees, Real.Angle.cos_coe, Real.Angle.sin_coe]
    rw [hAngle, Real.cos_pi_div_four, Real.sin_pi_div_four, hGamma]
    have hRadicand :
        (((3 / 5 : ℝ) * (Real.sqrt 2 / 2) - 4 / 5) /
            (1 - 4 / 5 * ((3 / 5) * (Real.sqrt 2 / 2)))) ^ 2 +
          (((3 / 5 : ℝ) * (Real.sqrt 2 / 2)) /
            ((5 / 3) *
              (1 - 4 / 5 * ((3 / 5) * (Real.sqrt 2 / 2))))) ^ 2 =
          (553 - 300 * Real.sqrt 2) /
            (697 - 300 * Real.sqrt 2) := by
      field_simp [hFirstDenominator, hRadicandDenominator]
      nlinarith
    exact congrArg Real.sqrt hRadicand
  have hDenominatorPositive :
      0 < 697 - 300 * Real.sqrt 2 := by
    nlinarith
  let radicand : ℝ :=
    (553 - 300 * Real.sqrt 2) /
      (697 - 300 * Real.sqrt 2)
  have hRadicandLower :
      (137 / 200 : ℝ) ^ 2 < radicand := by
    dsimp [radicand]
    rw [lt_div_iff₀ hDenominatorPositive]
    nlinarith
  have hRadicandUpper :
      radicand < (139 / 200 : ℝ) ^ 2 := by
    dsimp [radicand]
    rw [div_lt_iff₀ hDenominatorPositive]
    nlinarith
  have hRadicandPositive : 0 < radicand := by
    nlinarith [sq_nonneg (137 / 200 : ℝ)]
  have hSqrtSq : (Real.sqrt radicand) ^ 2 = radicand :=
    Real.sq_sqrt (le_of_lt hRadicandPositive)
  have hSqrtNonnegative : 0 ≤ Real.sqrt radicand :=
    Real.sqrt_nonneg radicand
  have hExpectedBounds :
      (137 / 200 : ℝ) < expectedRocketSpeedFractionInOPrime ∧
        expectedRocketSpeedFractionInOPrime < (139 / 200 : ℝ) := by
    rw [hExpectedFormula]
    change (137 / 200 : ℝ) < Real.sqrt radicand ∧
      Real.sqrt radicand < (139 / 200 : ℝ)
    constructor <;> nlinarith
  unfold IsUniqueMatchingAnswerChoice
  constructor
  · unfold MatchesAnswerChoice RoundsToNearestHundredth
    rw [hExact]
    change
      |expectedRocketSpeedFractionInOPrime - 69 / 100| < (1 / 200 : ℝ)
    rw [abs_lt]
    constructor <;> linarith [hExpectedBounds.1, hExpectedBounds.2]
  · intro other hOther
    cases other with
    | A =>
        unfold MatchesAnswerChoice RoundsToNearestHundredth at hOther
        rw [hExact] at hOther
        change
          |expectedRocketSpeedFractionInOPrime - 11 / 20| <
            (1 / 200 : ℝ) at hOther
        rw [abs_lt] at hOther
        linarith [hExpectedBounds.1]
    | B =>
        rfl
    | C =>
        unfold MatchesAnswerChoice RoundsToNearestHundredth at hOther
        rw [hExact] at hOther
        change
          |expectedRocketSpeedFractionInOPrime - 19 / 20| <
            (1 / 200 : ℝ) at hOther
        rw [abs_lt] at hOther
        linarith [hExpectedBounds.2]
    | D =>
        unfold MatchesAnswerChoice RoundsToNearestHundredth at hOther
        rw [hExact] at hOther
        change
          |expectedRocketSpeedFractionInOPrime - 51 / 5| <
            (1 / 200 : ℝ) at hOther
        rw [abs_lt] at hOther
        linarith [hExpectedBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0565
