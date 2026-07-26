import Mathlib.Analysis.Real.Sqrt
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0592

open Dimension

/-!
# Spatial-separation graph under a Lorentz transformation

The primary figure plots the separation `Δx`, measured in inertial frame
`S`, against the primed-frame time interval `Δt'`.  Its horizontal axis is
in nanoseconds and its vertical axis is in metres.  The vertical scale is
labelled `Δxₐ = 10.0 m`; the plotted straight line runs from `2 m` at
`Δt' = 0 ns` to `9 m` at the right boundary `Δt' = 10 ns`.

For a boost in the positive spatial direction, the inverse spatial Lorentz
transformation is

`Δx = γ(β) (Δx' + v Δt')`.

Thus the displayed intercept is `γ Δx'` and the displayed slope is `γ v`.
The target below asks for the independent primed-frame separation `Δx'`; it
is not fixed by any scenario, figure, or governing-law premise.

The assigned file did not exist at task start, so there were no
`/- USER: ... -/` hints to incorporate.
-/

/-! ## Dimensionful quantities and named unit readouts -/

/-- A signed, unit-independent physical spatial separation. -/
abbrev SpatialSeparation : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed, unit-independent physical time interval. -/
abbrev TimeInterval : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative, unit-independent relative-speed magnitude. -/
abbrev SpeedMagnitude : Type := DimSpeed

/-- Coherent units with metres for length and nanoseconds for time. -/
def meterNanosecondUnits : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.nanoseconds }

/-- Read a signed spatial separation in metres. -/
def separationInMeters (separation : SpatialSeparation) : ℝ :=
  (separation UnitChoices.SI).val

/-- Read a signed time interval in nanoseconds. -/
def timeIntervalInNanoseconds (time : TimeInterval) : ℝ :=
  (time meterNanosecondUnits).val

/-- Read a speed magnitude in metres per nanosecond. -/
def speedInMetersPerNanosecond (speed : SpeedMagnitude) : ℝ :=
  ((speed meterNanosecondUnits).val : ℝ)

/-- Physlib's exact vacuum light speed, read in metres per nanosecond. -/
def vacuumLightSpeedInMetersPerNanosecond : ℝ :=
  ((DimSpeed.speedOfLight meterNanosecondUnits).val : ℝ)

/-- The dimensionful time interval having the specified nanosecond readout. -/
noncomputable def timeIntervalOfNanoseconds (value : ℝ) : TimeInterval :=
  CarriesDimension.toDimensionful meterNanosecondUnits ⟨value⟩

/-! ## Frames, graph labels, and primary-figure vocabulary -/

/-- The unprimed observer frame and the relatively moving primed frame. -/
inductive InertialFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Repr

/-- Direction along the common one-dimensional spatial axis. -/
inductive AxialDirection where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The two coordinate axes in the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Literal physical labels attached to the two graph axes. -/
inductive GraphAxisLabel where
  | deltaTPrimeNanoseconds
  | deltaXMeters
  deriving DecidableEq, Repr

/-- The separate scale marker printed at the top of the vertical axis. -/
inductive VerticalScaleLabel where
  | deltaXa
  deriving DecidableEq, Repr

/-- The qualitative shape of the heavy plotted curve. -/
inductive PlottedCurveShape where
  | straightLine
  deriving DecidableEq, Repr

/-!
Semantic transcription of the graph.  The scalar fields are named coordinate
readouts from the bitmap; the vertical scale itself remains a dimensionful
length.
-/
structure SeparationTimeGraphFigure where
  axisLabel : GraphAxis → GraphAxisLabel
  verticalScaleLabel : VerticalScaleLabel
  horizontalTickNanoseconds : Fin 3 → ℝ
  verticalScaleDeltaXa : SpatialSeparation
  curveShape : PlottedCurveShape
  rightBoundaryNanoseconds : ℝ
  lineInterceptMeters : ℝ
  lineAtRightBoundaryMeters : ℝ

/-- Slope of the displayed straight line, in metres per nanosecond. -/
def displayedLineSlopeMetersPerNanosecond
    (figure : SeparationTimeGraphFigure) : ℝ :=
  (figure.lineAtRightBoundaryMeters - figure.lineInterceptMeters) /
    figure.rightBoundaryNanoseconds

/-!
Independent physical quantities in the relativity experiment.

`deltaXPrime` is the unknown primed-frame spatial separation.
`deltaXAccordingToS` is the family of unprimed-frame separations whose
metre readouts are plotted as the primed time interval varies.
-/
structure RelativisticSeparationSetup where
  figure : SeparationTimeGraphFigure
  observerFrame : InertialFrameLabel
  primedFrame : InertialFrameLabel
  primedFrameMotionDirection : AxialDirection
  relativeSpeed : SpeedMagnitude
  deltaXPrime : SpatialSeparation
  deltaXAccordingToS : TimeInterval → SpatialSeparation

/-- Dimensionless relative speed `β = v/c`. -/
def speedFractionOfLight (setup : RelativisticSeparationSetup) : ℝ :=
  speedInMetersPerNanosecond setup.relativeSpeed /
    vacuumLightSpeedInMetersPerNanosecond

/-- Physlib's Lorentz factor for the relative speed. -/
def lorentzFactor (setup : RelativisticSeparationSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Scenario and primary-figure readouts -/

/-- Frame roles and boost direction stated or implied by the problem. -/
structure MatchesRelativisticSeparationScenario
    (setup : RelativisticSeparationSetup) : Prop where
  unprimedObserverUsesS : setup.observerFrame = .S
  movingFrameIsPrimed : setup.primedFrame = .SPrime
  primedFrameMovesTowardPositiveAxis :
    setup.primedFrameMotionDirection = .positive

/-!
Direct transcription of `592.png`.  The bitmap, rather than its auxiliary
caption, determines the nonzero `2 m` intercept and the `9 m` value at the
`10 ns` right boundary.  The last field states only that the physical graph
follows that displayed affine line; it does not mention `Δx'`.
-/
structure MatchesSuppliedSeparationTimeGraph
    (setup : RelativisticSeparationSetup) : Prop where
  horizontalAxisIsDeltaTPrime :
    setup.figure.axisLabel .horizontal = .deltaTPrimeNanoseconds
  verticalAxisIsDeltaX :
    setup.figure.axisLabel .vertical = .deltaXMeters
  scaleMarkerIsDeltaXa : setup.figure.verticalScaleLabel = .deltaXa
  firstHorizontalTick : setup.figure.horizontalTickNanoseconds 0 = 0
  secondHorizontalTick : setup.figure.horizontalTickNanoseconds 1 = 4
  thirdHorizontalTick : setup.figure.horizontalTickNanoseconds 2 = 8
  verticalScaleIsTenMeters :
    separationInMeters setup.figure.verticalScaleDeltaXa = 10
  plottedCurveIsStraight : setup.figure.curveShape = .straightLine
  rightBoundaryIsTenNanoseconds :
    setup.figure.rightBoundaryNanoseconds = 10
  lineInterceptIsTwoMeters : setup.figure.lineInterceptMeters = 2
  lineAtRightBoundaryIsNineMeters :
    setup.figure.lineAtRightBoundaryMeters = 9
  physicalGraphFollowsDisplayedLine : ∀ timeNanoseconds : ℝ,
    separationInMeters
        (setup.deltaXAccordingToS
          (timeIntervalOfNanoseconds timeNanoseconds)) =
      setup.figure.lineInterceptMeters +
        displayedLineSlopeMetersPerNanosecond setup.figure *
          timeNanoseconds

/-! ## Governing relativistic physics -/

/--
The positivity and subluminality regime required for the Lorentz model.
These conditions constrain the physical branch but supply no numerical value
for the requested primed separation.
-/
structure HasPhysicalRelativisticParameters
    (setup : RelativisticSeparationSetup) : Prop where
  positivePrimedSeparation :
    0 < separationInMeters setup.deltaXPrime
  positiveVacuumLightSpeed :
    0 < vacuumLightSpeedInMetersPerNanosecond
  nonnegativeSpeedFraction : 0 ≤ speedFractionOfLight setup
  subluminalSpeedFraction : speedFractionOfLight setup < 1

/-!
Generic inverse spatial Lorentz transformation
`Δx = γ(β) (Δx' + v Δt')`, expressed in the coherent metre/nanosecond unit
system used by the graph.  It relates independent fields of the setup and
contains neither the requested numerical answer nor any answer-choice label.
-/
structure SatisfiesInverseLorentzSpatialTransformation
    (setup : RelativisticSeparationSetup) : Prop where
  inverseSpatialTransformation : ∀ deltaTPrime : TimeInterval,
    separationInMeters (setup.deltaXAccordingToS deltaTPrime) =
      lorentzFactor setup *
        (separationInMeters setup.deltaXPrime +
          speedInMetersPerNanosecond setup.relativeSpeed *
            timeIntervalInNanoseconds deltaTPrime)

/-! ## Displayed answers and formalization target -/

/-- Labels of the four metre-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical separation printed beside each answer-choice label, in metres. -/
def displayedSeparationInMeters : AnswerChoice → ℝ
  | .A => 2
  | .B => 13 / 10
  | .C => 79 / 100
  | .D => 3

/--
Half of one unit in the last printed decimal place for each displayed answer.
-/
def displayedHalfUnitInLastPlaceMeters : AnswerChoice → ℝ
  | .A => 1 / 20
  | .B => 1 / 20
  | .C => 1 / 200
  | .D => 1 / 20

/-- A physical separation agrees with an answer at its displayed precision. -/
def MatchesDisplayedPrecision
    (separation : SpatialSeparation) (choice : AnswerChoice) : Prop :=
  |separationInMeters separation - displayedSeparationInMeters choice| ≤
    displayedHalfUnitInLastPlaceMeters choice

/-- The selected choice is at least as close as every displayed alternative. -/
def IsNearestAnswerChoice
    (separation : SpatialSeparation) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |separationInMeters separation - displayedSeparationInMeters choice| ≤
      |separationInMeters separation -
        displayedSeparationInMeters alternative|

/-!
Blueprint label: `thm:physics:phyx_mini_0592:target`.

The line has intercept `2 m` and slope `7/10 m/ns`.  Since those are
`γ Δx'` and `γ v`, eliminating the subluminal boost speed gives the exact
metre readout shown below.  Using Physlib's exact light speed, this is about
`0.787378 m`, which rounds to `0.79 m` and makes answer C the nearest
displayed choice.
-/
theorem primedSeparation_matches_choice_C
    (setup : RelativisticSeparationSetup)
    (_scenario : MatchesRelativisticSeparationScenario setup)
    (_figure : MatchesSuppliedSeparationTimeGraph setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_lorentz : SatisfiesInverseLorentzSpatialTransformation setup) :
    separationInMeters setup.deltaXPrime =
        2 * vacuumLightSpeedInMetersPerNanosecond /
          Real.sqrt
            (vacuumLightSpeedInMetersPerNanosecond ^ 2 +
              (7 / 10 : ℝ) ^ 2) ∧
      MatchesDisplayedPrecision setup.deltaXPrime .C ∧
      IsNearestAnswerChoice setup.deltaXPrime .C := by
  have htime (value : ℝ) :
      timeIntervalInNanoseconds (timeIntervalOfNanoseconds value) = value := by
    simp [timeIntervalInNanoseconds, timeIntervalOfNanoseconds,
      CarriesDimension.toDimensionful_apply_apply]
  have hgraph0 := _figure.physicalGraphFollowsDisplayedLine 0
  have hgraph10 := _figure.physicalGraphFollowsDisplayedLine 10
  rw [displayedLineSlopeMetersPerNanosecond,
    _figure.lineInterceptIsTwoMeters,
    _figure.lineAtRightBoundaryIsNineMeters,
    _figure.rightBoundaryIsTenNanoseconds] at hgraph0 hgraph10
  norm_num at hgraph0 hgraph10
  have hlorentz0 :=
    _lorentz.inverseSpatialTransformation (timeIntervalOfNanoseconds 0)
  have hlorentz10 :=
    _lorentz.inverseSpatialTransformation (timeIntervalOfNanoseconds 10)
  rw [htime 0] at hlorentz0
  rw [htime 10] at hlorentz10
  let x : ℝ := separationInMeters setup.deltaXPrime
  let v : ℝ := speedInMetersPerNanosecond setup.relativeSpeed
  let c : ℝ := vacuumLightSpeedInMetersPerNanosecond
  let beta : ℝ := speedFractionOfLight setup
  let gamma : ℝ := lorentzFactor setup
  have hintercept : gamma * x = 2 := by
    dsimp [gamma, x]
    nlinarith only [hgraph0, hlorentz0]
  have hslope : gamma * v = 7 / 10 := by
    dsimp [gamma, v]
    nlinarith only [hgraph0, hgraph10, hlorentz0, hlorentz10]
  have hbeta_nonneg : 0 ≤ beta := _physical.nonnegativeSpeedFraction
  have hbeta_lt_one : beta < 1 := _physical.subluminalSpeedFraction
  have hbeta_abs_lt_one : |beta| < 1 := by
    rw [abs_of_nonneg hbeta_nonneg]
    exact hbeta_lt_one
  have hbeta_sq_lt_one : beta ^ 2 < 1 := by
    nlinarith [sq_nonneg beta, mul_self_lt_mul_self
      (show 0 ≤ beta from hbeta_nonneg) hbeta_lt_one]
  have hdenominator_pos : 0 < 1 - beta ^ 2 := sub_pos.mpr hbeta_sq_lt_one
  have hgamma_sq :
      gamma ^ 2 = 1 / (1 - beta ^ 2) := by
    exact LorentzGroup.γ_sq beta hbeta_abs_lt_one
  have hgamma_identity :
      gamma ^ 2 * (1 - beta ^ 2) = 1 :=
    (eq_div_iff (ne_of_gt hdenominator_pos)).mp hgamma_sq
  have hc_pos : 0 < c := _physical.positiveVacuumLightSpeed
  have hbeta_def : beta = v / c := by
    rfl
  rw [hbeta_def] at hgamma_identity
  field_simp [ne_of_gt hc_pos] at hgamma_identity
  have hgamma_def :
      gamma = 1 / Real.sqrt (1 - beta ^ 2) := by
    rfl
  have hgamma_pos : 0 < gamma := by
    rw [hgamma_def]
    exact one_div_pos.mpr (Real.sqrt_pos.2 hdenominator_pos)
  have hgamma_c_sq :
      (gamma * c) ^ 2 = c ^ 2 + (7 / 10 : ℝ) ^ 2 := by
    calc
      (gamma * c) ^ 2 = gamma ^ 2 * c ^ 2 := by ring
      _ = c ^ 2 + (gamma * v) ^ 2 := by
        nlinarith [hgamma_identity]
      _ = c ^ 2 + (7 / 10 : ℝ) ^ 2 := by rw [hslope]
  have hradicand_pos : 0 < c ^ 2 + (7 / 10 : ℝ) ^ 2 := by
    positivity
  have hgamma_c :
      gamma * c = Real.sqrt (c ^ 2 + (7 / 10 : ℝ) ^ 2) := by
    have hsqrt_sq := Real.sq_sqrt (le_of_lt hradicand_pos)
    have hsqrt_nonneg :=
      Real.sqrt_nonneg (c ^ 2 + (7 / 10 : ℝ) ^ 2)
    nlinarith [mul_pos hgamma_pos hc_pos]
  have hmain :
      x = 2 * c / Real.sqrt (c ^ 2 + (7 / 10 : ℝ) ^ 2) := by
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 hradicand_pos))).mpr
    calc
      x * Real.sqrt (c ^ 2 + (7 / 10 : ℝ) ^ 2) =
          x * (gamma * c) := by rw [hgamma_c]
      _ = c * (gamma * x) := by ring
      _ = c * 2 := by rw [hintercept]
      _ = 2 * c := by ring
  have hc_exact : c = (149896229 : ℝ) / 500000000 := by
    norm_num [c, vacuumLightSpeedInMetersPerNanosecond,
      meterNanosecondUnits, DimSpeed.speedOfLight,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale, UnitChoices.SI, TimeUnit.nanoseconds,
      TimeUnit.scale, TimeUnit.seconds, LengthUnit.meters,
      MassUnit.kilograms, ChargeUnit.coulombs, TemperatureUnit.kelvin,
      TimeUnit.div_eq_val, NNReal.rpow_neg_one, WithDim.smul_val,
      NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
    change (1000000000 : ℝ)⁻¹ * 299792458 =
      (149896229 : ℝ) / 500000000
    norm_num
  have hx_pos : 0 < x := _physical.positivePrimedSeparation
  have hx_equation :
      x ^ 2 * (c ^ 2 + (7 / 10 : ℝ) ^ 2) = 4 * c ^ 2 := by
    rw [← hgamma_c_sq]
    calc
      x ^ 2 * (gamma * c) ^ 2 =
          c ^ 2 * (gamma * x) ^ 2 := by ring
      _ = 4 * c ^ 2 := by rw [hintercept]; ring
  rw [hc_exact] at hx_equation
  norm_num at hx_equation
  have hx_lower : (157 / 200 : ℝ) < x := by
    nlinarith [sq_nonneg (x - 157 / 200)]
  have hx_upper : x < (159 / 200 : ℝ) := by
    nlinarith [sq_nonneg (x - 159 / 200)]
  have herror : |x - 79 / 100| ≤ (1 / 200 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hx_lower, hx_upper]
  constructor
  · simpa [x, c] using hmain
  constructor
  · change |x - 79 / 100| ≤ (1 / 200 : ℝ)
    exact herror
  · change ∀ alternative : AnswerChoice,
      |x - 79 / 100| ≤
        |x - displayedSeparationInMeters alternative|
    intro alternative
    cases alternative with
    | A =>
        change |x - 79 / 100| ≤ |x - 2|
        calc
          |x - 79 / 100| ≤ (1 / 200 : ℝ) := herror
          _ ≤ |x - 2| := by
            rw [abs_of_nonpos (by linarith only [hx_upper])]
            linarith only [hx_upper]
    | B =>
        change |x - 79 / 100| ≤ |x - 13 / 10|
        calc
          |x - 79 / 100| ≤ (1 / 200 : ℝ) := herror
          _ ≤ |x - 13 / 10| := by
            rw [abs_of_nonpos (by linarith only [hx_upper])]
            linarith only [hx_upper]
    | C =>
        exact le_rfl
    | D =>
        change |x - 79 / 100| ≤ |x - 3|
        calc
          |x - 79 / 100| ≤ (1 / 200 : ℝ) := herror
          _ ≤ |x - 3| := by
            rw [abs_of_nonpos (by linarith only [hx_upper])]
            linarith only [hx_upper]

end PhyXMiniProblems.ProblemPhyXMini0592
