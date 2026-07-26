import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0608

open Dimension

/-!
# Lorentz contraction of the Denebian Empire's elliptical marking

The Empire marking is an ellipse whose proper major-axis length `a` is
`1.40` times its proper minor-axis length `b`.  The ship moves parallel to
the major axis, so an observer sees that axis Lorentz-contracted while the
transverse minor axis is unchanged.  The marking is mistaken for the
Federation's circular marking exactly when those two observed axis lengths
are equal.

Lengths and speed magnitudes are unit-independent Physlib quantities.  Real
numbers are used only for unit readouts, the dimensionless ratio `v / c`, the
dimensionless axis ratio, and displayed answer values.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A nonnegative physical length, independent of a choice of units. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, dimensionful speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Scenario, frame, and primary-figure vocabulary -/

/-- The two organizations identified by captions in the supplied image. -/
inductive StarshipAffiliation where
  | federation
  | empire
  deriving DecidableEq, Fintype, Repr

/-- The two sides occupied by the ships in the supplied image. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Geometric kinds of the two affiliation markings. -/
inductive MarkingShape where
  | circle
  | ellipse
  deriving DecidableEq, Repr

/-- The two axis labels printed next to the Empire ellipse. -/
inductive FigureAxisLabel where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- Orientation of a labelled axis in the supplied raster. -/
inductive FigureOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Physical role assigned to each labelled ellipse axis. -/
inductive EllipseAxisRole where
  | major
  | minor
  deriving DecidableEq, Fintype, Repr

/-- The ship rest frame and the inertial frame of the observing viewer. -/
inductive InertialFrameLabel where
  | empireShipRest
  | observer
  deriving DecidableEq, Repr

/-!
Typed transcription of the primary image.  It records the left/right
affiliations, the circle/ellipse distinction, and the `a` and `b` labels and
orientations.  The prose-supplied numerical ratio is kept out of this image
record because it is not printed in the raster itself.
-/
structure StarshipMarkingFigure where
  affiliationAt : FigureSide → StarshipAffiliation
  markingShape : StarshipAffiliation → MarkingShape
  labelForAxis : EllipseAxisRole → FigureAxisLabel
  orientationOfLabel : FigureAxisLabel → FigureOrientation
  federationCaptionShown : Bool
  empireCaptionShown : Bool

/-!
Independent physical quantities in the observation.  The observed axis
lengths and relative speed are fields rather than definitions from the
contraction law or an answer choice.
-/
structure EmpireMarkingObservation where
  figure : StarshipMarkingFigure
  movingShipAffiliation : StarshipAffiliation
  markingToImitate : StarshipAffiliation
  properMeasurementFrame : InertialFrameLabel
  observedMeasurementFrame : InertialFrameLabel
  motionParallelTo : EllipseAxisRole
  properMajorAxisA : LengthQuantity
  properMinorAxisB : LengthQuantity
  observedLongitudinalAxis : LengthQuantity
  observedTransverseAxis : LengthQuantity
  relativeSpeed : SpeedQuantity
  statedMajorToMinorRatio : ℝ

/-- The dimensionless relative speed `β = v / c`, evaluated in SI units. -/
def speedFractionOfLight (setup : EmpireMarkingObservation) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- Physlib's Lorentz factor for the observation's dimensionless speed. -/
def lorentzFactor (setup : EmpireMarkingObservation) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Assumptions: scenario, data readouts, and governing physics -/

/-- Frame, affiliation, and motion-axis roles stated or required by the setup. -/
structure MatchesEmpireMarkingScenario
    (setup : EmpireMarkingObservation) : Prop where
  movingShipIsEmpire : setup.movingShipAffiliation = .empire
  imitatesFederationMarking : setup.markingToImitate = .federation
  properLengthsMeasuredInShipFrame :
    setup.properMeasurementFrame = .empireShipRest
  contractedLengthsMeasuredByObserver :
    setup.observedMeasurementFrame = .observer
  motionIsParallelToMajorAxis : setup.motionParallelTo = .major

/-- Qualitative geometry and literal labels visible in `test_image/608.png`. -/
structure MatchesSuppliedStarshipFigure
    (figure : StarshipMarkingFigure) : Prop where
  federationIsOnLeft :
    figure.affiliationAt .left = .federation
  empireIsOnRight :
    figure.affiliationAt .right = .empire
  federationMarkingIsCircle :
    figure.markingShape .federation = .circle
  empireMarkingIsEllipse :
    figure.markingShape .empire = .ellipse
  majorAxisCarriesA : figure.labelForAxis .major = .a
  minorAxisCarriesB : figure.labelForAxis .minor = .b
  axisAIsVertical : figure.orientationOfLabel .a = .vertical
  axisBIsHorizontal : figure.orientationOfLabel .b = .horizontal
  federationCaptionVisible : figure.federationCaptionShown = true
  empireCaptionVisible : figure.empireCaptionShown = true

/-!
The dimensionless `a = 1.40 b` datum from the prose, linked to the two
dimensionful proper axis lengths in every common length unit.
-/
structure MatchesProblemEllipseRatio
    (setup : EmpireMarkingObservation) : Prop where
  statedRatioIsOnePointFour :
    setup.statedMajorToMinorRatio = (7 / 5 : ℝ)
  properAxesHaveStatedRatio : ∀ unit : LengthUnit,
    lengthReadout unit setup.properMajorAxisA =
      setup.statedMajorToMinorRatio *
        lengthReadout unit setup.properMinorAxisB

/-! Positivity and the nonzero subluminal branch relevant to the question. -/
structure HasPhysicalEmpireMarkingParameters
    (setup : EmpireMarkingObservation) : Prop where
  positiveProperMajorAxis : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.properMajorAxisA
  positiveProperMinorAxis : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.properMinorAxisB
  positiveObservedLongitudinalAxis : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.observedLongitudinalAxis
  positiveObservedTransverseAxis : ∀ unit : LengthUnit,
    0 < lengthReadout unit setup.observedTransverseAxis
  positiveRelativeSpeed : 0 < speedFractionOfLight setup
  subluminalRelativeSpeed : speedFractionOfLight setup < 1
  positiveVacuumLightSpeed : 0 < vacuumSpeedOfLightInMetersPerSecond

/-!
The requested observational condition: the moving ellipse has equal apparent
axis lengths and can therefore be confused with the Federation circle.  This
does not supply the speed needed to produce that appearance.
-/
structure AppearsAsFederationCircle
    (setup : EmpireMarkingObservation) : Prop where
  observedAxesAreEqual : ∀ unit : LengthUnit,
    lengthReadout unit setup.observedLongitudinalAxis =
      lengthReadout unit setup.observedTransverseAxis

/-!
The generic special-relativistic length law.  The axis parallel to the motion
contracts by `1 / γ(β)` and the perpendicular axis is unchanged.  Neither
clause specializes `β` to this problem's numerical result.
-/
structure SatisfiesRelativisticAxisContraction
    (setup : EmpireMarkingObservation) : Prop where
  longitudinalAxisContracts : ∀ unit : LengthUnit,
    lengthReadout unit setup.observedLongitudinalAxis =
      lengthReadout unit setup.properMajorAxisA / lorentzFactor setup
  transverseAxisIsInvariant : ∀ unit : LengthUnit,
    lengthReadout unit setup.observedTransverseAxis =
      lengthReadout unit setup.properMinorAxisB

/-! ## Multiple-choice target -/

/-- Labels of the four speed choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed speed in metres per second for each answer choice. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 210000000
  | .B => 21200000
  | .C => 2130000
  | .D => 2110000000

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
Agreement with a speed displayed as `2.10 × 10⁸ m/s`.  The tolerance of
`5 × 10⁵ m/s` is half one unit in the final displayed digit, so this
predicate expresses rounding to three significant figures.
-/
def MatchesDisplayedSpeedChoice
    (setup : EmpireMarkingObservation) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond setup.relativeSpeed -
      displayedSpeedInMetersPerSecond choice| ≤ 500000

/-!
Equal apparent axes force `γ = 7/5`, hence
`β = sqrt (1 - (5/7)²) = sqrt (24/49)`.  With Physlib's exact SI speed
of light, this rounds to `2.10 × 10⁸ m/s`, answer A.

This formalizes `thm:physics:phyx_mini_0608:target`.
-/
theorem problem_phyx_mini_0608
    (setup : EmpireMarkingObservation)
    (h_scenario : MatchesEmpireMarkingScenario setup)
    (h_figure : MatchesSuppliedStarshipFigure setup.figure)
    (h_ratio : MatchesProblemEllipseRatio setup)
    (h_physical : HasPhysicalEmpireMarkingParameters setup)
    (h_circle : AppearsAsFederationCircle setup)
    (h_contraction : SatisfiesRelativisticAxisContraction setup) :
    speedFractionOfLight setup = Real.sqrt (24 / 49 : ℝ) ∧
      MatchesDisplayedSpeedChoice setup .A := by
  let β := speedFractionOfLight setup
  have hβ_pos : 0 < β := h_physical.positiveRelativeSpeed
  have hβ_lt_one : β < 1 := h_physical.subluminalRelativeSpeed
  have hβ_abs : |β| < 1 := by
    rw [abs_of_pos hβ_pos]
    exact hβ_lt_one
  have h_one_sub_sq_pos : 0 < 1 - β ^ 2 := by
    nlinarith
  have hγ_pos : 0 < lorentzFactor setup := by
    rw [lorentzFactor, LorentzGroup.γ]
    exact one_div_pos.mpr (Real.sqrt_pos.2 h_one_sub_sq_pos)

  let unit : LengthUnit := UnitChoices.SI.length
  let a := lengthReadout unit setup.properMajorAxisA
  let b := lengthReadout unit setup.properMinorAxisB
  have hb_pos : 0 < b := h_physical.positiveProperMinorAxis unit
  have hab : a = (7 / 5 : ℝ) * b := by
    calc
      a = setup.statedMajorToMinorRatio * b :=
        h_ratio.properAxesHaveStatedRatio unit
      _ = (7 / 5 : ℝ) * b := by rw [h_ratio.statedRatioIsOnePointFour]
  have hcontracted : a / lorentzFactor setup = b := by
    calc
      a / lorentzFactor setup =
          lengthReadout unit setup.observedLongitudinalAxis :=
        (h_contraction.longitudinalAxisContracts unit).symm
      _ = lengthReadout unit setup.observedTransverseAxis :=
        h_circle.observedAxesAreEqual unit
      _ = b := h_contraction.transverseAxisIsInvariant unit
  have hγ : lorentzFactor setup = (7 / 5 : ℝ) := by
    have hmul :
        a = b * lorentzFactor setup :=
      (div_eq_iff (ne_of_gt hγ_pos)).mp hcontracted
    rw [hab] at hmul
    nlinarith

  have hγ_sq :
      (lorentzFactor setup) ^ 2 = 1 / (1 - β ^ 2) := by
    simpa [lorentzFactor] using LorentzGroup.γ_sq β hβ_abs
  have hβ_sq : β ^ 2 = (24 / 49 : ℝ) := by
    rw [hγ] at hγ_sq
    field_simp [ne_of_gt h_one_sub_sq_pos] at hγ_sq
    nlinarith
  have hsqrt_sq :
      (Real.sqrt (24 / 49 : ℝ)) ^ 2 = (24 / 49 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hβ :
      speedFractionOfLight setup = Real.sqrt (24 / 49 : ℝ) := by
    change β = Real.sqrt (24 / 49 : ℝ)
    nlinarith [Real.sqrt_nonneg (24 / 49 : ℝ)]

  refine ⟨hβ, ?_⟩
  have hc : vacuumSpeedOfLightInMetersPerSecond = 299792458 := by
    norm_num [vacuumSpeedOfLightInMetersPerSecond,
      DimSpeed.speedOfLight_in_SI]
  have hspeed :
      speedInMetersPerSecond setup.relativeSpeed =
        299792458 * Real.sqrt (24 / 49 : ℝ) := by
    rw [speedFractionOfLight, hc] at hβ
    field_simp at hβ
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (24 / 49 : ℝ) :=
    Real.sqrt_nonneg _
  have hsqrt_lower :
      (699 / 1000 : ℝ) ≤ Real.sqrt (24 / 49 : ℝ) := by
    by_contra h
    have hlt :
        Real.sqrt (24 / 49 : ℝ) < (699 / 1000 : ℝ) :=
      lt_of_not_ge h
    have hsum_pos :
        0 < (699 / 1000 : ℝ) + Real.sqrt (24 / 49 : ℝ) := by
      positivity
    have hprod :=
      mul_pos (sub_pos.mpr hlt) hsum_pos
    nlinarith
  have hsqrt_upper :
      Real.sqrt (24 / 49 : ℝ) ≤ (7 / 10 : ℝ) := by
    by_contra h
    have hlt :
        (7 / 10 : ℝ) < Real.sqrt (24 / 49 : ℝ) :=
      lt_of_not_ge h
    have hsum_pos :
        0 < Real.sqrt (24 / 49 : ℝ) + (7 / 10 : ℝ) := by
      positivity
    have hprod :=
      mul_pos (sub_pos.mpr hlt) hsum_pos
    nlinarith
  rw [MatchesDisplayedSpeedChoice, displayedSpeedInMetersPerSecond, hspeed]
  rw [abs_le]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0608
