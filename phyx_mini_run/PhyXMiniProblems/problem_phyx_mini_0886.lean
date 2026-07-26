import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0886

open Dimension

/-!
# Instantaneous EMF from a phasor diagram

The primary image shows a phasor of magnitude `12 V` at `t = 15 ms`.  Its
arrow lies in the second quadrant, at an acute angle of `30°` above the
negative horizontal axis.  With the cosine-reference convention, the
instantaneous EMF is the horizontal projection of this arrow.

EMF and time are represented by Physlib's unit-independent `Dimensionful`
quantities.  Real numbers occur only as coherent-SI readouts, dimensionless
angle representatives in radians, or displayed multiple-choice values.

Assumption/target split:

* governing law: instantaneous EMF is the cosine projection of the peak-EMF
  phasor at every time;
* previous-part results: none;
* figure/data readouts: the arrow starts at the origin, lies in quadrant II,
  has magnitude `12 V`, is displayed at `15 ms`, and is `30°` above the
  negative horizontal axis;
* current target: the exact instantaneous EMF is `-6 * sqrt 3 V`, whose
  unique nearest displayed choice is C, `-10 V`.

No setup field or premise states either target conclusion.
-/

/-! ## Dimensionful quantities and named readouts -/

/-- The physical dimension `M L² T⁻² C⁻¹` shared by EMF and voltage. -/
def emfDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent peak EMF magnitude. -/
abbrev EmfMagnitudeQuantity : Type :=
  Dimensionful (WithDim emfDimension NNReal)

/-- A signed, unit-independent instantaneous EMF. -/
abbrev SignedEmfQuantity : Type :=
  Dimensionful (WithDim emfDimension ℝ)

/-- A nonnegative, unit-independent time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Coherent-SI readout of a peak EMF magnitude in volts. -/
def emfMagnitudeInVolts (emf : EmfMagnitudeQuantity) : ℝ :=
  ((emf UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed instantaneous EMF in volts. -/
def signedEmfInVolts (emf : SignedEmfQuantity) : ℝ :=
  (emf UnitChoices.SI).val

/-- Millisecond readout used by the time label in the supplied image. -/
def timeInMilliseconds (time : TimeQuantity) : ℝ :=
  1000 * ((time UnitChoices.SI).val : ℝ)

/-! ## Figure labels and independent physical setup -/

/-- The four open quadrants determined by the two axes in the phasor image. -/
inductive CartesianQuadrant where
  | first
  | second
  | third
  | fourth
  deriving DecidableEq, Repr

/-- Literal presentation data transcribed from image `886.png`. -/
structure EmfPhasorFigure where
  horizontalAxisShown : Bool
  verticalAxisShown : Bool
  phasorArrowShown : Bool
  arrowStartsAtOrigin : Bool
  arrowQuadrant : CartesianQuadrant
  peakMagnitudeLabelVolts : ℝ
  observationTimeLabelMilliseconds : ℝ
  acuteAngleAboveNegativeXAxisRadians : ℝ

/-!
Independent physical quantities and observables for the phasor experiment.
In particular, `instantaneousEmf` is not defined from the phasor projection,
the recorded answer, or any displayed numerical choice.
-/
structure EmfPhasorSetup where
  figure : EmfPhasorFigure
  peakMagnitude : EmfMagnitudeQuantity
  observationTime : TimeQuantity
  phaseAt : TimeQuantity → Real.Angle
  instantaneousEmf : TimeQuantity → SignedEmfQuantity

/-!
Primary-image evidence.  The raster places the marked `30°` between the arrow
and the negative horizontal ray, despite the auxiliary caption's wording
about the positive horizontal axis.  The final field converts that pictorial
relation into the cosine-reference phase at the displayed time.
-/
structure MatchesSuppliedEmfPhasorFigure
    (setup : EmfPhasorSetup) : Prop where
  horizontalAxisIsShown : setup.figure.horizontalAxisShown = true
  verticalAxisIsShown : setup.figure.verticalAxisShown = true
  phasorArrowIsShown : setup.figure.phasorArrowShown = true
  arrowOrigin : setup.figure.arrowStartsAtOrigin = true
  arrowLiesInSecondQuadrant : setup.figure.arrowQuadrant = .second
  printedPeakMagnitude : setup.figure.peakMagnitudeLabelVolts = 12
  physicalPeakMatchesLabel :
    emfMagnitudeInVolts setup.peakMagnitude =
      setup.figure.peakMagnitudeLabelVolts
  printedObservationTime :
    setup.figure.observationTimeLabelMilliseconds = 15
  physicalTimeMatchesLabel :
    timeInMilliseconds setup.observationTime =
      setup.figure.observationTimeLabelMilliseconds
  printedAcuteAngleIsThirtyDegrees :
    setup.figure.acuteAngleAboveNegativeXAxisRadians = Real.pi / 6
  phaseMatchesSecondQuadrantGeometry :
    setup.phaseAt setup.observationTime =
      (Real.pi : Real.Angle) -
        (setup.figure.acuteAngleAboveNegativeXAxisRadians : Real.Angle)

/-! ## Governing phasor law -/

/-!
For a cosine-reference phasor, the signed instantaneous EMF is its horizontal
projection.  This law is uniform in time and contains neither the evaluated
value `-6 * sqrt 3` nor a displayed answer choice.
-/
structure SatisfiesCosineReferencePhasorLaw
    (setup : EmfPhasorSetup) : Prop where
  instantaneousEmfIsHorizontalProjection : ∀ time,
    signedEmfInVolts (setup.instantaneousEmf time) =
      emfMagnitudeInVolts setup.peakMagnitude *
        Real.Angle.cos (setup.phaseAt time)

/-! ## Displayed choices and conclusions -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Voltage value printed beside each displayed answer label. -/
def AnswerChoice.emfInVolts : AnswerChoice → ℝ
  | .A => -6
  | .B => -8
  | .C => -10
  | .D => -5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A displayed choice is uniquely nearest to a computed scalar readout when it
has strictly smaller absolute error than every differently labelled choice.
This generic definition does not select C or prescribe the physical EMF.
-/
def IsUniqueNearestDisplayedChoice
    (computedVolts : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |computedVolts - choice.emfInVolts| <
      |computedVolts - other.emfInVolts|

/-!
The second-quadrant geometry makes the phase at the labelled time `5π/6`
modulo a full turn.
-/
lemma phaseAtObservationTime_eq_five_pi_div_six
    (setup : EmfPhasorSetup)
    (_figure : MatchesSuppliedEmfPhasorFigure setup) :
    setup.phaseAt setup.observationTime =
      ((5 * Real.pi / 6 : ℝ) : Real.Angle) := by
  rw [_figure.phaseMatchesSecondQuadrantGeometry,
    _figure.printedAcuteAngleIsThirtyDegrees]
  rw [← Real.Angle.coe_sub]
  congr 1
  ring

/-!
The exact horizontal projection is
`12 cos(5π/6) = -6 sqrt(3) V`.  Of the four integer-valued displayed choices,
`-10 V` (choice C) is uniquely nearest to this exact value.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0886:target`.
-/
theorem problem_phyx_mini_0886
    (setup : EmfPhasorSetup)
    (_figure : MatchesSuppliedEmfPhasorFigure setup)
    (_law : SatisfiesCosineReferencePhasorLaw setup) :
    signedEmfInVolts
          (setup.instantaneousEmf setup.observationTime) =
        -6 * Real.sqrt 3 ∧
      IsUniqueNearestDisplayedChoice
        (signedEmfInVolts
          (setup.instantaneousEmf setup.observationTime))
        recordedDatasetAnswer := by
  have hvalue :
      signedEmfInVolts (setup.instantaneousEmf setup.observationTime) =
        -6 * Real.sqrt 3 := by
    rw [_law.instantaneousEmfIsHorizontalProjection,
      _figure.physicalPeakMatchesLabel, _figure.printedPeakMagnitude,
      phaseAtObservationTime_eq_five_pi_div_six setup _figure,
      Real.Angle.cos_coe]
    rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_six]
    ring
  refine ⟨hvalue, ?_⟩
  rw [hvalue]
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hten : 10 < 6 * Real.sqrt 3 := by
    nlinarith
  intro other hother
  cases other with
  | A =>
      norm_num [recordedDatasetAnswer, AnswerChoice.emfInVolts]
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      linarith
  | B =>
      norm_num [recordedDatasetAnswer, AnswerChoice.emfInVolts]
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      linarith
  | C => exact (hother rfl).elim
  | D =>
      norm_num [recordedDatasetAnswer, AnswerChoice.emfInVolts]
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0886
