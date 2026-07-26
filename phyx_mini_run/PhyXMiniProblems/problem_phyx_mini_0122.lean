import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0122

open Dimension

/-!
# Width of each slit from missing double-slit fringes

The source image shows the central portion of a two-slit interference pattern.
Ideal constructive orders from `-9` through `9` are almost equally spaced at
the scale of the image, but orders `-7` and `7` are absent. Those first missing
interference maxima coincide with the first minima of the single-slit
diffraction envelope.

The prose reports the adjacent-fringe spacing as `1.53 cm`, whereas the image
labels it `1.53 mm`. Because the source directs us to use the image as primary
evidence, both reports are retained as distinct physical quantities and the
optical laws use the image spacing. This is also the interpretation consistent
with the recorded answer `0.148 mm`.

Screen projection is modeled by the exact planar-screen relation
`y = L tan θ`, not by the globalized paraxial replacement `y = L sin θ`.
Consequently the exact width below contains the very small finite-angle
correction `sqrt (1 + (1.53 / 2500)^2)`; its displayed rounding is unchanged.

All distances are dimensionful Physlib quantities. Real numbers occur only as
calibrated unit readouts, order labels, or dimensionless trigonometric values.
-/

/-- A signed, unit-independent physical quantity carrying length dimension. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real number in the selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The SI-metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The centimetre readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The millimetre readout of a physical length. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- The nanometre readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Labels for the two parallel openings. -/
inductive SlitLabel where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- The two sides of the symmetric screen pattern. -/
inductive ScreenSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Whether an ideal constructive order is visible in the cropped image. -/
inductive SpotVisibility where
  | bright
  | missing
  deriving DecidableEq, Repr

/-- Qualitative geometry assigned to the two openings in the experiment. -/
inductive SlitGeometry where
  | twoParallelEqualWidth
  deriving DecidableEq, Repr

/-- Geometry used to project an outgoing direction onto the screen. -/
inductive ScreenGeometry where
  | planarPerpendicular
  deriving DecidableEq, Repr

/-- Which of the inconsistent spacing reports controls the optical model. -/
inductive SpacingEvidencePolicy where
  | figurePrimary
  deriving DecidableEq, Repr

/-!
Physical quantities, order-indexed angles and screen locations, and figure
metadata for the experiment. `screenOffset order` is the signed position of
the ideal constructive maximum of that order, even when diffraction suppresses
the spot. `slitWidth` is an unknown physical length and no field assigns its
requested numerical value.
-/
structure MissingFringeDoubleSlitSetup where
  wavelength : LengthQuantity
  slitWidth : LengthQuantity
  slitSeparation : LengthQuantity
  screenDistance : LengthQuantity
  figureFringeSpacing : LengthQuantity
  proseFringeSpacing : LengthQuantity
  slitCenterCoordinate : SlitLabel → LengthQuantity
  screenOffset : ℤ → LengthQuantity
  interferenceAngle : ℤ → Real.Angle
  firstMinimumAngle : ScreenSide → Real.Angle
  spotVisibility : ℤ → SpotVisibility
  lowestShownOrder : ℤ
  highestShownOrder : ℤ
  spacingMarkerLeftOrder : ℤ
  spacingMarkerRightOrder : ℤ
  slitGeometry : SlitGeometry
  screenGeometry : ScreenGeometry
  spacingEvidence : SpacingEvidencePolicy

/-!
Positive physical lengths and the signs selecting the left and right angular
branches. These conditions do not determine the unknown width.
-/
def HasPhysicalParameters (setup : MissingFringeDoubleSlitSetup) : Prop :=
  0 < lengthInMeters setup.wavelength ∧
    0 < lengthInMeters setup.slitWidth ∧
    0 < lengthInMeters setup.slitSeparation ∧
    0 < lengthInMeters setup.screenDistance ∧
    0 < lengthInMeters setup.figureFringeSpacing ∧
    Real.Angle.sin (setup.interferenceAngle (-7)) < 0 ∧
    0 < Real.Angle.sin (setup.interferenceAngle 7) ∧
    0 < Real.Angle.cos (setup.interferenceAngle (-1)) ∧
    0 < Real.Angle.cos (setup.interferenceAngle 7)

/-!
The openings are interpreted as parallel and equal-width, and the difference
of their transverse center coordinates is their center separation. The common
width remains unconstrained numerically.
-/
def MatchesSlitGeometry (setup : MissingFringeDoubleSlitSetup) : Prop :=
  setup.slitGeometry = .twoParallelEqualWidth ∧
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.slitCenterCoordinate .upper) -
          lengthReadout unit (setup.slitCenterCoordinate .lower) =
        lengthReadout unit setup.slitSeparation

/-!
Problem-text readouts: a helium-neon wavelength of `632.8 nm`, a screen
distance of `2.50 m`, and the prose's adjacent-fringe report of `1.53 cm`.
The prose spacing is retained for provenance but is not the primary spacing
used by the laws.
-/
def MatchesProblemReadouts (setup : MissingFringeDoubleSlitSetup) : Prop :=
  lengthInNanometers setup.wavelength = 632.8 ∧
    lengthInMeters setup.screenDistance = 2.50 ∧
    lengthInCentimeters setup.proseFringeSpacing = 1.53

/-!
Figure readouts and labels. The cropped row represents ideal orders `-9`
through `9`; the spots at `-7` and `7` are missing, all other orders in the
window are bright, and the inward arrows between orders `-1` and `0` label a
center-to-center spacing of `1.53 mm`.
-/
def MatchesFigureReadouts (setup : MissingFringeDoubleSlitSetup) : Prop :=
  setup.spacingEvidence = .figurePrimary ∧
    lengthInMillimeters setup.figureFringeSpacing = 1.53 ∧
    setup.lowestShownOrder = -9 ∧
    setup.highestShownOrder = 9 ∧
    setup.spacingMarkerLeftOrder = -1 ∧
    setup.spacingMarkerRightOrder = 0 ∧
    lengthInMillimeters (setup.screenOffset 0) = 0 ∧
    lengthInMillimeters (setup.screenOffset 0) -
        lengthInMillimeters (setup.screenOffset (-1)) =
      lengthInMillimeters setup.figureFringeSpacing ∧
    setup.spotVisibility (-7) = .missing ∧
    setup.spotVisibility 7 = .missing ∧
    (∀ order : ℤ,
      -9 ≤ order → order ≤ 9 → order ≠ -7 → order ≠ 7 →
        setup.spotVisibility order = .bright)

/-!
Constructive two-slit interference law

`d sin θₘ = m λ`.

It is stated in every length unit for the finite order window represented by
the cropped figure. Restricting the law to physically represented orders is
essential: no fixed positive `d` and `λ` could realize every integer order.
The law does not contain the requested slit width.
-/
def SatisfiesConstructiveInterferenceLaw
    (setup : MissingFringeDoubleSlitSetup) : Prop :=
  ∀ (order : ℤ) (unit : LengthUnit),
    setup.lowestShownOrder ≤ order → order ≤ setup.highestShownOrder →
      lengthReadout unit setup.slitSeparation *
          Real.Angle.sin (setup.interferenceAngle order) =
        (order : ℝ) * lengthReadout unit setup.wavelength

/-!
Exact planar-screen projection

`yₘ = L tan θₘ`.

The screen is perpendicular to the central optical axis, so elementary ray
geometry gives this tangent relation without a small-angle replacement.  The
ideal order position exists even when the finite slit width suppresses its
brightness. Together with adjacent order positions, this law calibrates the
slit separation but says nothing directly about slit width.
-/
structure SatisfiesPlanarScreenProjection
    (setup : MissingFringeDoubleSlitSetup) : Prop where
  usesPlanarPerpendicularScreen : setup.screenGeometry = .planarPerpendicular
  screenProjection : ∀ (order : ℤ) (unit : LengthUnit),
    setup.lowestShownOrder ≤ order → order ≤ setup.highestShownOrder →
      lengthReadout unit (setup.screenOffset order) =
        lengthReadout unit setup.screenDistance *
          Real.Angle.tan (setup.interferenceAngle order)

/-!
First-minimum law for the diffraction envelope of each finite slit:

`a |sin θ₁| = λ`.

This is a governing single-slit law, not the requested numerical value of
`a`.
-/
def SatisfiesFirstMinimumDiffractionLaw
    (setup : MissingFringeDoubleSlitSetup) : Prop :=
  ∀ (side : ScreenSide) (unit : LengthUnit),
    lengthReadout unit setup.slitWidth *
        |Real.Angle.sin (setup.firstMinimumAngle side)| =
      lengthReadout unit setup.wavelength

/-!
Physical interpretation of the missing spots: the first missing constructive
order on each side coincides with the first minimum of the one-slit envelope.
This identifies the relevant orders and angles but does not assume a width.
-/
def MissingSpotsCoincideWithFirstMinima
    (setup : MissingFringeDoubleSlitSetup) : Prop :=
  setup.interferenceAngle (-7) = setup.firstMinimumAngle .left ∧
    setup.interferenceAngle 7 = setup.firstMinimumAngle .right

/-- Labels of the four slit-width choices printed with the dataset item. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The width in millimetres printed beside each answer label. -/
def displayedWidthInMillimeters : AnswerChoice → ℝ
  | .A => 0.148
  | .B => 0.152
  | .C => 0.134
  | .D => 0.132

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Round a millimetre readout to the nearest thousandth of a millimetre. -/
def roundedToNearestThousandth (value : ℝ) : ℝ :=
  (round (1000 * value) : ℝ) / 1000

/-- A displayed choice agrees with the derived rounded width. -/
def MatchesDisplayedWidth
    (setup : MissingFringeDoubleSlitSetup)
    (choice : AnswerChoice) : Prop :=
  roundedToNearestThousandth (lengthInMillimeters setup.slitWidth) =
    displayedWidthInMillimeters choice

/-- The selected answer is the unique displayed choice matching the width. -/
def IsUniqueMatchingDisplayedWidth
    (setup : MissingFringeDoubleSlitSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedWidth setup choice ∧
    ∀ other : AnswerChoice, MatchesDisplayedWidth setup other → other = choice

/-!
Using the figure-primary `1.53 mm` spacing, `λ = 632.8 nm`, and `L =
2.50 m`, the interference and exact tangent-projection laws give the slit
separation. Coincidence of order `7` with the first diffraction minimum then
gives the exact common width
`(791/5355) * sqrt (1 + (153/250000)^2) mm`, approximately `0.147712 mm`.
-/
lemma slitWidthInMillimeters_eq
    (setup : MissingFringeDoubleSlitSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_problem : MatchesProblemReadouts setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_interference : SatisfiesConstructiveInterferenceLaw setup)
    (h_projection : SatisfiesPlanarScreenProjection setup)
    (h_diffraction : SatisfiesFirstMinimumDiffractionLaw setup)
    (h_missing : MissingSpotsCoincideWithFirstMinima setup) :
    lengthInMillimeters setup.slitWidth =
      (791 / 5355) * Real.sqrt (1 + (153 / 250000 : ℝ) ^ 2) := by
  have nanometers_to_millimeters (length : LengthQuantity) :
      lengthInMillimeters length =
        (1 / 1000000 : ℝ) * lengthInNanometers length := by
    let u_nm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.nanometers }
    let u_mm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.millimeters }
    have hnonneg : (0 : ℝ) ≤ 1 / 1000000 := by norm_num
    let scaleFactor : NNReal := ⟨1 / 1000000, hnonneg⟩
    have hscale : u_nm.dimScale u_mm L𝓭 = scaleFactor := by
      norm_num [u_nm, u_mm, scaleFactor, UnitChoices.dimScale,
        LengthUnit.nanometers, LengthUnit.millimeters, LengthUnit.scale,
        LengthUnit.meters, LengthUnit.div_eq_val]
    have hcoe : (scaleFactor : ℝ) = 1 / 1000000 := NNReal.coe_mk _ _
    have hchange := congrArg WithDim.val (length.2 u_nm u_mm)
    change (length u_mm).val =
      (1 / 1000000 : ℝ) * (length u_nm).val
    rw [hchange]
    simp only [WithDim.smul_val, WithDim.dim_apply, hscale,
      NNReal.smul_def, smul_eq_mul]
    rw [hcoe]
  have meters_to_millimeters (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    let u_m : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.meters }
    let u_mm : UnitChoices :=
      { UnitChoices.SI with length := LengthUnit.millimeters }
    let scaleFactor : NNReal := ⟨1000, by norm_num⟩
    have hscale : u_m.dimScale u_mm L𝓭 = scaleFactor := by
      norm_num [u_m, u_mm, scaleFactor, UnitChoices.dimScale,
        LengthUnit.millimeters, LengthUnit.scale, LengthUnit.meters,
        LengthUnit.div_eq_val]
    have hcoe : (scaleFactor : ℝ) = 1000 := NNReal.coe_mk _ _
    have hchange := congrArg WithDim.val (length.2 u_m u_mm)
    change (length u_mm).val = (1000 : ℝ) * (length u_m).val
    rw [hchange]
    simp only [WithDim.smul_val, WithDim.dim_apply, hscale,
      NNReal.smul_def, smul_eq_mul]
    rw [hcoe]
  rcases h_physical with
    ⟨_, _, _, _, _, _, hsin_seven_pos, hcos_neg_one_pos, _⟩
  rcases h_problem with ⟨hwavelength_nm, hscreen_m, _⟩
  rcases h_figure with
    ⟨_, hspacing_mm, hlower, hupper, _, _, hoffset_zero,
      hadjacent, _, _, _⟩
  have hwavelength_mm :
      lengthInMillimeters setup.wavelength = (791 / 1250000 : ℝ) := by
    rw [nanometers_to_millimeters, hwavelength_nm]
    norm_num
  have hscreen_mm :
      lengthInMillimeters setup.screenDistance = 2500 := by
    rw [meters_to_millimeters, hscreen_m]
    norm_num
  have hoffset_neg_one :
      lengthInMillimeters (setup.screenOffset (-1)) = -1.53 := by
    linarith
  have hneg_one_lower : setup.lowestShownOrder ≤ -1 := by omega
  have hneg_one_upper : (-1 : ℤ) ≤ setup.highestShownOrder := by omega
  have hseven_lower : setup.lowestShownOrder ≤ 7 := by omega
  have hseven_upper : (7 : ℤ) ≤ setup.highestShownOrder := by omega
  have hprojection_neg_one :=
    h_projection.screenProjection (-1) LengthUnit.millimeters
      hneg_one_lower hneg_one_upper
  change
    lengthInMillimeters (setup.screenOffset (-1)) =
      lengthInMillimeters setup.screenDistance *
        Real.Angle.tan (setup.interferenceAngle (-1))
    at hprojection_neg_one
  have htan_neg_one :
      Real.Angle.tan (setup.interferenceAngle (-1)) =
        -(153 / 250000 : ℝ) := by
    rw [hoffset_neg_one, hscreen_mm] at hprojection_neg_one
    norm_num at hprojection_neg_one ⊢
    linarith
  have hinterference_neg_one :=
    h_interference (-1) LengthUnit.millimeters
      hneg_one_lower hneg_one_upper
  have hinterference_seven :=
    h_interference 7 LengthUnit.millimeters hseven_lower hseven_upper
  change
    lengthInMillimeters setup.slitSeparation *
        Real.Angle.sin (setup.interferenceAngle (-1)) =
      ((-1 : ℤ) : ℝ) * lengthInMillimeters setup.wavelength
    at hinterference_neg_one
  change
    lengthInMillimeters setup.slitSeparation *
        Real.Angle.sin (setup.interferenceAngle 7) =
      ((7 : ℤ) : ℝ) * lengthInMillimeters setup.wavelength
    at hinterference_seven
  rw [hwavelength_mm] at hinterference_neg_one hinterference_seven
  norm_num at hinterference_neg_one hinterference_seven
  have hdiffraction_seven :=
    h_diffraction .right LengthUnit.millimeters
  change
    lengthInMillimeters setup.slitWidth *
        |Real.Angle.sin (setup.firstMinimumAngle .right)| =
      lengthInMillimeters setup.wavelength
    at hdiffraction_seven
  rw [← h_missing.2, abs_of_pos hsin_seven_pos, hwavelength_mm] at hdiffraction_seven
  let sine_neg_one : ℝ :=
    Real.Angle.sin (setup.interferenceAngle (-1))
  let cosine_neg_one : ℝ :=
    Real.Angle.cos (setup.interferenceAngle (-1))
  let radial_factor : ℝ :=
    Real.sqrt (1 + (153 / 250000 : ℝ) ^ 2)
  change 0 < cosine_neg_one at hcos_neg_one_pos
  have hcos_neg_one_ne : cosine_neg_one ≠ 0 :=
    ne_of_gt hcos_neg_one_pos
  rw [Real.Angle.tan_eq_sin_div_cos] at htan_neg_one
  change sine_neg_one / cosine_neg_one = -(153 / 250000 : ℝ) at htan_neg_one
  have hsine_neg_one :
      sine_neg_one = -(153 / 250000 : ℝ) * cosine_neg_one :=
    (div_eq_iff hcos_neg_one_ne).mp htan_neg_one
  have htrig :
      cosine_neg_one ^ 2 + sine_neg_one ^ 2 = 1 := by
    exact Real.Angle.cos_sq_add_sin_sq (setup.interferenceAngle (-1))
  rw [hsine_neg_one] at htrig
  have hcosine_squared :
      cosine_neg_one ^ 2 * (1 + (153 / 250000 : ℝ) ^ 2) = 1 := by
    nlinarith
  have hradicand_pos :
      0 < (1 + (153 / 250000 : ℝ) ^ 2) := by positivity
  have hradial_pos : 0 < radial_factor := by
    exact Real.sqrt_pos.2 hradicand_pos
  have hradial_squared :
      radial_factor ^ 2 = 1 + (153 / 250000 : ℝ) ^ 2 := by
    dsimp [radial_factor]
    rw [Real.sq_sqrt (le_of_lt hradicand_pos)]
  have hcosine_radial_squared :
      (cosine_neg_one * radial_factor) ^ 2 = 1 := by
    calc
      (cosine_neg_one * radial_factor) ^ 2 =
          cosine_neg_one ^ 2 * radial_factor ^ 2 := by ring
      _ = cosine_neg_one ^ 2 *
          (1 + (153 / 250000 : ℝ) ^ 2) := by rw [hradial_squared]
      _ = 1 := hcosine_squared
  have hcosine_radial_pos :
      0 < cosine_neg_one * radial_factor :=
    mul_pos hcos_neg_one_pos hradial_pos
  have hcosine_radial :
      cosine_neg_one * radial_factor = 1 := by
    nlinarith
  change
    lengthInMillimeters setup.slitSeparation * sine_neg_one =
      -(791 / 1250000 : ℝ)
    at hinterference_neg_one
  rw [hsine_neg_one] at hinterference_neg_one
  have hseparation_relation :
      lengthInMillimeters setup.slitSeparation *
          (153 / 250000 : ℝ) * cosine_neg_one =
        (791 / 1250000 : ℝ) := by
    calc
      lengthInMillimeters setup.slitSeparation *
          (153 / 250000 : ℝ) * cosine_neg_one =
          -(lengthInMillimeters setup.slitSeparation *
            (-(153 / 250000 : ℝ) * cosine_neg_one)) := by ring
      _ = -(-(791 / 1250000 : ℝ)) := by rw [hinterference_neg_one]
      _ = (791 / 1250000 : ℝ) := by ring
  have hsine_seven_ne :
      Real.Angle.sin (setup.interferenceAngle 7) ≠ 0 :=
    ne_of_gt hsin_seven_pos
  have hseparation_eq_seven_width :
      lengthInMillimeters setup.slitSeparation =
        7 * lengthInMillimeters setup.slitWidth := by
    apply mul_right_cancel₀ hsine_seven_ne
    calc
      lengthInMillimeters setup.slitSeparation *
          Real.Angle.sin (setup.interferenceAngle 7) =
          (5537 / 1250000 : ℝ) := hinterference_seven
      _ = 7 * (791 / 1250000 : ℝ) := by norm_num
      _ = 7 * (lengthInMillimeters setup.slitWidth *
          Real.Angle.sin (setup.interferenceAngle 7)) := by
        rw [hdiffraction_seven]
      _ = (7 * lengthInMillimeters setup.slitWidth) *
          Real.Angle.sin (setup.interferenceAngle 7) := by ring
  rw [hseparation_eq_seven_width] at hseparation_relation
  have hwidth_relation :
      7 * lengthInMillimeters setup.slitWidth *
          (153 / 250000 : ℝ) =
        (791 / 1250000 : ℝ) * radial_factor := by
    calc
      7 * lengthInMillimeters setup.slitWidth *
          (153 / 250000 : ℝ) =
          (7 * lengthInMillimeters setup.slitWidth *
            (153 / 250000 : ℝ)) *
            (cosine_neg_one * radial_factor) := by
              rw [hcosine_radial]
              ring
      _ = (7 * lengthInMillimeters setup.slitWidth *
            (153 / 250000 : ℝ) * cosine_neg_one) *
            radial_factor := by ring
      _ = (791 / 1250000 : ℝ) * radial_factor := by
        rw [hseparation_relation]
  change lengthInMillimeters setup.slitWidth =
    (791 / 5355) * radial_factor
  norm_num at hwidth_relation ⊢
  linarith

/-!
The exact planar-screen-model width rounds to `0.148 mm`, uniquely selecting
answer A, which is also the recorded dataset answer.

This formalizes `thm:physics:phyx_mini_0122:target`. The printed choices and
recorded label are retained as source metadata, but no premise asserts the
exact width, its rounded value, or that A uniquely matches the derived width.
-/
theorem problem_phyx_mini_0122
    (setup : MissingFringeDoubleSlitSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_geometry : MatchesSlitGeometry setup)
    (h_problem : MatchesProblemReadouts setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_interference : SatisfiesConstructiveInterferenceLaw setup)
    (h_projection : SatisfiesPlanarScreenProjection setup)
    (h_diffraction : SatisfiesFirstMinimumDiffractionLaw setup)
    (h_missing : MissingSpotsCoincideWithFirstMinima setup) :
    lengthInMillimeters setup.slitWidth =
        (791 / 5355) * Real.sqrt (1 + (153 / 250000 : ℝ) ^ 2) ∧
      IsUniqueMatchingDisplayedWidth setup .A := by
  have hwidth := slitWidthInMillimeters_eq setup h_physical h_problem
    h_figure h_interference h_projection h_diffraction h_missing
  have hsqrt_lower :
      (1 : ℝ) ≤ Real.sqrt (1 + (153 / 250000 : ℝ) ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg (153 / 250000 : ℝ)]
  have hsqrt_upper :
      Real.sqrt (1 + (153 / 250000 : ℝ) ^ 2) <
        (1001 / 1000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1001 / 1000)]
    norm_num
  have hround :
      round (1000 * ((791 / 5355 : ℝ) *
        Real.sqrt (1 + (153 / 250000 : ℝ) ^ 2))) = 148 := by
    apply round_eq_iff.mpr
    constructor <;> linarith
  constructor
  · exact hwidth
  · change
      MatchesDisplayedWidth setup .A ∧
        ∀ other : AnswerChoice,
          MatchesDisplayedWidth setup other → other = .A
    constructor
    · unfold MatchesDisplayedWidth roundedToNearestThousandth
      rw [hwidth, hround]
      norm_num [displayedWidthInMillimeters]
    · intro other hother
      unfold MatchesDisplayedWidth roundedToNearestThousandth at hother
      rw [hwidth, hround] at hother
      cases other
      · rfl
      all_goals norm_num [displayedWidthInMillimeters] at hother

end PhyXMiniProblems.ProblemPhyXMini0122
