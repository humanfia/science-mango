import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Basic

/- USER: The assigned file was absent, so there were no file-specific hints to preserve. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0924

open Dimension

/-!
# Greatest two-slit interference-minimum angle

Monochromatic light of wavelength `435 nm` illuminates two parallel slits of
finite width.  The primary figure plots the full path phase difference `β`,
in radians, against `sin θ`.  Its thick straight trace joins `(0, 0)` to
`(1, βₛ)`, where the prose calibrates `βₛ = 80.0 rad`.

The convention used here is the full phase difference

`β(θ) = 2π d sin θ / λ`.

Thus interference minima occur at odd multiples of `π`.  This is the phase
convention consistent with the recorded `79.0°` answer.  The separate
single-slit phase `α(θ) = π a sin θ / λ` retains the source assumption that
no interference maximum is eliminated by a diffraction minimum.

Lengths are unit-independent Physlib quantities.  Radian and degree values
are real scalar readouts because plane angle and phase are dimensionless.
-/

/-! ## Dimensionful optical quantities and readouts -/

/-- A nonnegative physical length, independent of the chosen readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length as a real number in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- The nanometre readout used for the stated wavelength. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Convert an angle readout in radians to its numerical degree readout. -/
def angleInDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-! ## Primary-figure vocabulary -/

/-- The two quantities labelling the axes of the supplied graph. -/
inductive FigureAxis where
  | sineOfAngle
  | betaPhase
  deriving DecidableEq, Repr

/-- The units explicitly printed beside the graph axes. -/
inductive FigureAxisUnit where
  | dimensionless
  | radians
  deriving DecidableEq, Repr

/-- The symbol printed at the top of the vertical scale. -/
inductive VerticalScaleLabel where
  | betaSubS
  deriving DecidableEq, Repr

/-- The line style visible in the raster. -/
inductive TraceStyle where
  | thickBlackStraight
  deriving DecidableEq, Repr

/--
Literal graph metadata and its scalar plot readout.  The plot function is an
observable supplied by the figure; it is not defined from a desired angle.
-/
structure BetaVersusSineFigure where
  horizontalAxis : FigureAxis
  verticalAxis : FigureAxis
  horizontalUnit : FigureAxisUnit
  verticalUnit : FigureAxisUnit
  horizontalTickValues : List ℝ
  verticalScaleLabel : VerticalScaleLabel
  verticalScaleRadians : ℝ
  traceStyle : TraceStyle
  hasRectangularGrid : Bool
  gridColumnCount : ℕ
  gridRowCount : ℕ
  plottedBetaRadiansAtSine : ℝ → ℝ

/-! ## Physical setup and source readouts -/

/--
Physical lengths, phase observables, and the supplied figure for the finite
double-slit experiment.  `betaRadiansAt` is the full phase difference between
the two slit contributions; `alphaRadiansAt` is the phase governing the
single-slit diffraction envelope.
-/
structure FiniteDoubleSlitSetup where
  wavelength : LengthQuantity
  slitCenterSeparation : LengthQuantity
  commonSlitWidth : LengthQuantity
  betaRadiansAt : ℝ → ℝ
  alphaRadiansAt : ℝ → ℝ
  figure : BetaVersusSineFigure

/-- The nonnegative forward angular branch represented by `0 ≤ sin θ ≤ 1`. -/
def IsForwardAngle (angleRadians : ℝ) : Prop :=
  0 ≤ angleRadians ∧ angleRadians ≤ Real.pi / 2

/-- Positive wavelength, slit separation, and slit width. -/
def HasPhysicalDoubleSlitParameters (setup : FiniteDoubleSlitSetup) : Prop :=
  0 < lengthInNanometers setup.wavelength ∧
    0 < lengthInNanometers setup.slitCenterSeparation ∧
    0 < lengthInNanometers setup.commonSlitWidth

/-- The wavelength stated in the prose is `435 nm`. -/
def MatchesProblemWavelengthReadout (setup : FiniteDoubleSlitSetup) : Prop :=
  lengthInNanometers setup.wavelength = 435

/-!
The primary image has axes `sin θ` and `β (rad)`, horizontal markings
`0, 0.5, 1`, a four-by-four rectangular grid, and a thick black diagonal from
the origin to `(1, βₛ)`.  The prose calibrates `βₛ` as `80.0 rad`.

The final conjunct connects the plotted ordinate at `sin θ` to the physical
phase observable.  It is a general graph readout on the whole forward branch,
not the requested minimum-angle conclusion.
-/
def MatchesPrimaryBetaVersusSineFigure
    (setup : FiniteDoubleSlitSetup) : Prop :=
  setup.figure.horizontalAxis = .sineOfAngle ∧
    setup.figure.verticalAxis = .betaPhase ∧
    setup.figure.horizontalUnit = .dimensionless ∧
    setup.figure.verticalUnit = .radians ∧
    setup.figure.horizontalTickValues = [0, 1 / 2, 1] ∧
    setup.figure.verticalScaleLabel = .betaSubS ∧
    setup.figure.verticalScaleRadians = 80 ∧
    setup.figure.traceStyle = .thickBlackStraight ∧
    setup.figure.hasRectangularGrid = true ∧
    setup.figure.gridColumnCount = 4 ∧
    setup.figure.gridRowCount = 4 ∧
    setup.figure.plottedBetaRadiansAtSine 0 = 0 ∧
    setup.figure.plottedBetaRadiansAtSine 1 =
      setup.figure.verticalScaleRadians ∧
    (∀ sineValue : ℝ, 0 ≤ sineValue → sineValue ≤ 1 →
      setup.figure.plottedBetaRadiansAtSine sineValue =
        setup.figure.verticalScaleRadians * sineValue) ∧
    ∀ angleRadians : ℝ, IsForwardAngle angleRadians →
      setup.betaRadiansAt angleRadians =
        setup.figure.plottedBetaRadiansAtSine (Real.sin angleRadians)

/-! ## Governing finite-double-slit laws -/

/-!
The two general phase laws for equal finite-width slits:

* the full inter-slit path phase is `β = 2π(d/λ) sin θ`;
* the single-slit diffraction phase is `α = π(a/λ) sin θ`.

They are stated in every common length unit.  Neither law singles out an
order, a greatest angle, or an answer choice.
-/
structure SatisfiesFiniteDoubleSlitPhaseLaws
    (setup : FiniteDoubleSlitSetup) : Prop where
  fullPathPhaseDifference :
    ∀ (angleRadians : ℝ), IsForwardAngle angleRadians →
      ∀ unit : LengthUnit,
        setup.betaRadiansAt angleRadians =
          2 * Real.pi *
            (lengthReadout unit setup.slitCenterSeparation /
              lengthReadout unit setup.wavelength) *
            Real.sin angleRadians
  singleSlitDiffractionPhase :
    ∀ (angleRadians : ℝ), IsForwardAngle angleRadians →
      ∀ unit : LengthUnit,
        setup.alphaRadiansAt angleRadians =
          Real.pi *
            (lengthReadout unit setup.commonSlitWidth /
              lengthReadout unit setup.wavelength) *
            Real.sin angleRadians

/-- A destructive two-source fringe: the full phase is an odd multiple of π. -/
def IsInterferenceMinimum
    (setup : FiniteDoubleSlitSetup) (angleRadians : ℝ) : Prop :=
  IsForwardAngle angleRadians ∧
    ∃ order : ℕ,
      setup.betaRadiansAt angleRadians =
        (2 * (order : ℝ) + 1) * Real.pi

/-- A constructive two-source fringe: the full phase is an even multiple of π. -/
def IsInterferenceMaximum
    (setup : FiniteDoubleSlitSetup) (angleRadians : ℝ) : Prop :=
  IsForwardAngle angleRadians ∧
    ∃ order : ℕ,
      setup.betaRadiansAt angleRadians =
        2 * (order : ℝ) * Real.pi

/-- A noncentral minimum of the single-slit diffraction envelope. -/
def IsDiffractionMinimum
    (setup : FiniteDoubleSlitSetup) (angleRadians : ℝ) : Prop :=
  IsForwardAngle angleRadians ∧
    ∃ order : ℕ, 0 < order ∧
      setup.alphaRadiansAt angleRadians = (order : ℝ) * Real.pi

/--
The explicit source assumption that no interference maximum is completely
eliminated by a diffraction minimum.
-/
def NoInterferenceMaximumEliminatedByDiffraction
    (setup : FiniteDoubleSlitSetup) : Prop :=
  ∀ angleRadians : ℝ,
    IsInterferenceMaximum setup angleRadians →
      ¬ IsDiffractionMinimum setup angleRadians

/-- A forward interference minimum greater than or equal to every other one. -/
def IsGreatestInterferenceMinimum
    (setup : FiniteDoubleSlitSetup) (angleRadians : ℝ) : Prop :=
  IsInterferenceMinimum setup angleRadians ∧
    ∀ otherAngleRadians : ℝ,
      IsInterferenceMinimum setup otherAngleRadians →
        otherAngleRadians ≤ angleRadians

/-! ## Answer-choice readouts -/

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical degree readout printed beside each answer label. -/
def displayedAngleInDegrees : AnswerChoice → ℝ
  | .A => 77.5
  | .B => 80.0
  | .C => 79.0
  | .D => 75.0

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a value displayed to the nearest tenth of a degree. -/
def MatchesDisplayedTenthDegree
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |angleInDegrees angleRadians - displayedAngleInDegrees choice| ≤ 1 / 20

/-- A displayed choice is the unique tenth-degree match to an angle. -/
def IsUniqueMatchingDisplayedAngle
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedTenthDegree angleRadians choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedTenthDegree angleRadians other → other = choice

/-! ## Derived statements and blueprint target -/

/-!
Combining the graph endpoint, wavelength calibration, and general full-phase
law determines the slit-center separation.  This intermediate result retains
the stated wavelength even though it cancels from the requested angle.
-/
lemma slitCenterSeparationInNanometers_eq
    (setup : FiniteDoubleSlitSetup)
    (h_physical : HasPhysicalDoubleSlitParameters setup)
    (h_wavelength : MatchesProblemWavelengthReadout setup)
    (h_figure : MatchesPrimaryBetaVersusSineFigure setup)
    (h_laws : SatisfiesFiniteDoubleSlitPhaseLaws setup) :
    lengthInNanometers setup.slitCenterSeparation =
      80 * 435 / (2 * Real.pi) := by
  rcases h_figure with
    ⟨_, _, _, _, _, _, h_scale, _, _, _, _, _, _, h_linear, h_graph⟩
  have h_forward : IsForwardAngle (Real.pi / 2) := by
    exact ⟨by positivity, le_rfl⟩
  have h_beta : setup.betaRadiansAt (Real.pi / 2) = 80 := by
    calc
      setup.betaRadiansAt (Real.pi / 2) =
          setup.figure.plottedBetaRadiansAtSine
            (Real.sin (Real.pi / 2)) :=
        h_graph (Real.pi / 2) h_forward
      _ = setup.figure.plottedBetaRadiansAtSine 1 := by
        rw [Real.sin_pi_div_two]
      _ = setup.figure.verticalScaleRadians * 1 :=
        h_linear 1 (by norm_num) (by norm_num)
      _ = 80 := by rw [h_scale]; norm_num
  have h_phase :=
    h_laws.fullPathPhaseDifference
      (Real.pi / 2) h_forward LengthUnit.nanometers
  change lengthReadout LengthUnit.nanometers setup.wavelength = 435 at h_wavelength
  change
    lengthReadout LengthUnit.nanometers setup.slitCenterSeparation =
      80 * 435 / (2 * Real.pi)
  rw [h_beta, Real.sin_pi_div_two, h_wavelength] at h_phase
  apply (eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
  field_simp at h_phase
  nlinarith

/-!
The largest odd multiple of `π` below the graph's phase ceiling `80` is
`25π`, corresponding to interference-minimum order `12`.
-/
lemma twentyFivePi_is_largest_visible_odd_phase :
    25 * Real.pi ≤ 80 ∧
      ∀ order : ℕ,
        (2 * (order : ℝ) + 1) * Real.pi ≤ 80 → order ≤ 12 := by
  have h_sin_half : Real.sin (1 / 2 : ℝ) < 1 / 2 := by
    have hbound := Real.sin_bound (x := (1 / 2 : ℝ)) (by norm_num)
    rw [abs_le] at hbound
    norm_num at hbound ⊢
    linarith
  have h_sin_eight_fifteenths :
      (1 / 2 : ℝ) < Real.sin (8 / 15 : ℝ) := by
    have hbound := Real.sin_bound (x := (8 / 15 : ℝ)) (by norm_num)
    rw [abs_le] at hbound
    norm_num at hbound ⊢
    linarith
  have h_pi_six_mem :
      Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have h_half_mem :
      (1 / 2 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.one_le_pi_div_two]
  have h_eight_fifteenths_mem :
      (8 / 15 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.one_le_pi_div_two]
  have h_pi_lower : (3 : ℝ) < Real.pi := by
    have hangle :=
      (Real.strictMonoOn_sin.lt_iff_lt h_half_mem h_pi_six_mem).mp
        (by simpa [Real.sin_pi_div_six] using h_sin_half)
    nlinarith
  have h_pi_upper : Real.pi < (16 / 5 : ℝ) := by
    have hangle :=
      (Real.strictMonoOn_sin.lt_iff_lt
        h_pi_six_mem h_eight_fifteenths_mem).mp
        (by simpa [Real.sin_pi_div_six] using h_sin_eight_fifteenths)
    nlinarith
  constructor
  · nlinarith
  · intro order h_visible
    by_contra h_order
    have h_thirteen : 13 ≤ order := by omega
    have h_thirteen_real : (13 : ℝ) ≤ order := by
      exact_mod_cast h_thirteen
    have h_coefficient : (27 : ℝ) ≤ 2 * (order : ℝ) + 1 := by
      linarith
    have h_phase_lower :=
      mul_le_mul_of_nonneg_right h_coefficient Real.pi_pos.le
    nlinarith

/-!
The greatest forward interference minimum therefore has
`sin θ = 25π/80`, hence `θ = arcsin(25π/80)` radians.
-/
lemma greatestInterferenceMinimumAngle_exact
    (setup : FiniteDoubleSlitSetup)
    (h_physical : HasPhysicalDoubleSlitParameters setup)
    (h_wavelength : MatchesProblemWavelengthReadout setup)
    (h_figure : MatchesPrimaryBetaVersusSineFigure setup)
    (h_laws : SatisfiesFiniteDoubleSlitPhaseLaws setup) :
    IsGreatestInterferenceMinimum setup
      (Real.arcsin (25 * Real.pi / 80)) := by
  rcases h_figure with
    ⟨_, _, _, _, _, _, h_scale, _, _, _, _, _, _, h_linear, h_graph⟩
  have hx_nonneg : 0 ≤ 25 * Real.pi / 80 := by positivity
  have hx_le_one : 25 * Real.pi / 80 ≤ 1 := by
    nlinarith [twentyFivePi_is_largest_visible_odd_phase.1]
  have hx_neg_one : -(1 : ℝ) ≤ 25 * Real.pi / 80 := by
    linarith
  have h_sin_arcsin :
      Real.sin (Real.arcsin (25 * Real.pi / 80)) =
        25 * Real.pi / 80 :=
    Real.sin_arcsin hx_neg_one hx_le_one
  have h_forward :
      IsForwardAngle (Real.arcsin (25 * Real.pi / 80)) := by
    exact
      ⟨Real.arcsin_nonneg.2 hx_nonneg,
        Real.arcsin_le_pi_div_two (25 * Real.pi / 80)⟩
  have h_candidate_phase :
      setup.betaRadiansAt (Real.arcsin (25 * Real.pi / 80)) =
        25 * Real.pi := by
    calc
      setup.betaRadiansAt (Real.arcsin (25 * Real.pi / 80)) =
          setup.figure.plottedBetaRadiansAtSine
            (Real.sin (Real.arcsin (25 * Real.pi / 80))) :=
        h_graph _ h_forward
      _ = setup.figure.verticalScaleRadians *
            Real.sin (Real.arcsin (25 * Real.pi / 80)) :=
        h_linear _ (Real.sin_nonneg_of_nonneg_of_le_pi h_forward.1
          (by nlinarith [h_forward.2, Real.pi_pos]))
          (Real.sin_le_one _)
      _ = 25 * Real.pi := by
        rw [h_scale, h_sin_arcsin]
        ring
  refine ⟨⟨h_forward, ⟨12, ?_⟩⟩, ?_⟩
  · norm_num
    exact h_candidate_phase
  · intro otherAngle h_other
    rcases h_other with ⟨h_other_forward, order, h_other_phase⟩
    have h_other_sin_nonneg : 0 ≤ Real.sin otherAngle :=
      Real.sin_nonneg_of_nonneg_of_le_pi h_other_forward.1
        (by nlinarith [h_other_forward.2, Real.pi_pos])
    have h_other_beta :
        setup.betaRadiansAt otherAngle = 80 * Real.sin otherAngle := by
      calc
        setup.betaRadiansAt otherAngle =
            setup.figure.plottedBetaRadiansAtSine
              (Real.sin otherAngle) :=
          h_graph otherAngle h_other_forward
        _ = setup.figure.verticalScaleRadians * Real.sin otherAngle :=
          h_linear _ h_other_sin_nonneg (Real.sin_le_one _)
        _ = 80 * Real.sin otherAngle := by rw [h_scale]
    have h_visible :
        (2 * (order : ℝ) + 1) * Real.pi ≤ 80 := by
      rw [← h_other_phase, h_other_beta]
      nlinarith [Real.sin_le_one otherAngle]
    have h_order : order ≤ 12 :=
      twentyFivePi_is_largest_visible_odd_phase.2 order h_visible
    have h_order_real : (order : ℝ) ≤ 12 := by
      exact_mod_cast h_order
    have h_sin_le :
        Real.sin otherAngle ≤ 25 * Real.pi / 80 := by
      rw [h_other_beta] at h_other_phase
      nlinarith [Real.pi_pos]
    apply
      (Real.strictMonoOn_sin.le_iff_le
        ⟨by nlinarith [h_other_forward.1, Real.pi_pos],
          h_other_forward.2⟩
        ⟨by nlinarith [h_forward.1, Real.pi_pos], h_forward.2⟩).mp
    rwa [h_sin_arcsin]

/-!
The exact greatest angle is approximately `79.036°`; to the precision of the
displayed choices it is `79.0°`, uniquely selecting C.  The source's separate
non-elimination assumption is retained as a premise of the full problem.

This formalizes `thm:physics:phyx_mini_0924:target`.
-/
theorem problem_phyx_mini_0924
    (setup : FiniteDoubleSlitSetup)
    (h_physical : HasPhysicalDoubleSlitParameters setup)
    (h_wavelength : MatchesProblemWavelengthReadout setup)
    (h_figure : MatchesPrimaryBetaVersusSineFigure setup)
    (h_laws : SatisfiesFiniteDoubleSlitPhaseLaws setup)
    (h_no_eliminated_maximum :
      NoInterferenceMaximumEliminatedByDiffraction setup) :
    IsGreatestInterferenceMinimum setup
        (Real.arcsin (25 * Real.pi / 80)) ∧
      IsUniqueMatchingDisplayedAngle
        (Real.arcsin (25 * Real.pi / 80)) .C := by
  set_option maxHeartbeats 2000000 in
    refine
      ⟨greatestInterferenceMinimumAngle_exact setup h_physical h_wavelength
        h_figure h_laws, ?_⟩
    have nextUpperBounds {x su cu su' cu' : ℝ}
        (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
        (hs : Real.sin x < su) (hc : Real.cos x < cu)
        (hsUpper : 2 * su * cu ≤ su')
        (hcUpper : 2 * cu ^ 2 - 1 ≤ cu') :
        Real.sin (2 * x) < su' ∧ Real.cos (2 * x) < cu' := by
      have hsin : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi hx0
          (hx1.trans (by linarith [Real.two_le_pi]))
      have hcos : 0 ≤ Real.cos x :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by nlinarith [Real.pi_pos],
            hx1.trans Real.one_le_pi_div_two⟩
      rw [Real.sin_two_mul, Real.cos_two_mul]
      constructor
      · calc
          2 * Real.sin x * Real.cos x ≤ 2 * su * Real.cos x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs.le (by norm_num)) hcos
          _ < 2 * su * cu :=
            mul_lt_mul_of_pos_left hc
              (mul_pos (by norm_num) (lt_of_le_of_lt hsin hs))
          _ ≤ su' := hsUpper
      · nlinarith [hcUpper,
          mul_nonneg (sub_nonneg.mpr hc.le)
            (add_nonneg (lt_of_le_of_lt hcos hc).le hcos)]
    have nextLowerBounds {x sl cl sl' cl' : ℝ}
        (hsl : 0 < sl) (hcl : 0 < cl)
        (hs : sl < Real.sin x) (hc : cl < Real.cos x)
        (hsLower : sl' ≤ 2 * sl * cl)
        (hcLower : cl' ≤ 2 * cl ^ 2 - 1) :
        sl' < Real.sin (2 * x) ∧ cl' < Real.cos (2 * x) := by
      have hsin : 0 < Real.sin x := lt_trans hsl hs
      have hcos : 0 < Real.cos x := lt_trans hcl hc
      rw [Real.sin_two_mul, Real.cos_two_mul]
      constructor
      · calc
          sl' ≤ 2 * sl * cl := hsLower
          _ < 2 * Real.sin x * cl :=
            mul_lt_mul_of_pos_right
              (mul_lt_mul_of_pos_left hs (by norm_num)) hcl
          _ < 2 * Real.sin x * Real.cos x :=
            mul_lt_mul_of_pos_left hc (mul_pos (by norm_num) hsin)
      · nlinarith [hcLower,
          mul_pos (sub_pos.mpr hc) (add_pos hcos hcl)]
    have hPiL0 :
        Real.sin ((3.1415 : ℝ) / 384) < (0.00818090 : ℝ) ∧
          Real.cos ((3.1415 : ℝ) / 384) < (0.99996654 : ℝ) := by
      have hs := abs_le.mp
        (Real.sin_bound (x := (3.1415 : ℝ) / 384) (by norm_num))
      have hc := abs_le.mp
        (Real.cos_bound (x := (3.1415 : ℝ) / 384) (by norm_num))
      norm_num [abs_of_nonneg] at hs hc ⊢
      constructor
      · nlinarith [hs.2]
      · nlinarith [hc.2]
    have hPiL1 := nextUpperBounds
      (su' := (0.01636126 : ℝ)) (cu' := 0.99986617)
      (by norm_num) (by norm_num) hPiL0.1 hPiL0.2
      (by norm_num) (by norm_num)
    have hPiL2 := nextUpperBounds
      (su' := (0.03271815 : ℝ)) (cu' := 0.99946472)
      (by norm_num) (by norm_num) hPiL1.1 hPiL1.2
      (by norm_num) (by norm_num)
    have hPiL3 := nextUpperBounds
      (su' := (0.06540128 : ℝ)) (cu' := 0.99785946)
      (by norm_num) (by norm_num) hPiL2.1 hPiL2.2
      (by norm_num) (by norm_num)
    have hPiL4 := nextUpperBounds
      (su' := (0.13052258 : ℝ)) (cu' := 0.99144701)
      (by norm_num) (by norm_num) hPiL3.1 hPiL3.2
      (by norm_num) (by norm_num)
    have hPiL5 := nextUpperBounds
      (su' := (0.25881245 : ℝ)) (cu' := 0.96593435)
      (by norm_num) (by norm_num) hPiL4.1 hPiL4.2
      (by norm_num) (by norm_num)
    have hPiL6 := nextUpperBounds
      (su' := (0.49999168 : ℝ)) (cu' := 0.86605834)
      (by norm_num) (by norm_num) hPiL5.1 hPiL5.2
      (by norm_num) (by norm_num)
    have hPiU0 :
        (0.00818131 : ℝ) < Real.sin ((3.14166 : ℝ) / 384) ∧
          (0.99996653 : ℝ) < Real.cos ((3.14166 : ℝ) / 384) := by
      have hs := abs_le.mp
        (Real.sin_bound (x := (3.14166 : ℝ) / 384) (by norm_num))
      have hc := abs_le.mp
        (Real.cos_bound (x := (3.14166 : ℝ) / 384) (by norm_num))
      norm_num [abs_of_nonneg] at hs hc ⊢
      constructor
      · nlinarith [hs.1]
      · nlinarith [hc.1]
    have hPiU1 := nextLowerBounds
      (sl' := (0.01636207 : ℝ)) (cl' := 0.99986612)
      (by norm_num) (by norm_num) hPiU0.1 hPiU0.2
      (by norm_num) (by norm_num)
    have hPiU2 := nextLowerBounds
      (sl' := (0.03271975 : ℝ)) (cl' := 0.99946451)
      (by norm_num) (by norm_num) hPiU1.1 hPiU1.2
      (by norm_num) (by norm_num)
    have hPiU3 := nextLowerBounds
      (sl' := (0.06540445 : ℝ)) (cl' := 0.99785861)
      (by norm_num) (by norm_num) hPiU2.1 hPiU2.2
      (by norm_num) (by norm_num)
    have hPiU4 := nextLowerBounds
      (sl' := (0.13052878 : ℝ)) (cl' := 0.99144361)
      (by norm_num) (by norm_num) hPiU3.1 hPiU3.2
      (by norm_num) (by norm_num)
    have hPiU5 := nextLowerBounds
      (sl' := (0.25882384 : ℝ)) (cl' := 0.96592086)
      (by norm_num) (by norm_num) hPiU4.1 hPiU4.2
      (by norm_num) (by norm_num)
    have hPiU6 := nextLowerBounds
      (sl' := (0.50000669 : ℝ)) (cl' := 0.86600621)
      (by norm_num) (by norm_num) hPiU5.1 hPiU5.2
      (by norm_num) (by norm_num)
    clear hPiL0 hPiL1 hPiL2 hPiL3 hPiL4 hPiL5
      hPiU0 hPiU1 hPiU2 hPiU3 hPiU4 hPiU5
      nextUpperBounds nextLowerBounds
    have h_pi_bounds :
        (3.1415 : ℝ) < Real.pi ∧ Real.pi < (3.14166 : ℝ) := by
      norm_num at hPiL6 hPiU6
      have h_lower_sine :
          Real.sin ((3.1415 : ℝ) / 6) <
            Real.sin (Real.pi / 6) := by
        rw [Real.sin_pi_div_six]
        linarith [hPiL6.1]
      have h_upper_sine :
          Real.sin (Real.pi / 6) <
            Real.sin ((3.14166 : ℝ) / 6) := by
        rw [Real.sin_pi_div_six]
        linarith [hPiU6.1]
      have h_lower_mem :
          (3.1415 : ℝ) / 6 ∈
            Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> nlinarith [Real.two_le_pi]
      have h_pi_mem :
          Real.pi / 6 ∈
            Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> nlinarith [Real.pi_pos]
      have h_upper_mem :
          (3.14166 : ℝ) / 6 ∈
            Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> nlinarith [Real.two_le_pi]
      constructor
      · have hangle :=
          (Real.strictMonoOn_sin.lt_iff_lt h_lower_mem h_pi_mem).mp
            h_lower_sine
        linarith
      · have hangle :=
          (Real.strictMonoOn_sin.lt_iff_lt h_pi_mem h_upper_mem).mp
            h_upper_sine
        linarith
    have h_pi_lower : (31415 / 10000 : ℝ) < Real.pi := by
      norm_num at h_pi_bounds ⊢
      exact h_pi_bounds.1
    have h_pi_upper : Real.pi < (314166 / 100000 : ℝ) := by
      norm_num at h_pi_bounds ⊢
      exact h_pi_bounds.2
    clear h_pi_bounds
    clear hPiL6 hPiU6
    clear h_physical h_wavelength h_figure h_laws h_no_eliminated_maximum
    have hx_nonneg : 0 ≤ 25 * Real.pi / 80 := by positivity
    have hx_le_one : 25 * Real.pi / 80 ≤ 1 := by
      nlinarith [twentyFivePi_is_largest_visible_odd_phase.1]
    have hx_mem : 25 * Real.pi / 80 ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith, hx_le_one⟩
    have h_lower_sine :
        Real.sin (1579 * Real.pi / 3600) ≤ 25 * Real.pi / 80 := by
      let d : ℝ := 221 * Real.pi / 3600
      have hd_nonneg : 0 ≤ d := by
        dsimp [d]
        positivity
      have hd_le_pi : d ≤ Real.pi := by
        dsimp [d]
        nlinarith [Real.pi_pos]
      have hd_proxy : (1928 / 10000 : ℝ) ≤ d := by
        dsimp [d]
        nlinarith
      have hproxy_nonneg : (0 : ℝ) ≤ 1928 / 10000 := by norm_num
      have hcos_mono :
          Real.cos d ≤ Real.cos (1928 / 10000 : ℝ) :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          hproxy_nonneg hd_le_pi hd_proxy
      have hcos_proxy :
          Real.cos (1928 / 10000 : ℝ) ≤ 25 * Real.pi / 80 := by
        have hbound :=
          Real.cos_bound (x := (1928 / 10000 : ℝ)) (by norm_num)
        rw [abs_le] at hbound
        norm_num at hbound ⊢
        nlinarith
      rw [show 1579 * Real.pi / 3600 = Real.pi / 2 - d by
        dsimp [d]; ring, Real.sin_pi_div_two_sub]
      exact hcos_mono.trans hcos_proxy
    have h_upper_sine :
        25 * Real.pi / 80 ≤ Real.sin (1581 * Real.pi / 3600) := by
      let d : ℝ := 219 * Real.pi / 3600
      let z : ℝ := 239 / 5000
      have hd_nonneg : 0 ≤ d := by
        dsimp [d]
        positivity
      have hd_proxy : d ≤ (1912 / 10000 : ℝ) := by
        dsimp [d]
        nlinarith
      have hproxy_le_pi : (1912 / 10000 : ℝ) ≤ Real.pi := by
        nlinarith
      have hcos_mono :
          Real.cos (1912 / 10000 : ℝ) ≤ Real.cos d :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          hd_nonneg hproxy_le_pi hd_proxy
      let b : ℝ := 1 - z ^ 2 / 2 - z ^ 4 * (5 / 96)
      have hb_lower : b ≤ Real.cos z := by
        have hbound := Real.cos_bound (x := z) (by
          dsimp [z]
          norm_num)
        rw [abs_le, abs_of_nonneg (by dsimp [z]; norm_num)] at hbound
        dsimp [b]
        linarith
      have hb_nonneg : 0 ≤ b := by
        dsimp [b, z]
        norm_num
      have hcos_z_nonneg : 0 ≤ Real.cos z :=
        hb_nonneg.trans hb_lower
      have hb_sq : b ^ 2 ≤ (Real.cos z) ^ 2 := by
        nlinarith
          [mul_nonneg (sub_nonneg.mpr hb_lower)
            (add_nonneg hcos_z_nonneg hb_nonneg)]
      let b₂ : ℝ := 2 * b ^ 2 - 1
      have hb₂_lower : b₂ ≤ Real.cos (2 * z) := by
        rw [Real.cos_two_mul]
        dsimp [b₂]
        nlinarith
      have hb₂_nonneg : 0 ≤ b₂ := by
        dsimp [b₂, b, z]
        norm_num
      have hcos_two_z_nonneg : 0 ≤ Real.cos (2 * z) :=
        hb₂_nonneg.trans hb₂_lower
      have hb₂_sq : b₂ ^ 2 ≤ (Real.cos (2 * z)) ^ 2 := by
        nlinarith
          [mul_nonneg (sub_nonneg.mpr hb₂_lower)
            (add_nonneg hcos_two_z_nonneg hb₂_nonneg)]
      have hcos_proxy :
          25 * Real.pi / 80 ≤ Real.cos (1912 / 10000 : ℝ) := by
        calc
          25 * Real.pi / 80 ≤ 2 * b₂ ^ 2 - 1 := by
            dsimp [b₂, b, z]
            nlinarith
          _ ≤ 2 * (Real.cos (2 * z)) ^ 2 - 1 := by nlinarith
          _ = Real.cos (2 * (2 * z)) :=
            (Real.cos_two_mul (2 * z)).symm
          _ = Real.cos (1912 / 10000 : ℝ) := by
            congr 1
            dsimp [z]
            norm_num
      rw [show 1581 * Real.pi / 3600 = Real.pi / 2 - d by
        dsimp [d]; ring, Real.sin_pi_div_two_sub]
      exact hcos_proxy.trans hcos_mono
    have h_lower_angle :
        1579 * Real.pi / 3600 ≤
          Real.arcsin (25 * Real.pi / 80) := by
      apply (Real.le_arcsin_iff_sin_le ?_ hx_mem).2
      · exact h_lower_sine
      · constructor <;> nlinarith [Real.pi_pos]
    have h_upper_angle :
        Real.arcsin (25 * Real.pi / 80) ≤
          1581 * Real.pi / 3600 := by
      apply (Real.arcsin_le_iff_le_sin hx_mem ?_).2
      · exact h_upper_sine
      · constructor <;> nlinarith [Real.pi_pos]
    have h_degree_lower :
        (1579 / 20 : ℝ) ≤
          angleInDegrees (Real.arcsin (25 * Real.pi / 80)) := by
      unfold angleInDegrees
      apply (le_div_iff₀ Real.pi_pos).2
      nlinarith
    have h_degree_upper :
        angleInDegrees (Real.arcsin (25 * Real.pi / 80)) ≤
          (1581 / 20 : ℝ) := by
      unfold angleInDegrees
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith
    refine ⟨?_, ?_⟩
    · unfold MatchesDisplayedTenthDegree displayedAngleInDegrees
      rw [abs_le]
      constructor <;> norm_num <;> linarith
    · intro other h_other
      unfold MatchesDisplayedTenthDegree at h_other
      cases other with
      | A =>
          simp only [displayedAngleInDegrees] at h_other
          rw [abs_le] at h_other
          norm_num at h_other
          exfalso
          linarith
      | B =>
          simp only [displayedAngleInDegrees] at h_other
          rw [abs_le] at h_other
          norm_num at h_other
          exfalso
          linarith
      | C => rfl
      | D =>
          simp only [displayedAngleInDegrees] at h_other
          rw [abs_le] at h_other
          norm_num at h_other
          exfalso
          linarith

end PhyXMiniProblems.ProblemPhyXMini0924
