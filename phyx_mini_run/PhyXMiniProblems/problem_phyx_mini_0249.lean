import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

/-!
# Width of a single slit from its first diffraction minimum

This file models problem `phyx_mini_0249`. Light of wavelength `633 nm`
from a helium-neon laser passes through a single narrow slit. The screen is
`2.0 m` from the slit, and the first diffraction minimum is `1.2 cm` from
the central maximum.

The supplied figure labels the slit width by `a`, the slit-to-screen distance
by `L`, the first-minimum angle by `θ₁`, the minimum orders by `p = 1`
and `p = 2`, and the full central-maximum width by `w`. It also displays
the qualitative far-field condition `L ≫ a`.

Lengths are genuine dimensionful Physlib quantities. Real numbers occur only
as explicit unit readouts, dimensionless ratios, trigonometric values, and the
dimensionless parameter of a controlled asymptotic optical family.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0249

open Dimension

/-! ## Dimensionful optical quantities and unit readouts -/

/-- A signed, unit-independent physical quantity carrying length dimension. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout of a physical length. -/
def lengthInCentimeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Millimetre readout of a physical length. -/
def lengthInMillimeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Nanometre readout of a physical length. -/
def lengthInNanometers (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-! ## Apparatus and primary-figure labels -/

/-- The laser source named in the problem. -/
inductive LaserKind where
  | heliumNeon
  deriving DecidableEq, Repr

/-- The aperture geometry shown on the left of the supplied diagram. -/
inductive SlitGeometry where
  | singleNarrowSlit
  deriving DecidableEq, Repr

/-- The controlled limiting model used for the diffraction calculation. -/
inductive OpticalRegime where
  | fraunhoferParaxialAsymptotic
  deriving DecidableEq, Repr

/-- Text labels and qualitative features visible in the supplied figure. -/
inductive FigureFeature where
  | singleSlit
  | screen
  | lightIntensityCurve
  | centralMaximum
  | slitWidthLabelA
  | screenDistanceLabelL
  | firstMinimumAngleLabelThetaOne
  | firstMinimumOrderLabelPOne
  | secondMinimumOrderLabelPTwo
  | centralMaximumWidthLabelW
  | screenCoordinateAxisY
  | screenOriginZero
  | farFieldConditionLabelLMuchGreaterThanA
  deriving DecidableEq, Repr

/-
`scaledWavelengthInMillimeters ε`, `scaledMinimumAngle p ε`, and
`scaledMinimumDistanceRatio p ε` describe a family of similar experiments as
the positive dimensionless approximation parameter `ε` tends to zero. The
last quantity is the dimensionless ratio `yₚ / L`.

The experiment in the source is the member at `experimentalScale`. The fields
do not assign a value to the unknown physical slit width `slitWidthA`.
-/
structure SingleSlitDiffractionSetup where
  laserKind : LaserKind
  slitGeometry : SlitGeometry
  opticalRegime : OpticalRegime
  figureShows : FigureFeature → Prop
  /-- Vacuum/air wavelength `λ` in the source experiment. -/
  wavelength : OpticalLength
  /-- Unknown physical slit width `a` requested by the problem. -/
  slitWidthA : OpticalLength
  /-- Axial slit-to-screen separation `L`. -/
  screenDistanceL : OpticalLength
  /-- Positive screen distance from the center to the first minimum. -/
  firstMinimumDistanceFromCenter : OpticalLength
  /-- Full width `w` of the central maximum between its first minima. -/
  centralMaximumWidthW : OpticalLength
  /-- Positive-side minimum angle in the source experiment, indexed by `p`. -/
  minimumAngle : ℕ → Real.Angle
  /-- Lowest diffraction-minimum order explicitly marked in the figure. -/
  firstMarkedOrderP : ℕ
  /-- Highest diffraction-minimum order explicitly marked in the figure. -/
  secondMarkedOrderP : ℕ
  /-- Positive dimensionless scale selecting the source experiment. -/
  experimentalScale : ℝ
  /-- Millimetre wavelength readout in the scaled optical family. -/
  scaledWavelengthInMillimeters : ℝ → ℝ
  /-- Minimum angle of order `p` in the scaled optical family. -/
  scaledMinimumAngle : ℕ → ℝ → Real.Angle
  /-- Dimensionless transverse ratio `yₚ / L` in the scaled family. -/
  scaledMinimumDistanceRatio : ℕ → ℝ → ℝ

/-!
Source values and primary-figure readouts. The full central-maximum width is
the distance between the two symmetric first minima, hence `w = 2 y₁`.
This predicate contains no value of the unknown slit width or of a displayed
answer.
-/
def MatchesProblemAndFigureReadouts
    (setup : SingleSlitDiffractionSetup) : Prop :=
  setup.laserKind = .heliumNeon ∧
    setup.slitGeometry = .singleNarrowSlit ∧
    setup.opticalRegime = .fraunhoferParaxialAsymptotic ∧
    setup.figureShows .singleSlit ∧
    setup.figureShows .screen ∧
    setup.figureShows .lightIntensityCurve ∧
    setup.figureShows .centralMaximum ∧
    setup.figureShows .slitWidthLabelA ∧
    setup.figureShows .screenDistanceLabelL ∧
    setup.figureShows .firstMinimumAngleLabelThetaOne ∧
    setup.figureShows .firstMinimumOrderLabelPOne ∧
    setup.figureShows .secondMinimumOrderLabelPTwo ∧
    setup.figureShows .centralMaximumWidthLabelW ∧
    setup.figureShows .screenCoordinateAxisY ∧
    setup.figureShows .screenOriginZero ∧
    setup.figureShows .farFieldConditionLabelLMuchGreaterThanA ∧
    setup.firstMarkedOrderP = 1 ∧
    setup.secondMarkedOrderP = 2 ∧
    lengthInNanometers setup.wavelength = 633 ∧
    lengthInMeters setup.screenDistanceL = 2 ∧
    lengthInCentimeters setup.firstMinimumDistanceFromCenter = 6 / 5 ∧
    (∀ unit : LengthUnit,
      lengthReadout unit setup.centralMaximumWidthW =
        2 * lengthReadout unit setup.firstMinimumDistanceFromCenter)

/-- Positive, nondegenerate parameters of the source experiment. -/
def HasPhysicalParameters (setup : SingleSlitDiffractionSetup) : Prop :=
  0 < lengthInMeters setup.wavelength ∧
    0 < lengthInMeters setup.slitWidthA ∧
    0 < lengthInMeters setup.screenDistanceL ∧
    0 < lengthInMeters setup.firstMinimumDistanceFromCenter ∧
    0 < lengthInMeters setup.centralMaximumWidthW ∧
    0 < setup.experimentalScale

/--
An angle lies on the positive acute branch when it has a representative
strictly between `0` and `π/2`.
-/
def IsPositiveAcuteAngle (angle : Real.Angle) : Prop :=
  ∃ radians : ℝ,
    0 < radians ∧
      radians < Real.pi / 2 ∧
      angle = (radians : Real.Angle)

/-- Approach zero through positive values of the approximation parameter. -/
def smallPositiveScale : Filter ℝ :=
  nhdsWithin 0 (Set.Ioi 0)

/-! ## Exact geometry and controlled optical asymptotics -/

/-!
This interface connects the actual experiment to a scaled family. The family
keeps the physical slit width fixed and uses
`λ(ε) = ε a`; thus `ε` has the physical role of the dimensionless ratio
`λ / a`. It also identifies the measured first-minimum ratio at the selected
experimental scale. These are parameterization and observation relations,
not the numerical answer.
-/
structure ConnectsExperimentToScaledFamily
    (setup : SingleSlitDiffractionSetup) : Prop where
  source_wavelength_is_family_sample :
    setup.scaledWavelengthInMillimeters setup.experimentalScale =
      lengthInMillimeters setup.wavelength
  source_angles_are_family_sample :
    ∀ p : ℕ,
      setup.minimumAngle p =
        setup.scaledMinimumAngle p setup.experimentalScale
  source_first_minimum_ratio_is_family_sample :
    ∀ unit : LengthUnit,
      setup.scaledMinimumDistanceRatio 1 setup.experimentalScale *
          lengthReadout unit setup.screenDistanceL =
        lengthReadout unit setup.firstMinimumDistanceFromCenter
  wavelength_scaling :
    ∀ ε : ℝ, 0 ≤ ε →
      setup.scaledWavelengthInMillimeters ε =
        ε * lengthInMillimeters setup.slitWidthA

/-!
Exact planar-screen ray geometry uses `yₚ / L = tan θₚ`. This equality is
geometrical and is not the paraxial approximation `tan θ ≈ sin θ`.
-/
structure SatisfiesExactScreenRayGeometry
    (setup : SingleSlitDiffractionSetup) : Prop where
  minimum_angles_are_positive_acute :
    ∀ (p : ℕ), 0 < p → ∀ (ε : ℝ), 0 < ε →
      IsPositiveAcuteAngle (setup.scaledMinimumAngle p ε)
  relative_displacement_is_tangent :
    ∀ (p : ℕ), 0 < p → ∀ (ε : ℝ), 0 < ε →
      setup.scaledMinimumDistanceRatio p ε =
        Real.Angle.tan (setup.scaledMinimumAngle p ε)

/-!
A controlled asymptotic form of the two approximations used by the textbook
calculation.

* The single-slit residual
  `a sin θₚ(ε) - p λ(ε)` is little-o of `λ(ε)`.
* The paraxial projection residual
  `yₚ(ε)/L - sin θₚ(ε)` is little-o of `sin θₚ(ε)`.

Consequently neither approximation is asserted as a global exact identity at
the finite source experiment. The exact screen relation remains the tangent
law above.
-/
structure SatisfiesFraunhoferParaxialAsymptotics
    (setup : SingleSlitDiffractionSetup) : Prop where
  uses_controlled_asymptotic_regime :
    setup.opticalRegime = .fraunhoferParaxialAsymptotic
  single_slit_minimum_residual :
    ∀ (p : ℕ), 0 < p →
      Asymptotics.IsLittleO smallPositiveScale
        (fun ε : ℝ =>
          lengthInMillimeters setup.slitWidthA *
              Real.Angle.sin (setup.scaledMinimumAngle p ε) -
            (p : ℝ) * setup.scaledWavelengthInMillimeters ε)
        setup.scaledWavelengthInMillimeters
  paraxial_projection_residual :
    ∀ (p : ℕ), 0 < p →
      Asymptotics.IsLittleO smallPositiveScale
        (fun ε : ℝ =>
          setup.scaledMinimumDistanceRatio p ε -
            Real.Angle.sin (setup.scaledMinimumAngle p ε))
        (fun ε : ℝ =>
          Real.Angle.sin (setup.scaledMinimumAngle p ε))

/-! ## Leading-order inference and displayed answer -/

/-!
The order-one Fraunhofer-paraxial width estimator along the scaled family.
Both numerator and result are millimetre scalar readouts, while the denominator
is the dimensionless ratio `y₁ / L`.
-/
def widthEstimateProfileInMillimeters
    (setup : SingleSlitDiffractionSetup) (ε : ℝ) : ℝ :=
  setup.scaledWavelengthInMillimeters ε /
    setup.scaledMinimumDistanceRatio 1 ε

/-!
The leading-order estimator evaluated directly from the three source
measurements: `a_est = λ L / y₁`. This is a general measurement formula, not
a definition of the requested numerical answer or of the physical slit width.
-/
def inferredSlitWidthInMillimeters
    (setup : SingleSlitDiffractionSetup) : ℝ :=
  lengthInMillimeters setup.wavelength *
      lengthInMillimeters setup.screenDistanceL /
    lengthInMillimeters setup.firstMinimumDistanceFromCenter

/-- Labels of the four slit-width choices printed with the dataset item. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Millimetre value printed beside each answer label. -/
def displayedWidthInMillimeters : AnswerChoice → ℝ
  | .A => 11 / 100
  | .B => 13 / 100
  | .C => 1 / 10
  | .D => 3 / 25

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Round a millimetre readout to the nearest hundredth of a millimetre. -/
def roundedToNearestHundredth (value : ℝ) : ℝ :=
  (round (100 * value) : ℝ) / 100

/-- A displayed choice agrees with an inferred width at the shown precision. -/
def MatchesDisplayedWidth
    (widthInMillimeters : ℝ) (choice : AnswerChoice) : Prop :=
  roundedToNearestHundredth widthInMillimeters =
    displayedWidthInMillimeters choice

/-- The selected label is the unique displayed choice matching the estimate. -/
def IsUniqueMatchingDisplayedWidth
    (widthInMillimeters : ℝ) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedWidth widthInMillimeters choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedWidth widthInMillimeters other → other = choice

/-!
The source measurements give the leading-order estimate

`a_est = λ L / y₁ = 211/2000 mm = 0.1055 mm`,

which rounds to the uniquely matching displayed value `0.11 mm`, answer A.
The controlled asymptotic laws also make the estimator profile converge to the
genuine dimensionful slit width as the positive parameter tends to zero.

Crucially, the theorem does not equate the actual finite-scale slit width with
the paraxial estimate. Neither the numerical estimate, its rounding, nor
answer A occurs in a law or readout premise.

This formalizes `thm:physics:phyx_mini_0249:target`.
-/
theorem problem_phyx_mini_0249
    (setup : SingleSlitDiffractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_family : ConnectsExperimentToScaledFamily setup)
    (h_geometry : SatisfiesExactScreenRayGeometry setup)
    (h_asymptotics : SatisfiesFraunhoferParaxialAsymptotics setup) :
    inferredSlitWidthInMillimeters setup = 211 / 2000 ∧
      IsUniqueMatchingDisplayedWidth
        (inferredSlitWidthInMillimeters setup) recordedDatasetAnswer ∧
      Filter.Tendsto (widthEstimateProfileInMillimeters setup)
        smallPositiveScale
        (nhds (lengthInMillimeters setup.slitWidthA)) := by
  have wavelength_mm :
      lengthInMillimeters setup.wavelength =
        lengthInNanometers setup.wavelength / 1000000 := by
    have hscale :
        ({ UnitChoices.SI with length := LengthUnit.nanometers } :
            UnitChoices).dimScale
          ({ UnitChoices.SI with length := LengthUnit.millimeters } :
            UnitChoices) L𝓭 =
          (1 / 1000000 : NNReal) := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
        LengthUnit.millimeters, LengthUnit.scale, LengthUnit.div_eq_val]
      field_simp [LengthUnit.val_ne_zero]
      change (1000 / 1000000000 : ℝ) * 1000000 = 1
      norm_num
    have hunit := setup.wavelength.2
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
    simp only [WithDim.dim_apply] at hunit
    rw [hscale] at hunit
    have hval := congrArg WithDim.val hunit
    norm_num [lengthInMillimeters, lengthInNanometers, lengthReadout,
      NNReal.smul_def] at hval ⊢
    rw [hval]
    ring
  have meters_to_millimeters (length : OpticalLength) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    have hunit := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
    have hval := congrArg WithDim.val hunit
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.millimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hval ⊢
    exact hval
  have screenDistance_mm :
      lengthInMillimeters setup.screenDistanceL =
        1000 * lengthInMeters setup.screenDistanceL :=
    meters_to_millimeters setup.screenDistanceL
  have firstMinimumDistance_mm :
      lengthInMillimeters setup.firstMinimumDistanceFromCenter =
        10 * lengthInCentimeters setup.firstMinimumDistanceFromCenter := by
    have hscale :
        ({ UnitChoices.SI with length := LengthUnit.centimeters } :
            UnitChoices).dimScale
          ({ UnitChoices.SI with length := LengthUnit.millimeters } :
            UnitChoices) L𝓭 =
          (10 : NNReal) := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.millimeters, LengthUnit.scale, LengthUnit.div_eq_val]
      field_simp [LengthUnit.val_ne_zero]
      change (1000 / 100 : ℝ) = 10
      norm_num
    have hunit := setup.firstMinimumDistanceFromCenter.2
      ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
    simp only [WithDim.dim_apply] at hunit
    rw [hscale] at hunit
    have hval := congrArg WithDim.val hunit
    norm_num [lengthInMillimeters, lengthInCentimeters, lengthReadout,
      NNReal.smul_def] at hval ⊢
    exact hval
  have h_width :
      inferredSlitWidthInMillimeters setup = 211 / 2000 := by
    rcases h_readouts with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        h_wavelength, h_screenDistance, h_firstMinimumDistance, _⟩
    rw [inferredSlitWidthInMillimeters, wavelength_mm, screenDistance_mm,
      firstMinimumDistance_mm, h_wavelength, h_screenDistance, h_firstMinimumDistance]
    norm_num
  refine ⟨h_width, ?_, ?_⟩
  · rw [h_width]
    constructor
    · norm_num [MatchesDisplayedWidth, roundedToNearestHundredth,
        displayedWidthInMillimeters, recordedDatasetAnswer, round_eq_iff]
    · intro other h_other
      cases other
      · rfl
      all_goals
        exfalso
        norm_num [MatchesDisplayedWidth, roundedToNearestHundredth,
          displayedWidthInMillimeters, recordedDatasetAnswer, round_eq_iff] at h_other
  · let a : ℝ := lengthInMillimeters setup.slitWidthA
    let s : ℝ → ℝ := fun ε =>
      Real.Angle.sin (setup.scaledMinimumAngle 1 ε)
    let r : ℝ → ℝ := fun ε =>
      setup.scaledMinimumDistanceRatio 1 ε
    have ha_pos : 0 < a := by
      rw [show a = lengthInMillimeters setup.slitWidthA by rfl,
        meters_to_millimeters setup.slitWidthA]
      exact mul_pos (by norm_num) h_physical.2.1
    have hε_pos : ∀ᶠ ε : ℝ in smallPositiveScale, 0 < ε := by
      change ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε ∈ Set.Ioi 0
      exact self_mem_nhdsWithin
    have h_single_slit :=
      h_asymptotics.single_slit_minimum_residual 1 (by norm_num)
    have h_single_slit_scaled :
        (fun ε : ℝ => a * (s ε - ε)) =o[smallPositiveScale]
          (fun ε : ℝ => a * ε) := by
      apply h_single_slit.congr'
      · filter_upwards [hε_pos] with ε hε
        rw [h_family.wavelength_scaling ε hε.le]
        simp only [Nat.cast_one, one_mul]
        simp only [a, s]
        ring
      · filter_upwards [hε_pos] with ε hε
        rw [h_family.wavelength_scaling ε hε.le]
        simp only [a]
        ring
    have h_sin_error :
        (fun ε : ℝ => s ε - ε) =o[smallPositiveScale]
          (fun ε : ℝ => ε) := by
      have h_without_left_constant :=
        (Asymptotics.isLittleO_const_mul_left_iff ha_pos.ne').mp
          h_single_slit_scaled
      exact
        (Asymptotics.isLittleO_const_mul_right_iff ha_pos.ne').mp
          h_without_left_constant
    have h_sin_bigO :
        s =O[smallPositiveScale] (fun ε : ℝ => ε) := by
      have h := h_sin_error.add_isBigO
        (Asymptotics.isBigO_refl (fun ε : ℝ => ε) smallPositiveScale)
      simpa only [sub_add_cancel] using h
    have h_projection :=
      h_asymptotics.paraxial_projection_residual 1 (by norm_num)
    have h_projection_error :
        (fun ε : ℝ => r ε - s ε) =o[smallPositiveScale]
          (fun ε : ℝ => ε) := by
      apply h_projection.trans_isBigO h_sin_bigO
    have h_ratio_error :
        (fun ε : ℝ => r ε - ε) =o[smallPositiveScale]
          (fun ε : ℝ => ε) := by
      have h := h_projection_error.add h_sin_error
      apply h.congr_left
      intro ε
      ring
    have h_ratio_error_tendsto :
        Filter.Tendsto (fun ε : ℝ => r ε / ε - 1)
          smallPositiveScale (nhds 0) := by
      apply h_ratio_error.tendsto_div_nhds_zero.congr'
      filter_upwards [hε_pos] with ε hε
      field_simp [hε.ne']
    have h_ratio :
        Filter.Tendsto (fun ε : ℝ => r ε / ε)
          smallPositiveScale (nhds 1) := by
      simpa only [sub_add_cancel, zero_add] using
        h_ratio_error_tendsto.add_const 1
    have h_estimator :
        Filter.Tendsto (fun ε : ℝ => a / (r ε / ε))
          smallPositiveScale (nhds a) := by
      have h_constant :
          Filter.Tendsto (fun _ : ℝ => a) smallPositiveScale (nhds a) :=
        tendsto_const_nhds
      simpa only [Pi.div_def, div_one] using
        h_constant.div h_ratio (by norm_num : (1 : ℝ) ≠ 0)
    apply h_estimator.congr'
    filter_upwards [hε_pos] with ε hε
    rw [widthEstimateProfileInMillimeters,
      h_family.wavelength_scaling ε hε.le]
    change a / (r ε / ε) = ε * a / r ε
    rw [div_div_eq_mul_div]
    ring

end PhyXMiniProblems.ProblemPhyXMini0249
