import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Optics.Basic

/-!
# Dispersion of white light through a 30-degree prism

This file formalizes the geometry and optical laws in `phyx_mini_0073`.
Angles use Mathlib's `Real.Angle`; refractive indices and displayed degree
values are dimensionless real readouts.  Physlib's optics module is currently
a placeholder, so the problem-specific prism and Snell-law interfaces are
stated explicitly below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0073

/-- Convert a degree readout to its real radian representative. -/
def radiansOfDegrees (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- Convert a degree readout to Mathlib's type of angles modulo one turn. -/
def angleOfDegrees (angleDegrees : ℝ) : Real.Angle :=
  (radiansOfDegrees angleDegrees : Real.Angle)

/-- Principal degree readout of an angle, used to compare answer choices. -/
def degreesOfAngle (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- The two spectral components singled out by the dispersion diagram. -/
inductive SpectralColor where
  | red
  | violet
  deriving DecidableEq, Repr

/-- The two homogeneous optical media traversed by each colored ray. -/
inductive OpticalMedium where
  | ambientAir
  | prismGlass
  deriving DecidableEq, Repr

/--
The physical quantities and named angles in the prism figure.

The incident white ray has one common entrance incidence angle.  Dispersion in
the glass gives color-dependent internal and emerging angles.  The field
`incidentRayToEntranceFace` is the angle marked `40°` between the incoming ray
and the entrance *face*.  All other path angles are measured from the indicated
face normal.  In particular, the red value of `emergenceFromRearNormal` is the
figure's unknown `φ`, since the violet ray follows that normal.
-/
structure DispersivePrismSetup where
  /-- Angle between the entrance and rear prism faces, labelled `30°`. -/
  apexAngle : Real.Angle
  /-- Figure's `40°` readout between the white ray and the entrance face. -/
  incidentRayToEntranceFace : Real.Angle
  /-- Dimensionless refractive-index readout, dependent on medium and color. -/
  refractiveIndexDimensionless : OpticalMedium → SpectralColor → ℝ
  /-- Common incidence angle of the incoming white ray from the entrance normal. -/
  entranceIncidenceFromNormal : Real.Angle
  /-- Internal angle after entry, measured from the entrance-face inward normal. -/
  entranceRefractionFromNormal : SpectralColor → Real.Angle
  /-- Internal incidence magnitude at the rear face, measured from its normal. -/
  rearIncidenceFromNormal : SpectralColor → Real.Angle
  /-- Emerging angle in air measured from the outward rear-face normal. -/
  emergenceFromRearNormal : SpectralColor → Real.Angle

/-- An angle lies on the principal geometrical-optics branch. -/
def IsPrincipalOpticalAngle (angle : Real.Angle) : Prop :=
  angle.toReal ∈ Set.Icc 0 (Real.pi / 2)

/--
Positivity and branch information for the physical optical data.  These
conditions make the normal-referenced sine equations select physical angles.
-/
structure HasPhysicalOpticalParameters (setup : DispersivePrismSetup) : Prop where
  apexAnglePhysical : IsPrincipalOpticalAngle setup.apexAngle
  faceMarkedAnglePhysical :
    IsPrincipalOpticalAngle setup.incidentRayToEntranceFace
  entranceIncidencePhysical :
    IsPrincipalOpticalAngle setup.entranceIncidenceFromNormal
  entranceRefractionPhysical :
    ∀ color, IsPrincipalOpticalAngle (setup.entranceRefractionFromNormal color)
  rearIncidencePhysical :
    ∀ color, IsPrincipalOpticalAngle (setup.rearIncidenceFromNormal color)
  emergencePhysical :
    ∀ color, IsPrincipalOpticalAngle (setup.emergenceFromRearNormal color)
  refractiveIndexPositive :
    ∀ medium color, 0 < setup.refractiveIndexDimensionless medium color
  glassIndexExceedsAir :
    ∀ color,
      setup.refractiveIndexDimensionless .ambientAir color <
        setup.refractiveIndexDimensionless .prismGlass color

/--
Numerical and figure-derived data supplied by the problem.  The image makes
the `40°` mark face-referenced; its complementary normal-referenced incidence
is imposed separately by prism geometry.  No red emergence value occurs here.
-/
structure MatchesProblemAndFigureData (setup : DispersivePrismSetup) : Prop where
  apexAngleReadout : setup.apexAngle = angleOfDegrees 30
  incidentFaceAngleReadout :
    setup.incidentRayToEntranceFace = angleOfDegrees 40
  airIndexReadout :
    ∀ color, setup.refractiveIndexDimensionless .ambientAir color = 1
  violetIndexTwoPercentLarger :
    setup.refractiveIndexDimensionless .prismGlass .violet =
      (102 / 100 : ℝ) * setup.refractiveIndexDimensionless .prismGlass .red
  violetEmergesNormally :
    setup.emergenceFromRearNormal .violet = 0

/--
The angle relations determined by the triangular figure.  The face-marked
entrance angle and normal-referenced incidence are complementary.  On the
depicted branch, the red internal ray is just above the rear-face normal, so
its entrance-normal angle is the apex angle plus its rear incidence magnitude;
the same equation specializes to zero rear incidence for violet.
-/
structure SatisfiesPrismGeometry (setup : DispersivePrismSetup) : Prop where
  entranceFaceNormalComplement :
    setup.incidentRayToEntranceFace +
        setup.entranceIncidenceFromNormal =
      angleOfDegrees 90
  internalAnglesFromFaceNormals :
    ∀ color,
      setup.entranceRefractionFromNormal color =
        setup.apexAngle + setup.rearIncidenceFromNormal color

/--
Snell's law `n₁ sin θ₁ = n₂ sin θ₂` at the air--glass entrance for
one spectral component of the incident white light.
-/
def SatisfiesEntranceSnellLaw
    (setup : DispersivePrismSetup) (color : SpectralColor) : Prop :=
  setup.refractiveIndexDimensionless .ambientAir color *
      Real.Angle.sin setup.entranceIncidenceFromNormal =
    setup.refractiveIndexDimensionless .prismGlass color *
      Real.Angle.sin (setup.entranceRefractionFromNormal color)

/-- Snell's law at the glass--air rear face for one spectral component. -/
def SatisfiesRearFaceSnellLaw
    (setup : DispersivePrismSetup) (color : SpectralColor) : Prop :=
  setup.refractiveIndexDimensionless .prismGlass color *
      Real.Angle.sin (setup.rearIncidenceFromNormal color) =
    setup.refractiveIndexDimensionless .ambientAir color *
      Real.Angle.sin (setup.emergenceFromRearNormal color)

/-- Both red and violet obey Snell's law at both prism faces. -/
structure ObeysSnellLaw (setup : DispersivePrismSetup) : Prop where
  atEntrance : ∀ color, SatisfiesEntranceSnellLaw setup color
  atRearFace : ∀ color, SatisfiesRearFaceSnellLaw setup color

/-- The figure label `φ`: red light's emergence angle from the rear-face normal. -/
def phi (setup : DispersivePrismSetup) : Real.Angle :=
  setup.emergenceFromRearNormal .red

/-- The answer-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The whole-degree angle printed next to each answer choice. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 3
  | .B => 9
  | .C => 1
  | .D => 2

/-- Dataset metadata recording answer C; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A computed angle rounds to the displayed whole-degree choice. -/
def RoundsToAnswerChoice (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreesOfAngle angle - choice.angleDegrees| < 1 / 2

/-- Angular error between `φ` and one displayed answer, measured in radians. -/
def answerChoiceErrorRadians
    (setup : DispersivePrismSetup) (choice : AnswerChoice) : ℝ :=
  |(phi setup).toReal - radiansOfDegrees choice.angleDegrees|

/-- A choice is strictly closer to `φ` than each of the other displayed angles. -/
def IsUniqueClosestAnswerChoice
    (setup : DispersivePrismSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorRadians setup choice < answerChoiceErrorRadians setup other

/--
For the depicted `30°` prism and face-referenced `40°` incident ray, normal
violet emergence fixes the violet index.  Since that index is `2.0%` larger
than red's, Snell's law at both faces makes the red emergence angle `φ` round
to `1°`, and C is the unique closest displayed answer.

Blueprint: `thm:physics:phyx_mini_0073:target`.
-/
theorem redLightEmergenceAngle_is_choiceC
    (setup : DispersivePrismSetup)
    (hFigure : MatchesProblemAndFigureData setup)
    (hPhysical : HasPhysicalOpticalParameters setup)
    (hGeometry : SatisfiesPrismGeometry setup)
    (hSnell : ObeysSnellLaw setup) :
    RoundsToAnswerChoice (phi setup) .C ∧
      IsUniqueClosestAnswerChoice setup .C := by
  have hPiLower : (3 : ℝ) < Real.pi := by
    have hbound := Real.sin_bound (x := (1 / 2 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_le] at hbound
    have hsinHalf : Real.sin (1 / 2 : ℝ) < 1 / 2 := by
      norm_num at hbound ⊢
      linarith
    by_contra h
    have hle : Real.sin (Real.pi / 6) ≤ Real.sin (1 / 2) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · linarith [Real.two_le_pi]
      · linarith
    rw [Real.sin_pi_div_six] at hle
    linarith
  have hAngle30 :
      angleOfDegrees 30 = ((Real.pi / 6 : ℝ) : Real.Angle) := by
    change
      ((30 * Real.pi / 180 : ℝ) : Real.Angle) =
        ((Real.pi / 6 : ℝ) : Real.Angle)
    congr 1
    ring
  have hAngle40 :
      angleOfDegrees 40 = ((2 * Real.pi / 9 : ℝ) : Real.Angle) := by
    change
      ((40 * Real.pi / 180 : ℝ) : Real.Angle) =
        ((2 * Real.pi / 9 : ℝ) : Real.Angle)
    congr 1
    ring
  have hAngle50 :
      angleOfDegrees 50 = ((5 * Real.pi / 18 : ℝ) : Real.Angle) := by
    change
      ((50 * Real.pi / 180 : ℝ) : Real.Angle) =
        ((5 * Real.pi / 18 : ℝ) : Real.Angle)
    congr 1
    ring
  have hAngle90 :
      angleOfDegrees 90 = ((Real.pi / 2 : ℝ) : Real.Angle) := by
    change
      ((90 * Real.pi / 180 : ℝ) : Real.Angle) =
        ((Real.pi / 2 : ℝ) : Real.Angle)
    congr 1
    ring
  have hEntranceIncidence :
      setup.entranceIncidenceFromNormal = angleOfDegrees 50 := by
    calc
      setup.entranceIncidenceFromNormal =
          (setup.incidentRayToEntranceFace +
              setup.entranceIncidenceFromNormal) -
            setup.incidentRayToEntranceFace := by abel
      _ = angleOfDegrees 90 - angleOfDegrees 40 := by
        rw [hGeometry.entranceFaceNormalComplement,
          hFigure.incidentFaceAngleReadout]
      _ = angleOfDegrees 50 := by
        rw [hAngle90, hAngle40, hAngle50, ← Real.Angle.coe_sub]
        congr 1
        ring
  have hRearVioletSin :
      Real.Angle.sin (setup.rearIncidenceFromNormal .violet) = 0 := by
    have h := hSnell.atRearFace .violet
    simp only [SatisfiesRearFaceSnellLaw] at h
    rw [hFigure.airIndexReadout .violet,
      hFigure.violetEmergesNormally, Real.Angle.sin_zero, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left
      (ne_of_gt
        (hPhysical.refractiveIndexPositive .prismGlass .violet))
  have hRearVioletReal :
      (setup.rearIncidenceFromNormal .violet).toReal = 0 := by
    apply Real.injOn_sin
      (show
        (setup.rearIncidenceFromNormal .violet).toReal ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        have h := hPhysical.rearIncidencePhysical .violet
        exact ⟨by linarith [h.1, Real.pi_pos], h.2⟩)
      (show (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
    simpa only [Real.Angle.sin_toReal, Real.sin_zero] using hRearVioletSin
  have hRearViolet :
      setup.rearIncidenceFromNormal .violet = 0 :=
    Real.Angle.toReal_eq_zero_iff.mp hRearVioletReal
  have hRefractionViolet :
      setup.entranceRefractionFromNormal .violet =
        setup.apexAngle := by
    rw [hGeometry.internalAnglesFromFaceNormals .violet, hRearViolet,
      add_zero]
  have hVioletIndex :
      setup.refractiveIndexDimensionless .prismGlass .violet =
        2 * Real.Angle.sin setup.entranceIncidenceFromNormal := by
    have h := hSnell.atEntrance .violet
    simp only [SatisfiesEntranceSnellLaw] at h
    rw [hFigure.airIndexReadout .violet, one_mul, hRefractionViolet,
      hFigure.apexAngleReadout, hAngle30, Real.Angle.sin_coe,
      Real.sin_pi_div_six] at h
    linarith only [h]
  have hRedRefractionSin :
      Real.Angle.sin (setup.entranceRefractionFromNormal .red) =
        (51 / 100 : ℝ) := by
    have hRed := hSnell.atEntrance .red
    simp only [SatisfiesEntranceSnellLaw] at hRed
    rw [hFigure.airIndexReadout .red, one_mul] at hRed
    have hIndexPositive :=
      hPhysical.refractiveIndexPositive .prismGlass .red
    have hDispersion := hFigure.violetIndexTwoPercentLarger
    norm_num at hDispersion ⊢
    have hProduct :
        setup.refractiveIndexDimensionless .prismGlass .red *
            (2 * Real.Angle.sin
              (setup.entranceRefractionFromNormal .red)) =
          setup.refractiveIndexDimensionless .prismGlass .red *
            (51 / 50 : ℝ) := by
      calc
        setup.refractiveIndexDimensionless .prismGlass .red *
            (2 * Real.Angle.sin
              (setup.entranceRefractionFromNormal .red)) =
            2 * (setup.refractiveIndexDimensionless .prismGlass .red *
              Real.Angle.sin
                (setup.entranceRefractionFromNormal .red)) := by ring
        _ = 2 * Real.Angle.sin
            setup.entranceIncidenceFromNormal := by rw [← hRed]
        _ =
            setup.refractiveIndexDimensionless .prismGlass .violet :=
          hVioletIndex.symm
        _ = (51 / 50 : ℝ) *
            setup.refractiveIndexDimensionless .prismGlass .red :=
          hDispersion
        _ = setup.refractiveIndexDimensionless .prismGlass .red *
            (51 / 50 : ℝ) := by ring
    have hCancel :=
      mul_left_cancel₀ (ne_of_gt hIndexPositive) hProduct
    linarith only [hCancel]
  let x : ℝ := (setup.rearIncidenceFromNormal .red).toReal
  have hxPhysical : x ∈ Set.Icc 0 (Real.pi / 2) :=
    hPhysical.rearIncidencePhysical .red
  have hApex :
      setup.apexAngle = ((Real.pi / 6 : ℝ) : Real.Angle) := by
    rw [hFigure.apexAngleReadout, hAngle30]
  have hRefractionReal :
      (setup.entranceRefractionFromNormal .red).toReal =
        Real.pi / 6 + x := by
    rw [hGeometry.internalAnglesFromFaceNormals .red, hApex]
    rw [← Real.Angle.coe_toReal (setup.rearIncidenceFromNormal .red),
      ← Real.Angle.coe_add]
    apply Real.Angle.toReal_coe_eq_self_iff.mpr
    have hxNonnegative :
        0 ≤ (setup.rearIncidenceFromNormal .red).toReal :=
      (hPhysical.rearIncidencePhysical .red).1
    have hxAtMostHalfPi :
        (setup.rearIncidenceFromNormal .red).toReal ≤ Real.pi / 2 :=
      (hPhysical.rearIncidencePhysical .red).2
    constructor
    · linarith [Real.pi_pos]
    · linarith [hxAtMostHalfPi, hPiLower]
  have hxSumUpper : Real.pi / 6 + x ≤ Real.pi / 2 := by
    rw [← hRefractionReal]
    exact (hPhysical.entranceRefractionPhysical .red).2
  have hSinXEquation :
      Real.sin (Real.pi / 6 + x) = (51 / 100 : ℝ) := by
    calc
      Real.sin (Real.pi / 6 + x) =
          Real.Angle.sin
            (((Real.pi / 6 + x : ℝ) : Real.Angle)) := by
              rw [Real.Angle.sin_coe]
      _ = Real.Angle.sin
          (((Real.pi / 6 : ℝ) : Real.Angle) +
            setup.rearIncidenceFromNormal .red) := by
              rw [Real.Angle.coe_add, Real.Angle.coe_toReal]
      _ = Real.Angle.sin
          (setup.entranceRefractionFromNormal .red) := by
              rw [← hApex,
                ← hGeometry.internalAnglesFromFaceNormals .red]
      _ = (51 / 100 : ℝ) := hRedRefractionSin
  have hSmallSinUpper :
      Real.sin (Real.pi / 360) < Real.pi / 360 := by
    have hargPos : 0 < Real.pi / 360 := by positivity
    have hargLe : |Real.pi / 360| ≤ 1 := by
      rw [abs_of_pos hargPos]
      linarith [Real.pi_le_four]
    have hbound := abs_le.mp (Real.sin_bound hargLe)
    rw [abs_of_pos hargPos] at hbound
    have hargFourth :
        (Real.pi / 360) ^ 4 * (5 / 96 : ℝ) <
          (Real.pi / 360) ^ 3 / 6 := by
      have hargUpper : Real.pi / 360 < (1 : ℝ) := by
        linarith [Real.pi_le_four]
      calc
        (Real.pi / 360) ^ 4 * (5 / 96 : ℝ) =
            (Real.pi / 360) ^ 3 *
              ((Real.pi / 360) * (5 / 96 : ℝ)) := by ring
        _ < (Real.pi / 360) ^ 3 * (1 / 6 : ℝ) :=
          mul_lt_mul_of_pos_left
            (by linarith only [hargUpper])
            (pow_pos hargPos 3)
        _ = (Real.pi / 360) ^ 3 / 6 := by ring
    linarith only [hbound.2, hargFourth]
  have hSinLowerComparison :
      Real.sin (Real.pi / 6 + Real.pi / 360) <
        (51 / 100 : ℝ) := by
    rw [Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
    have hcosLe := Real.cos_le_one (Real.pi / 360)
    have hsqrtUpper : Real.sqrt 3 / 2 < (7 / 8 : ℝ) := by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      norm_num
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7 / 4)]
      norm_num
    have hsinPos : 0 < Real.sin (Real.pi / 360) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith only [Real.pi_pos]
    have hproduct :
        Real.sqrt 3 / 2 * Real.sin (Real.pi / 360) <
          (7 / 8 : ℝ) * (Real.pi / 360) :=
      mul_lt_mul hsqrtUpper hSmallSinUpper.le hsinPos
        (by norm_num)
    linarith only [hcosLe, hproduct, Real.pi_le_four]
  have hxLower : Real.pi / 360 < x := by
    by_contra h
    have hle :
        Real.sin (Real.pi / 6 + x) ≤
          Real.sin (Real.pi / 6 + Real.pi / 360) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos, hxPhysical.1]
      · linarith [Real.pi_le_four, Real.two_le_pi]
      · linarith
    rw [hSinXEquation] at hle
    linarith
  have hSinThreeHundredSixtiethPositive :
      0 < Real.sin (Real.pi / 360) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith only [Real.pi_pos]
  have hDeltaBounds :
      Real.pi / 240 ∈ Set.Icc (1 / 80 : ℝ) (1 / 60 : ℝ) := by
    constructor
    · linarith
    · linarith [Real.pi_le_four]
  have hSinDeltaLower :
      (2499 / 200000 : ℝ) < Real.sin (Real.pi / 240) := by
    have hargPos : 0 < Real.pi / 240 := by positivity
    have hargLe : |Real.pi / 240| ≤ 1 := by
      rw [abs_of_pos hargPos]
      linarith [hDeltaBounds.2]
    have hbound := abs_le.mp (Real.sin_bound hargLe)
    rw [abs_of_pos hargPos] at hbound
    have hargCubeLower :
        (1 / 80 : ℝ) ^ 3 ≤ (Real.pi / 240) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hDeltaBounds.1 3
    have hargCubeUpper :
        (Real.pi / 240) ^ 3 ≤ (1 / 60 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hDeltaBounds.2 3
    have hargFourthUpper :
        (Real.pi / 240) ^ 4 ≤ (1 / 60 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hDeltaBounds.2 4
    norm_num at hargCubeLower hargCubeUpper hargFourthUpper ⊢
    linarith only [hbound.1, hargCubeLower, hargCubeUpper,
      hargFourthUpper, hDeltaBounds.1]
  have hCosDeltaLower :
      (999 / 1000 : ℝ) < Real.cos (Real.pi / 240) := by
    have hargPos : 0 < Real.pi / 240 := by positivity
    have hargLe : |Real.pi / 240| ≤ 1 := by
      rw [abs_of_pos hargPos]
      linarith [hDeltaBounds.2]
    have hbound := abs_le.mp (Real.cos_bound hargLe)
    rw [abs_of_pos hargPos] at hbound
    have hargSquareUpper :
        (Real.pi / 240) ^ 2 ≤ (1 / 60 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hDeltaBounds.2 2
    have hargFourthUpper :
        (Real.pi / 240) ^ 4 ≤ (1 / 60 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hDeltaBounds.2 4
    norm_num at hargSquareUpper hargFourthUpper ⊢
    linarith only [hbound.1, hargSquareUpper, hargFourthUpper]
  have hSinUpperComparison :
      (51 / 100 : ℝ) <
        Real.sin (Real.pi / 6 + Real.pi / 240) := by
    rw [Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
    have hsqrtLower : (17 / 20 : ℝ) < Real.sqrt 3 / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      norm_num
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 17 / 10)]
      norm_num
    have hproduct :
        (17 / 20 : ℝ) * (2499 / 200000 : ℝ) <
          Real.sqrt 3 / 2 * Real.sin (Real.pi / 240) :=
      mul_lt_mul hsqrtLower hSinDeltaLower.le (by norm_num)
        (by positivity)
    linarith only [hproduct, hCosDeltaLower]
  have hxUpper : x < Real.pi / 240 := by
    by_contra h
    have hle :
        Real.sin (Real.pi / 6 + Real.pi / 240) ≤
          Real.sin (Real.pi / 6 + x) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · exact hxSumUpper
      · linarith
    rw [hSinXEquation] at hle
    linarith
  clear hPiLower hAngle30 hAngle40 hAngle50 hAngle90
    hEntranceIncidence hRearVioletSin hRearVioletReal hRearViolet
    hRefractionViolet hRedRefractionSin hApex hRefractionReal
    hxSumUpper hSinXEquation hSmallSinUpper hSinLowerComparison
    hSinThreeHundredSixtiethPositive hDeltaBounds hSinDeltaLower
    hSinUpperComparison hGeometry
  have hRedIndexLower :
      1 < setup.refractiveIndexDimensionless .prismGlass .red := by
    rw [← hFigure.airIndexReadout .red]
    exact hPhysical.glassIndexExceedsAir .red
  have hRedIndexUpper :
      setup.refractiveIndexDimensionless .prismGlass .red <
        (99 / 50 : ℝ) := by
    have hDispersion := hFigure.violetIndexTwoPercentLarger
    have hSinAtMostOne :
        Real.Angle.sin setup.entranceIncidenceFromNormal ≤ 1 := by
      rw [← Real.Angle.sin_toReal]
      exact Real.sin_le_one _
    norm_num at hDispersion
    linarith only [hDispersion, hVioletIndex, hSinAtMostOne]
  let y : ℝ := (phi setup).toReal
  have hyPhysical : y ∈ Set.Icc 0 (Real.pi / 2) :=
    hPhysical.emergencePhysical .red
  have hRearSnellReal :
      Real.sin y =
        setup.refractiveIndexDimensionless .prismGlass .red *
          Real.sin x := by
    have h := hSnell.atRearFace .red
    simp only [SatisfiesRearFaceSnellLaw] at h
    rw [hFigure.airIndexReadout .red, one_mul] at h
    dsimp [x, y, phi]
    simpa only [Real.Angle.sin_toReal] using h.symm
  clear hFigure hPhysical hSnell hVioletIndex
  have hSinXPositive : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact (by positivity : 0 < Real.pi / 360).trans hxLower
    · linarith [hxPhysical.2, Real.pi_pos]
  have hyLower : Real.pi / 360 < y := by
    have hsinYX : Real.sin x < Real.sin y := by
      rw [hRearSnellReal]
      exact lt_mul_of_one_lt_left hSinXPositive hRedIndexLower
    have hxy : x < y := by
      by_contra h
      have hle : Real.sin y ≤ Real.sin x := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · linarith [Real.pi_pos, hyPhysical.1]
        · exact hxPhysical.2
        · linarith
      linarith
    exact hxLower.trans hxy
  have hSinXUpper :
      Real.sin x < Real.sin (Real.pi / 240) := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · linarith [Real.pi_pos, hxPhysical.1]
    · linarith [Real.pi_le_four, Real.two_le_pi]
    · exact hxUpper
  have hSinDoubleDelta :
      Real.sin (Real.pi / 120) =
        2 * Real.sin (Real.pi / 240) *
          Real.cos (Real.pi / 240) := by
    rw [show Real.pi / 120 = 2 * (Real.pi / 240) by ring,
      Real.sin_two_mul]
  have hSinPhiUpper :
      Real.sin y < Real.sin (Real.pi / 120) := by
    rw [hRearSnellReal, hSinDoubleDelta]
    have hsinDeltaPos : 0 < Real.sin (Real.pi / 240) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith only [Real.pi_pos]
    have hleft :
        setup.refractiveIndexDimensionless .prismGlass .red *
            Real.sin x <
          (99 / 50 : ℝ) * Real.sin (Real.pi / 240) :=
      mul_lt_mul hRedIndexUpper hSinXUpper.le hSinXPositive
        (by norm_num)
    have hright :
        (99 / 50 : ℝ) * Real.sin (Real.pi / 240) <
          2 * Real.sin (Real.pi / 240) *
            Real.cos (Real.pi / 240) := by
      have hCoefficient :
          (99 / 50 : ℝ) <
            2 * Real.cos (Real.pi / 240) := by
        linarith only [hCosDeltaLower]
      calc
        (99 / 50 : ℝ) * Real.sin (Real.pi / 240) =
            Real.sin (Real.pi / 240) * (99 / 50 : ℝ) := by ring
        _ < Real.sin (Real.pi / 240) *
            (2 * Real.cos (Real.pi / 240)) :=
          mul_lt_mul_of_pos_left hCoefficient hsinDeltaPos
        _ = 2 * Real.sin (Real.pi / 240) *
            Real.cos (Real.pi / 240) := by ring
    exact hleft.trans hright
  have hyUpper : y < Real.pi / 120 := by
    by_contra h
    have hle :
        Real.sin (Real.pi / 120) ≤ Real.sin y := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · exact hyPhysical.2
      · linarith
    linarith
  have hDegreesLower : (1 / 2 : ℝ) < degreesOfAngle (phi setup) := by
    dsimp [degreesOfAngle, y] at ⊢
    rw [lt_div_iff₀ Real.pi_pos]
    linarith only [hyLower]
  have hDegreesUpper : degreesOfAngle (phi setup) < (3 / 2 : ℝ) := by
    dsimp [degreesOfAngle, y] at ⊢
    rw [div_lt_iff₀ Real.pi_pos]
    linarith only [hyUpper]
  have hChoiceCError :
      |(phi setup).toReal - (1 : ℝ) * Real.pi / 180| <
        Real.pi / 360 := by
    rw [abs_lt]
    dsimp [y] at hyLower hyUpper
    constructor <;> linarith only [hyLower, hyUpper]
  constructor
  · unfold RoundsToAnswerChoice
    simp only [AnswerChoice.angleDegrees]
    rw [abs_lt]
    constructor <;> linarith
  · intro other hOther
    unfold answerChoiceErrorRadians phi radiansOfDegrees
    cases other with
    | A =>
        simp only [AnswerChoice.angleDegrees]
        change
          |(phi setup).toReal - (1 : ℝ) * Real.pi / 180| <
            |(phi setup).toReal - (3 : ℝ) * Real.pi / 180|
        have hSign :
            (phi setup).toReal - (3 : ℝ) * Real.pi / 180 ≤ 0 := by
          dsimp [y] at hyUpper ⊢
          linarith only [hyUpper, Real.pi_pos]
        rw [abs_of_nonpos hSign]
        exact hChoiceCError.trans (by
          dsimp [y] at hyUpper ⊢
          linarith only [hyUpper, Real.pi_pos])
    | B =>
        simp only [AnswerChoice.angleDegrees]
        change
          |(phi setup).toReal - (1 : ℝ) * Real.pi / 180| <
            |(phi setup).toReal - (9 : ℝ) * Real.pi / 180|
        have hSign :
            (phi setup).toReal - (9 : ℝ) * Real.pi / 180 ≤ 0 := by
          dsimp [y] at hyUpper ⊢
          linarith only [hyUpper, Real.pi_pos]
        rw [abs_of_nonpos hSign]
        exact hChoiceCError.trans (by
          dsimp [y] at hyUpper ⊢
          linarith only [hyUpper, Real.pi_pos])
    | C => exact (hOther rfl).elim
    | D =>
        simp only [AnswerChoice.angleDegrees]
        change
          |(phi setup).toReal - (1 : ℝ) * Real.pi / 180| <
            |(phi setup).toReal - (2 : ℝ) * Real.pi / 180|
        have hSign :
            (phi setup).toReal - (2 : ℝ) * Real.pi / 180 ≤ 0 := by
          dsimp [y] at hyUpper ⊢
          linarith only [hyUpper, Real.pi_pos]
        rw [abs_of_nonpos hSign]
        exact hChoiceCError.trans (by
          dsimp [y] at hyUpper ⊢
          linarith only [hyUpper, Real.pi_pos])

end PhyXMiniProblems.ProblemPhyXMini0073
