import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Optics.Basic

/-!
# PhyX mini problem 0146: emergence from an equilateral glass prism

The primary image shows an incident ray, an internal refracted ray, and an
emergent ray crossing the two sloping faces of an equilateral prism.  Dashed
normals are drawn at both interfaces.  The entry angle from the first normal is
labelled `45.0°`; the exit angle from the second normal is marked `?`.

Physical angles are represented by Mathlib's `Real.Angle`.  Refractive indices
and displayed degree values are dimensionless real readouts.  The installed
Physlib optics module is imported as the domain-specific library boundary; it
is currently a placeholder and does not yet supply media, refractive indices,
or Snell's law.  Those missing physical roles are therefore modeled explicitly
below.  Figure data, physical branch conditions, prism geometry, Snell's law,
and the requested multiple-choice conclusion are kept separate.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0146

/-! ## Units and labelled physical roles -/

/-- Convert a scalar degree readout to a physical angle. -/
def angleFromDegrees (angleDegrees : ℝ) : Real.Angle :=
  ((angleDegrees * Real.pi / 180 : ℝ) : Real.Angle)

/-- Principal degree readout of a physical angle. -/
def angleDegreesReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- The two homogeneous optical media traversed by the ray. -/
inductive OpticalMedium where
  | air
  | glass
  deriving DecidableEq, Repr

/-- The two sloping prism faces crossed by the light ray. -/
inductive PrismInterface where
  | entryFace
  | exitFace
  deriving DecidableEq, Repr

/-- The three directed portions of the light path visible in the image. -/
inductive RaySegment where
  | incident
  | insidePrism
  | emergent
  deriving DecidableEq, Repr

/-- The two normal-referenced angle labels in the primary image. -/
inductive FigureAngleLabel where
  | entryFortyFive
  | exitQuestion
  deriving DecidableEq, Repr

/-- Medium containing the ray immediately before each interface crossing. -/
def incidentMedium : PrismInterface → OpticalMedium
  | .entryFace => .air
  | .exitFace => .glass

/-- Medium containing the ray immediately after each interface crossing. -/
def transmittedMedium : PrismInterface → OpticalMedium
  | .entryFace => .glass
  | .exitFace => .air

/-! ## Diagram data and physical admissibility -/

/--
The physical quantities attached to the labelled equilateral-prism diagram.

At each face, `incidenceAngle` is measured from the dashed normal on the
incident side and `refractionAngle` from that normal on the transmitted side.
Thus the exit-face refraction angle is the emergence angle requested by the
problem.
-/
structure EquilateralGlassPrismDiagram where
  /-- Dimensionless refractive-index readout for each medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Normal-referenced incident angle at each crossed face. -/
  incidenceAngle : PrismInterface → Real.Angle
  /-- Normal-referenced transmitted angle at each crossed face. -/
  refractionAngle : PrismInterface → Real.Angle
  /-- Interior angle between the two refracting faces. -/
  apexAngle : Real.Angle
  /-- Physical angle denoted by each visible figure label. -/
  angleForLabel : FigureAngleLabel → Real.Angle
  /-- Whether a named portion of the ray is shown in the primary image. -/
  raySegmentDepicted : RaySegment → Prop
  /-- Whether the dashed interface normal is shown at a crossed face. -/
  dashedNormalDepicted : PrismInterface → Prop

/--
Primary-image readouts and numerical data stated in the problem.  In
particular, this does not assign a numerical value to the exit question mark.
-/
structure MatchesProblemData
    (diagram : EquilateralGlassPrismDiagram) : Prop where
  allRaySegmentsDepicted : ∀ segment, diagram.raySegmentDepicted segment
  bothDashedNormalsDepicted :
    ∀ interface, diagram.dashedNormalDepicted interface
  equilateralApexReadout : diagram.apexAngle = angleFromDegrees 60
  entryLabelIsIncidenceAngle :
    diagram.angleForLabel .entryFortyFive =
      diagram.incidenceAngle .entryFace
  entryAngleReadout :
    diagram.angleForLabel .entryFortyFive = angleFromDegrees 45
  questionMarkIsEmergenceAngle :
    diagram.angleForLabel .exitQuestion =
      diagram.refractionAngle .exitFace
  glassIndexReadout : diagram.refractiveIndex .glass = 154 / 100
  airIndexCalibration : diagram.refractiveIndex .air = 1

/-- An angle on the acute principal branch used by the depicted ray. -/
def IsPhysicalRayAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal < Real.pi / 2

/-- Positivity and principal-branch conditions for the optical quantities. -/
structure HasPhysicalOpticalParameters
    (diagram : EquilateralGlassPrismDiagram) : Prop where
  refractiveIndicesPositive :
    ∀ medium, 0 < diagram.refractiveIndex medium
  incidenceAnglesPhysical :
    ∀ interface, IsPhysicalRayAngle (diagram.incidenceAngle interface)
  refractionAnglesPhysical :
    ∀ interface, IsPhysicalRayAngle (diagram.refractionAngle interface)

/-! ## Governing prism geometry and optics -/

/--
Standard prism geometry for the internal ray: its refraction angle at entry
and incidence angle at exit add to the angle between the refracting faces.
-/
structure SatisfiesPrismRayGeometry
    (diagram : EquilateralGlassPrismDiagram) : Prop where
  internalAnglesSumToApex :
    diagram.refractionAngle .entryFace +
        diagram.incidenceAngle .exitFace =
      diagram.apexAngle

/-- Snell's law `n₁ sin θ₁ = n₂ sin θ₂` at one crossed prism face. -/
def SatisfiesSnellsLawAt
    (diagram : EquilateralGlassPrismDiagram)
    (interface : PrismInterface) : Prop :=
  diagram.refractiveIndex (incidentMedium interface) *
      Real.Angle.sin (diagram.incidenceAngle interface) =
    diagram.refractiveIndex (transmittedMedium interface) *
      Real.Angle.sin (diagram.refractionAngle interface)

/-- The depicted ray obeys Snell's law at both prism faces. -/
structure ObeysSnellsLaw
    (diagram : EquilateralGlassPrismDiagram) : Prop where
  atInterface : ∀ interface, SatisfiesSnellsLawAt diagram interface

/-! ## Multiple-choice target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Emergence-angle readout in degrees printed beside each answer choice. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 662 / 10
  | .B => 462 / 10
  | .C => 562 / 10
  | .D => 762 / 10

/-- A physical angle rounds to a displayed degree value to the nearest tenth. -/
def RoundsToNearestTenthDegree
    (angle : Real.Angle) (displayedDegrees : ℝ) : Prop :=
  |angleDegreesReadout angle - displayedDegrees| < 1 / 20

/-- A choice is strictly nearer to the physical angle than every other choice. -/
def IsUniqueNearestAnswerChoice
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |angleDegreesReadout angle - choice.angleDegrees| <
        |angleDegreesReadout angle - otherChoice.angleDegrees|

/--
**Physics formalization target
(`thm:physics:phyx_mini_0146:target`).**

For the pictured equilateral glass prism, the `45°` air-to-glass entry ray,
the index `n = 1.54`, prism geometry, and Snell's law at both faces imply that
the normal-referenced emergence angle rounds to `56.2°` and is uniquely closest
to answer choice C.
-/
theorem emergenceAngleIsChoiceC
    (diagram : EquilateralGlassPrismDiagram)
    (hData : MatchesProblemData diagram)
    (hPhysical : HasPhysicalOpticalParameters diagram)
    (hGeometry : SatisfiesPrismRayGeometry diagram)
    (hSnell : ObeysSnellsLaw diagram) :
    RoundsToNearestTenthDegree
        (diagram.angleForLabel .exitQuestion)
        AnswerChoice.C.angleDegrees ∧
      IsUniqueNearestAnswerChoice
        (diagram.angleForLabel .exitQuestion) .C := by
  set_option maxHeartbeats 800000 in
    focus
      have hEntryAngle :
          diagram.incidenceAngle .entryFace = angleFromDegrees 45 :=
        hData.entryLabelIsIncidenceAngle.symm.trans hData.entryAngleReadout
      have hSinEntry := hSnell.atInterface .entryFace
      rw [SatisfiesSnellsLawAt, incidentMedium, transmittedMedium,
        hData.airIndexCalibration, hData.glassIndexReadout, hEntryAngle] at hSinEntry
      have hSin45 : Real.Angle.sin (angleFromDegrees 45) = Real.sqrt 2 / 2 := by
        rw [angleFromDegrees, Real.Angle.sin_coe]
        rw [show (45 : ℝ) * Real.pi / 180 = Real.pi / 4 by ring,
          Real.sin_pi_div_four]
      rw [hSin45] at hSinEntry
      have hSinR :
          Real.Angle.sin (diagram.refractionAngle .entryFace) =
            25 * Real.sqrt 2 / 77 := by
        norm_num at hSinEntry ⊢
        linarith
      have hRPhysical := hPhysical.refractionAnglesPhysical .entryFace
      have hCosRPos : 0 < Real.Angle.cos (diagram.refractionAngle .entryFace) := by
        rw [Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two]
        rw [abs_of_nonneg hRPhysical.1]
        exact hRPhysical.2
      have hCosSq := Real.Angle.cos_sq_add_sin_sq
        (diagram.refractionAngle .entryFace)
      have hSqrt2Sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hCosRSq :
          Real.Angle.cos (diagram.refractionAngle .entryFace) ^ 2 =
            (4679 : ℝ) / 5929 := by
        rw [hSinR] at hCosSq
        nlinarith
      have hSqrt4679Sq : Real.sqrt 4679 ^ 2 = (4679 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hCosR :
          Real.Angle.cos (diagram.refractionAngle .entryFace) =
            Real.sqrt 4679 / 77 := by
        have hsqrtpos : 0 < Real.sqrt (4679 : ℝ) :=
          Real.sqrt_pos.2 (by norm_num)
        nlinarith
      have hExitIncidence :
          diagram.incidenceAngle .exitFace =
            angleFromDegrees 60 - diagram.refractionAngle .entryFace := by
        apply eq_sub_of_add_eq
        rw [add_comm]
        exact hGeometry.internalAnglesSumToApex.trans
          hData.equilateralApexReadout
      have hSin60 : Real.Angle.sin (angleFromDegrees 60) = Real.sqrt 3 / 2 := by
        rw [angleFromDegrees, Real.Angle.sin_coe]
        rw [show (60 : ℝ) * Real.pi / 180 = Real.pi / 3 by ring,
          Real.sin_pi_div_three]
      have hCos60 : Real.Angle.cos (angleFromDegrees 60) = 1 / 2 := by
        rw [angleFromDegrees, Real.Angle.cos_coe]
        rw [show (60 : ℝ) * Real.pi / 180 = Real.pi / 3 by ring,
          Real.cos_pi_div_three]
      have hSinExitIncidence :
          Real.Angle.sin (diagram.incidenceAngle .exitFace) =
            Real.sqrt 3 / 2 * (Real.sqrt 4679 / 77) -
              (1 / 2) * (25 * Real.sqrt 2 / 77) := by
        rw [hExitIncidence, sub_eq_add_neg, Real.Angle.sin_add,
          Real.Angle.sin_neg, Real.Angle.cos_neg, hSin60, hCos60, hSinR, hCosR]
        ring
      have hSnellExit := hSnell.atInterface .exitFace
      rw [SatisfiesSnellsLawAt, incidentMedium, transmittedMedium,
        hData.glassIndexReadout, hData.airIndexCalibration, hSinExitIncidence] at hSnellExit
      have hSqrtProduct : Real.sqrt 3 * Real.sqrt 4679 = Real.sqrt 14037 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      have hSinExit :
          Real.Angle.sin (diagram.refractionAngle .exitFace) =
            Real.sqrt 14037 / 100 - Real.sqrt 2 / 4 := by
        calc
          Real.Angle.sin (diagram.refractionAngle .exitFace) =
              154 / 100 *
                (Real.sqrt 3 / 2 * (Real.sqrt 4679 / 77) -
                  (1 / 2) * (25 * Real.sqrt 2 / 77)) := by
                norm_num at hSnellExit ⊢
                linarith
          _ = Real.sqrt 14037 / 100 - Real.sqrt 2 / 4 := by
                calc
                  154 / 100 *
                        (Real.sqrt 3 / 2 * (Real.sqrt 4679 / 77) -
                          (1 / 2) * (25 * Real.sqrt 2 / 77)) =
                      (Real.sqrt 3 * Real.sqrt 4679) / 100 -
                        Real.sqrt 2 / 4 := by ring
                  _ = Real.sqrt 14037 / 100 - Real.sqrt 2 / 4 := by
                    rw [hSqrtProduct]
      have hSqrt2Lower : (141421 : ℝ) / 100000 < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hSqrt2Upper : Real.sqrt 2 < (141422 : ℝ) / 100000 := by
        rw [Real.sqrt_lt (by norm_num) (by norm_num)]
        norm_num
      have hSqrt14037Lower : (1184778 : ℝ) / 10000 < Real.sqrt 14037 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hSqrt14037Upper : Real.sqrt 14037 < (1184779 : ℝ) / 10000 := by
        rw [Real.sqrt_lt (by norm_num) (by norm_num)]
        norm_num
      have hSinExitLower :
          (83122 : ℝ) / 100000 <
            Real.Angle.sin (diagram.refractionAngle .exitFace) := by
        rw [hSinExit]
        nlinarith only [hSqrt14037Lower, hSqrt2Upper]
      have hSinExitUpper :
          Real.Angle.sin (diagram.refractionAngle .exitFace) <
            (83123 : ℝ) / 100000 := by
        rw [hSinExit]
        nlinarith only [hSqrt14037Upper, hSqrt2Lower]
      have hSinUpperValue :
          Real.sin (5 * Real.pi / 16) =
            Real.sqrt ((1 + Real.sqrt (2 - Real.sqrt 2) / 2) / 2) := by
        rw [show 5 * Real.pi / 16 =
            Real.pi / 2 - 3 * Real.pi / 16 by ring,
          Real.sin_pi_div_two_sub]
        rw [show 3 * Real.pi / 16 = (3 * Real.pi / 8) / 2 by ring,
          Real.cos_half (by nlinarith [Real.pi_pos])
            (by nlinarith [Real.pi_pos])]
        rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring,
          Real.cos_pi_div_two_sub, Real.sin_pi_div_eight]
      have hSinUpperLower :
          (83146 : ℝ) / 100000 < Real.sin (5 * Real.pi / 16) := by
        rw [hSinUpperValue]
        have hInnerLower :
            (76536 : ℝ) / 100000 < Real.sqrt (2 - Real.sqrt 2) := by
          rw [Real.lt_sqrt (by norm_num)]
          nlinarith only [hSqrt2Upper]
        rw [Real.lt_sqrt (by norm_num)]
        nlinarith only [hInnerLower]
      have hSinUpperUpper :
          Real.sin (5 * Real.pi / 16) < (83148 : ℝ) / 100000 := by
        rw [hSinUpperValue]
        have hRadicand : 0 ≤ 2 - Real.sqrt 2 := by
          nlinarith only [hSqrt2Upper]
        have hInnerUpper :
            Real.sqrt (2 - Real.sqrt 2) < (76537 : ℝ) / 100000 := by
          rw [Real.sqrt_lt hRadicand (by norm_num)]
          nlinarith only [hSqrt2Lower]
        have hOuterRadicand :
            0 ≤ (1 + Real.sqrt (2 - Real.sqrt 2) / 2) / 2 := by
          nlinarith [Real.sqrt_nonneg (2 - Real.sqrt 2)]
        apply (Real.sqrt_lt hOuterRadicand (by norm_num)).2
        nlinarith only [hInnerUpper]
      have hHalfSin (x : ℝ) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
          Real.sin x / 2 ≤ Real.sin (x / 2) := by
        have hs : 0 ≤ Real.sin (x / 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        calc
          Real.sin x / 2 = Real.sin (2 * (x / 2)) / 2 := by
            congr 2 <;> ring
          _ = Real.sin (x / 2) * Real.cos (x / 2) := by
            rw [Real.sin_two_mul]
            ring
          _ ≤ Real.sin (x / 2) * 1 :=
            mul_le_mul_of_nonneg_left (Real.cos_le_one _) hs
          _ = Real.sin (x / 2) := by ring
      have hRepeatedHalf : ∀ n : ℕ,
          Real.sin (Real.pi / 4) / (2 : ℝ) ^ n ≤
            Real.sin ((Real.pi / 4) / (2 : ℝ) ^ n) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
            have hx0 : 0 ≤ (Real.pi / 4) / (2 : ℝ) ^ n := by positivity
            have hxpi : (Real.pi / 4) / (2 : ℝ) ^ n ≤ Real.pi := by
              have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
              apply (div_le_iff₀' (by positivity)).2
              nlinarith [Real.pi_pos]
            calc
              Real.sin (Real.pi / 4) / (2 : ℝ) ^ (n + 1) =
                  (Real.sin (Real.pi / 4) / (2 : ℝ) ^ n) / 2 := by
                    rw [pow_succ]
                    ring
              _ ≤ Real.sin ((Real.pi / 4) / (2 : ℝ) ^ n) / 2 := by
                    exact div_le_div_of_nonneg_right ih (by norm_num)
              _ ≤ Real.sin (((Real.pi / 4) / (2 : ℝ) ^ n) / 2) :=
                    hHalfSin _ hx0 hxpi
              _ = Real.sin ((Real.pi / 4) / (2 : ℝ) ^ (n + 1)) := by
                    congr 1
                    rw [pow_succ]
                    ring
      have hSmallBase :
          Real.sqrt 2 / 2048 ≤ Real.sin (Real.pi / 4096) := by
        have h := hRepeatedHalf 10
        norm_num [Real.sin_pi_div_four] at h
        calc
          Real.sqrt 2 / 2048 = Real.sqrt 2 / 2 / 1024 := by ring
          _ ≤ Real.sin (Real.pi / 4 / 1024) := h
          _ = Real.sin (Real.pi / 4096) := by
            congr 1 <;> ring
      have hSqrt2One : (1 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hSmallSin : (1 : ℝ) / 2048 < Real.sin (Real.pi / 3600) := by
        have hbase : (1 : ℝ) / 2048 < Real.sin (Real.pi / 4096) := by
          nlinarith only [hSmallBase, hSqrt2One]
        exact hbase.trans_le (Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith only [Real.pi_pos]) (by nlinarith only [Real.pi_pos])
          (by nlinarith only [Real.pi_pos]))
      have hCosMidpoint :
          (1 : ℝ) / 2 ≤ Real.cos (281 * Real.pi / 900) := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi
          (x := 281 * Real.pi / 900) (y := Real.pi / 3)
          (by positivity) (by nlinarith only [Real.pi_pos])
          (by nlinarith only [Real.pi_pos])
        rw [Real.cos_pi_div_three] at h
        exact h
      have hSineGap :
          (1 : ℝ) / 2048 <
            Real.sin (5 * Real.pi / 16) -
              Real.sin (1123 * Real.pi / 3600) := by
        rw [Real.sin_sub_sin]
        rw [show (5 * Real.pi / 16 - 1123 * Real.pi / 3600) / 2 =
            Real.pi / 3600 by ring]
        rw [show (5 * Real.pi / 16 + 1123 * Real.pi / 3600) / 2 =
            281 * Real.pi / 900 by ring]
        nlinarith only [hSmallSin, hCosMidpoint]
      have hExitPhysical := hPhysical.refractionAnglesPhysical .exitFace
      have hExitRealUpper :
          (diagram.refractionAngle .exitFace).toReal < 5 * Real.pi / 16 := by
        by_contra h
        have hAngleLe :
            5 * Real.pi / 16 ≤ (diagram.refractionAngle .exitFace).toReal :=
          le_of_not_gt h
        have hSinLe := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := 5 * Real.pi / 16)
          (y := (diagram.refractionAngle .exitFace).toReal)
          (by nlinarith only [Real.pi_pos]) hExitPhysical.2.le hAngleLe
        rw [Real.Angle.sin_toReal] at hSinLe
        nlinarith only [hSinLe, hSinExitUpper, hSinUpperLower]
      have hExitRealLower :
          1123 * Real.pi / 3600 <
            (diagram.refractionAngle .exitFace).toReal := by
        have hUpperDifference :
            Real.sin (5 * Real.pi / 16) -
            Real.Angle.sin (diagram.refractionAngle .exitFace) <
              (1 : ℝ) / 2048 := by
          nlinarith only [hSinUpperUpper, hSinExitLower]
        have hSinLower :
            Real.sin (1123 * Real.pi / 3600) <
              Real.Angle.sin (diagram.refractionAngle .exitFace) := by
          nlinarith only [hSineGap, hUpperDifference]
        by_contra h
        have hAngleLe :
            (diagram.refractionAngle .exitFace).toReal ≤
              1123 * Real.pi / 3600 := le_of_not_gt h
        have hSinLe := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := (diagram.refractionAngle .exitFace).toReal)
          (y := 1123 * Real.pi / 3600)
          (by nlinarith only [hExitPhysical.1, Real.pi_pos])
          (by nlinarith only [Real.pi_pos]) hAngleLe
        rw [Real.Angle.sin_toReal] at hSinLe
        linarith
      have hReadoutLower :
          (1123 : ℝ) / 20 <
            angleDegreesReadout (diagram.refractionAngle .exitFace) := by
        rw [angleDegreesReadout]
        apply (lt_div_iff₀ Real.pi_pos).2
        nlinarith only [hExitRealLower, Real.pi_pos]
      have hReadoutUpper :
          angleDegreesReadout (diagram.refractionAngle .exitFace) <
            (225 : ℝ) / 4 := by
        rw [angleDegreesReadout]
        apply (div_lt_iff₀ Real.pi_pos).2
        nlinarith only [hExitRealUpper, Real.pi_pos]
      have hRoundExit :
          RoundsToNearestTenthDegree
            (diagram.refractionAngle .exitFace)
            AnswerChoice.C.angleDegrees := by
        rw [RoundsToNearestTenthDegree, AnswerChoice.angleDegrees, abs_lt]
        constructor <;> nlinarith only [hReadoutLower, hReadoutUpper]
      have hCDistance :
          |angleDegreesReadout (diagram.refractionAngle .exitFace) -
              (562 : ℝ) / 10| < (1 : ℝ) / 20 := by
        exact hRoundExit
      have hNearestExit :
          IsUniqueNearestAnswerChoice
            (diagram.refractionAngle .exitFace) .C := by
        intro otherChoice hOther
        cases otherChoice
        · change
            |angleDegreesReadout (diagram.refractionAngle .exitFace) -
                (562 : ℝ) / 10| <
              |angleDegreesReadout (diagram.refractionAngle .exitFace) -
                (662 : ℝ) / 10|
          have hAneg :
              angleDegreesReadout (diagram.refractionAngle .exitFace) -
                  (662 : ℝ) / 10 < 0 := by
            nlinarith only [hReadoutUpper]
          rw [abs_of_neg hAneg]
          nlinarith only [hCDistance, hReadoutUpper]
        · change
            |angleDegreesReadout (diagram.refractionAngle .exitFace) -
                (562 : ℝ) / 10| <
              |angleDegreesReadout (diagram.refractionAngle .exitFace) -
                (462 : ℝ) / 10|
          have hBpos :
              0 < angleDegreesReadout (diagram.refractionAngle .exitFace) -
                  (462 : ℝ) / 10 := by
            nlinarith only [hReadoutLower]
          rw [abs_of_pos hBpos]
          nlinarith only [hCDistance, hReadoutLower]
        · exact (hOther rfl).elim
        · change
            |angleDegreesReadout (diagram.refractionAngle .exitFace) -
                (562 : ℝ) / 10| <
              |angleDegreesReadout (diagram.refractionAngle .exitFace) -
                (762 : ℝ) / 10|
          have hDneg :
              angleDegreesReadout (diagram.refractionAngle .exitFace) -
                  (762 : ℝ) / 10 < 0 := by
            nlinarith only [hReadoutUpper]
          rw [abs_of_neg hDneg]
          nlinarith only [hCDistance, hReadoutUpper]
      constructor
      · rw [hData.questionMarkIsEmergenceAngle]
        exact hRoundExit
      · rw [hData.questionMarkIsEmergenceAngle]
        exact hNearestExit

end PhyXMiniProblems.ProblemPhyXMini0146
