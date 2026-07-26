import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Basic

/-!
# Angular separation of two rays emerging from a prism

This file formalizes `phyx_mini_0099`.  The two labelled light rays enter the
vertical face of a prism normally and in parallel.  They then meet the upper
and lower exit faces symmetrically.  Each angle labelled `A` is the incidence
angle, measured from the corresponding exit-face normal.

Ray directions are nonzero vectors in the two-dimensional diagram plane.
Refractive indices are Physlib quantities carrying the trivial physical
dimension, while all angle fields are real radian readouts.  The
multiple-choice values are displayed in degrees.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0099

/-! ## Diagram objects and scalar readouts -/

/-- The Euclidean plane containing the prism diagram. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/-- A propagation direction is a nonzero vector in the diagram plane. -/
abbrev RayDirection := RayVector ℝ DiagramPlane

/-- A refractive index is a real physical quantity with trivial dimension. -/
abbrev RefractiveIndex := WithDim (1 : Dimension) ℝ

/-- The two light rays labelled in the source figure. -/
inductive FigureRay where
  | m
  | n
  deriving DecidableEq, Repr

/-- The three directed portions of either ray's path. -/
inductive RaySegment where
  | incoming
  | insidePrism
  | emerged
  deriving DecidableEq, Repr

/-- The symmetric sloping faces through which the two rays leave the prism. -/
inductive ExitFace where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The ray which meets each sloping exit face in the primary figure. -/
def rayAtExitFace : ExitFace → FigureRay
  | .upper => .m
  | .lower => .n

/-- The two homogeneous optical media traversed by each ray. -/
inductive OpticalMedium where
  | ambientAir
  | prismGlass
  deriving DecidableEq, Repr

/-- Convert an angle readout in degrees to the radian scalar used in the model. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- The undirected radian angle between two nonzero propagation directions. -/
def angleBetweenDirections (first second : RayDirection) : ℝ :=
  InnerProductGeometry.angle first.1 second.1

/-- A scalar radian readout belongs to the physical geometrical-optics branch. -/
def IsPhysicalOpticsAngle (angleRadians : ℝ) : Prop :=
  0 ≤ angleRadians ∧ angleRadians ≤ Real.pi / 2

/--
Physical objects and measured angle/index data in the prism experiment.

The exit-face normals point from the glass toward the air.  Incidence and
refraction angles are measured from those normals, as required by Snell's law.
-/
structure TwoRayPrismSetup where
  /-- Dimensionless refractive index for each named medium. -/
  refractiveIndex : OpticalMedium → RefractiveIndex
  /-- Propagation direction for every labelled portion of each ray. -/
  rayDirection : FigureRay → RaySegment → RayDirection
  /-- Propagation-oriented normal to the common vertical entry face. -/
  entryFaceNormal : RayDirection
  /-- Glass-to-air normal of each sloping exit face. -/
  exitFaceNormal : ExitFace → RayDirection
  /-- Common figure label `A`, stored as a radian readout. -/
  faceAngleA : ℝ
  /-- Internal angle from the ray to the normal at each exit face. -/
  incidenceAngleRadians : ExitFace → ℝ
  /-- External angle from the normal to the emerged ray at each exit face. -/
  refractionAngleRadians : ExitFace → ℝ

/-! ## Figure data, geometry, and optical laws -/

/--
Numerical and directional information supplied by the problem text and primary
figure.  In particular, this records `n = 1.66`, `A = 25°`, the ambient-air
index, parallel codirected inputs, and normal incidence at the vertical face.
No emergent separation or answer-choice value occurs in this data.
-/
structure MatchesProblemAndFigure (setup : TwoRayPrismSetup) : Prop where
  prismIndexReadout :
    (setup.refractiveIndex .prismGlass).val = 1.66
  ambientAirIndexReadout :
    (setup.refractiveIndex .ambientAir).val = 1
  angleAReadout :
    setup.faceAngleA = degreesToRadians 25
  incomingRaysParallel :
    SameRay ℝ
      (setup.rayDirection .m .incoming).1
      (setup.rayDirection .n .incoming).1
  rayMNormalAtEntry :
    angleBetweenDirections
        (setup.rayDirection .m .incoming) setup.entryFaceNormal = 0
  rayNNormalAtEntry :
    angleBetweenDirections
        (setup.rayDirection .n .incoming) setup.entryFaceNormal = 0

/-- Positivity and principal-branch conditions for the optical quantities. -/
structure HasPhysicalOpticalParameters (setup : TwoRayPrismSetup) : Prop where
  refractiveIndicesPositive :
    ∀ medium, 0 < (setup.refractiveIndex medium).val
  angleAPhysical :
    IsPhysicalOpticsAngle setup.faceAngleA
  incidenceAnglesPhysical :
    ∀ face, IsPhysicalOpticsAngle (setup.incidenceAngleRadians face)
  refractionAnglesPhysical :
    ∀ face, IsPhysicalOpticsAngle (setup.refractionAngleRadians face)

/--
Geometric content of the symmetric prism drawing.

The scalar incidence/refraction readouts are tied to actual vector angles.
Both internal incidence angles equal the displayed `A`.  Because the upper and
lower rays bend on opposite sides of their common internal direction, their
emergent separation is the sum of the two deviations `refraction - incidence`.
This is a general figure relation and contains no numerical answer.
-/
structure SatisfiesSymmetricPrismGeometry
    (setup : TwoRayPrismSetup) : Prop where
  incidenceAngleFromDirections : ∀ face,
    setup.incidenceAngleRadians face =
      angleBetweenDirections
        (setup.rayDirection (rayAtExitFace face) .insidePrism)
        (setup.exitFaceNormal face)
  refractionAngleFromDirections : ∀ face,
    setup.refractionAngleRadians face =
      angleBetweenDirections
        (setup.rayDirection (rayAtExitFace face) .emerged)
        (setup.exitFaceNormal face)
  bothExitIncidencesCarryLabelA : ∀ face,
    setup.incidenceAngleRadians face = setup.faceAngleA
  oppositeSideExitComposition :
    angleBetweenDirections
        (setup.rayDirection .m .emerged)
        (setup.rayDirection .n .emerged) =
      (setup.refractionAngleRadians .upper -
          setup.incidenceAngleRadians .upper) +
        (setup.refractionAngleRadians .lower -
          setup.incidenceAngleRadians .lower)

/-- Snell's law at one of the two glass-to-air exit faces. -/
def SatisfiesSnellsLawAtExit
    (setup : TwoRayPrismSetup) (face : ExitFace) : Prop :=
  (setup.refractiveIndex .prismGlass).val *
      Real.sin (setup.incidenceAngleRadians face) =
    (setup.refractiveIndex .ambientAir).val *
      Real.sin (setup.refractionAngleRadians face)

/--
Governing ray-optics laws used by the experiment.  Normal entry preserves each
ray's direction, and Snell's law holds independently at both exit faces.
-/
structure ObeysPrismOpticsLaws (setup : TwoRayPrismSetup) : Prop where
  normalEntryTransmission : ∀ ray,
    SameRay ℝ
      (setup.rayDirection ray .incoming).1
      (setup.rayDirection ray .insidePrism).1
  snellAtEachExit : ∀ face, SatisfiesSnellsLawAtExit setup face

/-! ## Exact relation and multiple-choice target -/

/-- The actual angular separation of the emerged rays, measured in radians. -/
def emergentSeparationRadians (setup : TwoRayPrismSetup) : ℝ :=
  angleBetweenDirections
    (setup.rayDirection .m .emerged)
    (setup.rayDirection .n .emerged)

/-- The four answer labels displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Angular-separation readout, in degrees, printed beside each answer choice. -/
def AnswerChoice.separationDegrees : AnswerChoice → ℝ
  | .A => 39.1
  | .B => 35.9
  | .C => 37.3
  | .D => 38.2

/-- Dataset metadata: the recorded answer label, never used as a premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
`actualRadians` agrees with a degree display rounded to the nearest tenth.
The strict half-tenth-degree tolerance avoids asserting that the rounded
multiple-choice number is the exact transcendental Snell-law value.
-/
def RoundsToTenthDegree
    (actualRadians displayedDegrees : ℝ) : Prop :=
  |actualRadians - degreesToRadians displayedDegrees| <
    degreesToRadians ((1 : ℝ) / 20)

/--
Snell's law and the symmetric figure geometry give the exact (unrounded)
angular separation: twice the deviation of either ray from its original
direction.  This auxiliary conclusion contains no selected answer value.
-/
lemma emergentSeparation_symbolic
    (setup : TwoRayPrismSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_geometry : SatisfiesSymmetricPrismGeometry setup)
    (_optics : ObeysPrismOpticsLaws setup) :
    emergentSeparationRadians setup =
      2 *
        (Real.arcsin
            ((setup.refractiveIndex .prismGlass).val /
                (setup.refractiveIndex .ambientAir).val *
              Real.sin setup.faceAngleA) -
          setup.faceAngleA) := by
  have hAir :
      (setup.refractiveIndex .ambientAir).val ≠ 0 :=
    ne_of_gt (_physical.refractiveIndicesPositive .ambientAir)
  have incidenceUpper :
      setup.incidenceAngleRadians .upper = setup.faceAngleA :=
    _geometry.bothExitIncidencesCarryLabelA .upper
  have incidenceLower :
      setup.incidenceAngleRadians .lower = setup.faceAngleA :=
    _geometry.bothExitIncidencesCarryLabelA .lower
  have sinRefraction (face : ExitFace) :
      Real.sin (setup.refractionAngleRadians face) =
        (setup.refractiveIndex .prismGlass).val /
            (setup.refractiveIndex .ambientAir).val *
          Real.sin setup.faceAngleA := by
    have hSnell := _optics.snellAtEachExit face
    rw [SatisfiesSnellsLawAtExit,
      _geometry.bothExitIncidencesCarryLabelA face] at hSnell
    field_simp [hAir]
    linarith
  have refraction (face : ExitFace) :
      setup.refractionAngleRadians face =
        Real.arcsin
          ((setup.refractiveIndex .prismGlass).val /
              (setup.refractiveIndex .ambientAir).val *
            Real.sin setup.faceAngleA) := by
    have hPhysical := _physical.refractionAnglesPhysical face
    rw [IsPhysicalOpticsAngle] at hPhysical
    calc
      setup.refractionAngleRadians face =
          Real.arcsin (Real.sin (setup.refractionAngleRadians face)) :=
        (Real.arcsin_sin (by linarith [hPhysical.1, Real.pi_pos])
          hPhysical.2).symm
      _ = Real.arcsin
          ((setup.refractiveIndex .prismGlass).val /
              (setup.refractiveIndex .ambientAir).val *
            Real.sin setup.faceAngleA) := by rw [sinRefraction face]
  rw [emergentSeparationRadians,
    _geometry.oppositeSideExitComposition,
    refraction .upper, refraction .lower,
    incidenceUpper, incidenceLower]
  ring

/--
For prism index `1.66` and symmetric incidence angles `A = 25°`, the two
normally incident parallel rays emerge with an angular separation which rounds
to `39.1°`.  Hence the recorded multiple-choice answer is A.

Blueprint: `thm:physics:phyx_mini_0099:target`.
-/
theorem emergentRaysSeparation_isAnswerA
    (setup : TwoRayPrismSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_geometry : SatisfiesSymmetricPrismGeometry setup)
    (_optics : ObeysPrismOpticsLaws setup) :
    RoundsToTenthDegree
      (emergentSeparationRadians setup)
      AnswerChoice.A.separationDegrees := by
  set_option maxHeartbeats 800000 in
    have doubleBounds (x sl su cl cu : ℝ)
        (hsl : sl ≤ Real.sin x) (hsu : Real.sin x ≤ su)
        (hcl : cl ≤ Real.cos x) (hcu : Real.cos x ≤ cu)
        (hsl0 : 0 ≤ sl) (hcl0 : 0 ≤ cl) :
        2 * sl * cl ≤ Real.sin (2 * x) ∧
          Real.sin (2 * x) ≤ 2 * su * cu ∧
          2 * cl ^ 2 - 1 ≤ Real.cos (2 * x) ∧
          Real.cos (2 * x) ≤ 2 * cu ^ 2 - 1 := by
      have hs0 : 0 ≤ Real.sin x := hsl0.trans hsl
      have hc0 : 0 ≤ Real.cos x := hcl0.trans hcl
      have hsu0 : 0 ≤ su := hs0.trans hsu
      have hcu0 : 0 ≤ cu := hc0.trans hcu
      constructor
      · rw [Real.sin_two_mul]
        gcongr
      constructor
      · rw [Real.sin_two_mul]
        gcongr
      constructor
      · rw [Real.cos_two_mul]
        gcongr
      · rw [Real.cos_two_mul]
        gcongr

    have sqrtTwoLower : (1.414213 : ℝ) < √2 := by
      nlinarith only [
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]
    have sqrtTwoUpper : √2 < (1.414214 : ℝ) := by
      nlinarith only [
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]

    /-
    The decimal π bounds are derived from the exact value at `π / 4`.
    Starting at one sixteenth of each rational comparison angle makes the
    imported cubic/quartic sine and cosine error bounds sharp enough; four
    exact double-angle steps then recover the comparison at `π / 4`.
    -/
    have sinLowerPi : Real.sin (3141 / 4000 : ℝ) < √2 / 2 := by
      have hsin0 :=
        Real.sin_bound (x := (3141 / 64000 : ℝ))
          (by norm_num [abs_of_nonneg])
      have hcos0 :=
        Real.cos_bound (x := (3141 / 64000 : ℝ))
          (by norm_num [abs_of_nonneg])
      rw [abs_le] at hsin0 hcos0
      have hs0l :
          (0.0490581 : ℝ) ≤ Real.sin (3141 / 64000 : ℝ) := by
        norm_num [abs_of_nonneg] at hsin0
        linarith only [hsin0.1]
      have hs0u :
          Real.sin (3141 / 64000 : ℝ) ≤ (0.0490588 : ℝ) := by
        norm_num [abs_of_nonneg] at hsin0
        linarith only [hsin0.2]
      have hc0l :
          (0.9987953 : ℝ) ≤ Real.cos (3141 / 64000 : ℝ) := by
        norm_num [abs_of_nonneg] at hcos0
        linarith only [hcos0.1]
      have hc0u :
          Real.cos (3141 / 64000 : ℝ) ≤ (0.9987960 : ℝ) := by
        norm_num [abs_of_nonneg] at hcos0
        linarith only [hcos0.2]
      obtain ⟨hs1l, hs1u, hc1l, hc1u⟩ :=
        doubleBounds (3141 / 64000)
          0.0490581 0.0490588 0.9987953 0.9987960
          hs0l hs0u hc0l hc0u (by norm_num) (by norm_num)
      obtain ⟨hs2l, hs2u, hc2l, hc2u⟩ :=
        doubleBounds (2 * (3141 / 64000))
          (2 * 0.0490581 * 0.9987953)
          (2 * 0.0490588 * 0.9987960)
          (2 * 0.9987953 ^ 2 - 1)
          (2 * 0.9987960 ^ 2 - 1)
          hs1l hs1u hc1l hc1u (by norm_num) (by norm_num)
      obtain ⟨hs3l, hs3u, hc3l, hc3u⟩ :=
        doubleBounds (2 * (2 * (3141 / 64000)))
          (2 * (2 * 0.0490581 * 0.9987953) *
            (2 * 0.9987953 ^ 2 - 1))
          (2 * (2 * 0.0490588 * 0.9987960) *
            (2 * 0.9987960 ^ 2 - 1))
          (2 * (2 * 0.9987953 ^ 2 - 1) ^ 2 - 1)
          (2 * (2 * 0.9987960 ^ 2 - 1) ^ 2 - 1)
          hs2l hs2u hc2l hc2u (by norm_num) (by norm_num)
      obtain ⟨_hs4l, hs4u, _hc4l, _hc4u⟩ :=
        doubleBounds (2 * (2 * (2 * (3141 / 64000))))
          (2 *
            (2 * (2 * 0.0490581 * 0.9987953) *
              (2 * 0.9987953 ^ 2 - 1)) *
            (2 * (2 * 0.9987953 ^ 2 - 1) ^ 2 - 1))
          (2 *
            (2 * (2 * 0.0490588 * 0.9987960) *
              (2 * 0.9987960 ^ 2 - 1)) *
            (2 * (2 * 0.9987960 ^ 2 - 1) ^ 2 - 1))
          (2 * (2 * (2 * 0.9987953 ^ 2 - 1) ^ 2 - 1) ^ 2 - 1)
          (2 * (2 * (2 * 0.9987960 ^ 2 - 1) ^ 2 - 1) ^ 2 - 1)
          hs3l hs3u hc3l hc3u (by norm_num) (by norm_num)
      norm_num at hs4u
      linarith only [hs4u, sqrtTwoLower]

    have sinUpperPi : √2 / 2 < Real.sin (1571 / 2000 : ℝ) := by
      have hsin0 :=
        Real.sin_bound (x := (1571 / 32000 : ℝ))
          (by norm_num [abs_of_nonneg])
      have hcos0 :=
        Real.cos_bound (x := (1571 / 32000 : ℝ))
          (by norm_num [abs_of_nonneg])
      rw [abs_le] at hsin0 hcos0
      have hs0l :
          (0.0490737 : ℝ) ≤ Real.sin (1571 / 32000 : ℝ) := by
        norm_num [abs_of_nonneg] at hsin0
        linarith only [hsin0.1]
      have hs0u :
          Real.sin (1571 / 32000 : ℝ) ≤ (0.0490744 : ℝ) := by
        norm_num [abs_of_nonneg] at hsin0
        linarith only [hsin0.2]
      have hc0l :
          (0.9987945 : ℝ) ≤ Real.cos (1571 / 32000 : ℝ) := by
        norm_num [abs_of_nonneg] at hcos0
        linarith only [hcos0.1]
      have hc0u :
          Real.cos (1571 / 32000 : ℝ) ≤ (0.9987953 : ℝ) := by
        norm_num [abs_of_nonneg] at hcos0
        linarith only [hcos0.2]
      obtain ⟨hs1l, hs1u, hc1l, hc1u⟩ :=
        doubleBounds (1571 / 32000)
          0.0490737 0.0490744 0.9987945 0.9987953
          hs0l hs0u hc0l hc0u (by norm_num) (by norm_num)
      obtain ⟨hs2l, hs2u, hc2l, hc2u⟩ :=
        doubleBounds (2 * (1571 / 32000))
          (2 * 0.0490737 * 0.9987945)
          (2 * 0.0490744 * 0.9987953)
          (2 * 0.9987945 ^ 2 - 1)
          (2 * 0.9987953 ^ 2 - 1)
          hs1l hs1u hc1l hc1u (by norm_num) (by norm_num)
      obtain ⟨hs3l, hs3u, hc3l, hc3u⟩ :=
        doubleBounds (2 * (2 * (1571 / 32000)))
          (2 * (2 * 0.0490737 * 0.9987945) *
            (2 * 0.9987945 ^ 2 - 1))
          (2 * (2 * 0.0490744 * 0.9987953) *
            (2 * 0.9987953 ^ 2 - 1))
          (2 * (2 * 0.9987945 ^ 2 - 1) ^ 2 - 1)
          (2 * (2 * 0.9987953 ^ 2 - 1) ^ 2 - 1)
          hs2l hs2u hc2l hc2u (by norm_num) (by norm_num)
      obtain ⟨hs4l, _hs4u, _hc4l, _hc4u⟩ :=
        doubleBounds (2 * (2 * (2 * (1571 / 32000))))
          (2 *
            (2 * (2 * 0.0490737 * 0.9987945) *
              (2 * 0.9987945 ^ 2 - 1)) *
            (2 * (2 * 0.9987945 ^ 2 - 1) ^ 2 - 1))
          (2 *
            (2 * (2 * 0.0490744 * 0.9987953) *
              (2 * 0.9987953 ^ 2 - 1)) *
            (2 * (2 * 0.9987953 ^ 2 - 1) ^ 2 - 1))
          (2 * (2 * (2 * 0.9987945 ^ 2 - 1) ^ 2 - 1) ^ 2 - 1)
          (2 * (2 * (2 * 0.9987953 ^ 2 - 1) ^ 2 - 1) ^ 2 - 1)
          hs3l hs3u hc3l hc3u (by norm_num) (by norm_num)
      norm_num at hs4l
      linarith only [hs4l, sqrtTwoUpper]

    have hpi : (3.141 : ℝ) < Real.pi ∧ Real.pi < (3.142 : ℝ) := by
      constructor
      · by_contra h
        have hpiLe : Real.pi ≤ (3.141 : ℝ) := le_of_not_gt h
        have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := Real.pi / 4) (y := (3141 / 4000 : ℝ))
          (by linarith only [Real.pi_pos])
          (by linarith only [Real.two_le_pi])
          (by linarith only [hpiLe])
        rw [Real.sin_pi_div_four] at hmono
        linarith only [hmono, sinLowerPi]
      · by_contra h
        have hpiGe : (3.142 : ℝ) ≤ Real.pi := le_of_not_gt h
        have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := (1571 / 2000 : ℝ)) (y := Real.pi / 4)
          (by linarith only [Real.pi_pos])
          (by linarith only [Real.pi_pos])
          (by linarith only [hpiGe])
        rw [Real.sin_pi_div_four] at hmono
        linarith only [hmono, sinUpperPi]

    /- Polynomial enclosures for sine and cosine on a small positive interval. -/
    have smallAngleBounds (x xl xu : ℝ)
        (hxl0 : 0 ≤ xl) (hxl : xl ≤ x) (hxu : x ≤ xu)
        (hxu1 : xu ≤ 1) :
        xl - xu ^ 3 / 6 - xu ^ 4 * (5 / 96) ≤ Real.sin x ∧
          Real.sin x ≤ xu - xl ^ 3 / 6 + xu ^ 4 * (5 / 96) ∧
          1 - xu ^ 2 / 2 - xu ^ 4 * (5 / 96) ≤ Real.cos x ∧
          Real.cos x ≤ 1 - xl ^ 2 / 2 + xu ^ 4 * (5 / 96) := by
      have hx0 : 0 ≤ x := hxl0.trans hxl
      have habs : |x| ≤ 1 := by
        rw [abs_of_nonneg hx0]
        exact hxu.trans hxu1
      have hs := abs_le.mp (Real.sin_bound habs)
      have hc := abs_le.mp (Real.cos_bound habs)
      rw [abs_of_nonneg hx0] at hs hc
      have hxl2 : xl ^ 2 ≤ x ^ 2 := by gcongr
      have hxl3 : xl ^ 3 ≤ x ^ 3 := by gcongr
      have hxu2 : x ^ 2 ≤ xu ^ 2 := by gcongr
      have hxu3 : x ^ 3 ≤ xu ^ 3 := by gcongr
      have hxu4 : x ^ 4 ≤ xu ^ 4 := by gcongr
      constructor
      · nlinarith only [hs.1, hxl, hxu3, hxu4]
      constructor
      · nlinarith only [hs.2, hxu, hxl3, hxu4]
      constructor
      · nlinarith only [hc.1, hxu2, hxu4]
      · nlinarith only [hc.2, hxl2, hxu4]

    have sqrtThreeLower : (1.73205 : ℝ) < √3 := by
      nlinarith only [
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg (3 : ℝ)]
    have sqrtThreeUpper : √3 < (1.732051 : ℝ) := by
      nlinarith only [
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg (3 : ℝ)]

    obtain ⟨hsxL', hsxU', hcxL', hcxU'⟩ :=
      smallAngleBounds (Real.pi / 36) (349 / 4000) (1571 / 18000)
        (by norm_num)
        (by linarith only [hpi.1])
        (by linarith only [hpi.2])
        (by norm_num)
    have hsxL : (0.0871361 : ℝ) ≤ Real.sin (Real.pi / 36) := by
      norm_num at hsxL'
      linarith only [hsxL']
    have hsxU : Real.sin (Real.pi / 36) ≤ (0.0871702 : ℝ) := by
      norm_num at hsxU'
      linarith only [hsxU']
    have hcxL : (0.9961882 : ℝ) ≤ Real.cos (Real.pi / 36) := by
      norm_num at hcxL'
      linarith only [hcxL']
    have hcxU : Real.cos (Real.pi / 36) ≤ (0.9961968 : ℝ) := by
      norm_num at hcxU'
      linarith only [hcxU']
    have sinFivePiOverThirtySix :
        Real.sin (5 * Real.pi / 36) =
          (1 / 2 : ℝ) * Real.cos (Real.pi / 36) -
            √3 / 2 * Real.sin (Real.pi / 36) := by
      rw [show (5 : ℝ) * Real.pi / 36 =
          Real.pi / 6 - Real.pi / 36 by ring,
        Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]
    have zLower :
        (0.7015 : ℝ) <
          (83 / 50 : ℝ) * Real.sin (5 * Real.pi / 36) := by
      have hsx0 : 0 ≤ Real.sin (Real.pi / 36) := by
        linarith only [hsxL]
      have hprod :
          √3 / 2 * Real.sin (Real.pi / 36) ≤
            (1.732051 / 2 : ℝ) * 0.0871702 := by
        gcongr
      rw [sinFivePiOverThirtySix]
      nlinarith only [hprod, hcxL]
    have zUpper :
        (83 / 50 : ℝ) * Real.sin (5 * Real.pi / 36) <
          (0.7016 : ℝ) := by
      have hprod :
          (1.73205 / 2 : ℝ) * 0.0871361 ≤
            √3 / 2 * Real.sin (Real.pi / 36) := by
        gcongr
      rw [sinFivePiOverThirtySix]
      nlinarith only [hprod, hcxU]

    obtain ⟨hsdLL', hsdLU', hcdLL', hcdLU'⟩ :=
      smallAngleBounds (19 * Real.pi / 7200)
        (19 * 3.141 / 7200) (19 * 3.142 / 7200)
        (by norm_num)
        (by nlinarith only [hpi.1])
        (by nlinarith only [hpi.2])
        (by norm_num)
    have hsdLL :
        (0.0082886 : ℝ) ≤ Real.sin (19 * Real.pi / 7200) := by
      norm_num at hsdLL'
      linarith only [hsdLL']
    have hsdLU :
        Real.sin (19 * Real.pi / 7200) ≤ (0.0082914 : ℝ) := by
      norm_num at hsdLU'
      linarith only [hsdLU']
    have hcdLL :
        (0.9999656 : ℝ) ≤ Real.cos (19 * Real.pi / 7200) := by
      norm_num at hcdLL'
      linarith only [hcdLL']
    have hcdLU :
        Real.cos (19 * Real.pi / 7200) ≤ (0.9999657 : ℝ) := by
      norm_num at hcdLU'
      linarith only [hcdLU']
    have sinLowerAngle :
        Real.sin (1781 * Real.pi / 7200) < (0.7013 : ℝ) := by
      have hbracket :
          0 ≤ Real.cos (19 * Real.pi / 7200) -
            Real.sin (19 * Real.pi / 7200) := by
        linarith only [hcdLL, hsdLU]
      have hprod :
          √2 / 2 *
              (Real.cos (19 * Real.pi / 7200) -
                Real.sin (19 * Real.pi / 7200)) ≤
            (1.414214 / 2 : ℝ) * (0.9999657 - 0.0082886) := by
        gcongr
      rw [show (1781 : ℝ) * Real.pi / 7200 =
          Real.pi / 4 - 19 * Real.pi / 7200 by ring,
        Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
      norm_num at hprod ⊢
      linarith only [hprod]

    obtain ⟨hsdUL', hsdUU', hcdUL', hcdUU'⟩ :=
      smallAngleBounds (17 * Real.pi / 7200)
        (17 * 3.141 / 7200) (17 * 3.142 / 7200)
        (by norm_num)
        (by nlinarith only [hpi.1])
        (by nlinarith only [hpi.2])
        (by norm_num)
    have hsdUU :
        Real.sin (17 * Real.pi / 7200) ≤ (0.0074186 : ℝ) := by
      norm_num at hsdUU'
      linarith only [hsdUU']
    have hcdUL :
        (0.9999724 : ℝ) ≤ Real.cos (17 * Real.pi / 7200) := by
      norm_num at hcdUL'
      linarith only [hcdUL']
    have sinUpperAngle :
        (0.7018 : ℝ) < Real.sin (1783 * Real.pi / 7200) := by
      have hprod :
          (1.414213 / 2 : ℝ) * (0.9999724 - 0.0074186) ≤
            √2 / 2 *
              (Real.cos (17 * Real.pi / 7200) -
                Real.sin (17 * Real.pi / 7200)) := by
        gcongr
      rw [show (1783 : ℝ) * Real.pi / 7200 =
          Real.pi / 4 - 17 * Real.pi / 7200 by ring,
        Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
      norm_num at hprod ⊢
      linarith only [hprod]

    have sinComparisonLower :
        Real.sin (1781 * Real.pi / 7200) <
          (83 / 50 : ℝ) * Real.sin (5 * Real.pi / 36) := by
      linarith only [sinLowerAngle, zLower]
    have sinComparisonUpper :
        (83 / 50 : ℝ) * Real.sin (5 * Real.pi / 36) <
          Real.sin (1783 * Real.pi / 7200) := by
      linarith only [zUpper, sinUpperAngle]
    have lowerRange :
        (1781 * Real.pi / 7200 : ℝ) ∈
          Set.Ico (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have upperRange :
        (1783 * Real.pi / 7200 : ℝ) ∈
          Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have arcLower :
        (1781 * Real.pi / 7200 : ℝ) <
          Real.arcsin
            ((83 / 50 : ℝ) * Real.sin (5 * Real.pi / 36)) :=
      (Real.lt_arcsin_iff_sin_lt' lowerRange).2 sinComparisonLower
    have arcUpper :
        Real.arcsin
            ((83 / 50 : ℝ) * Real.sin (5 * Real.pi / 36)) <
          (1783 * Real.pi / 7200 : ℝ) :=
      (Real.arcsin_lt_iff_lt_sin' upperRange).2 sinComparisonUpper
    have roundedNumerical :
        |2 *
              (Real.arcsin
                  ((83 / 50 : ℝ) * Real.sin (5 * Real.pi / 36)) -
                5 * Real.pi / 36) -
            (391 / 10 : ℝ) * Real.pi / 180| <
          (1 / 20 : ℝ) * Real.pi / 180 := by
      rw [abs_lt]
      constructor <;> nlinarith only [arcLower, arcUpper, Real.pi_pos]
    have hSeparation :=
      emergentSeparation_symbolic
        setup _problem _physical _geometry _optics
    rw [_problem.prismIndexReadout, _problem.ambientAirIndexReadout,
      _problem.angleAReadout] at hSeparation
    norm_num [degreesToRadians] at hSeparation
    rw [hSeparation]
    norm_num [RoundsToTenthDegree, AnswerChoice.separationDegrees,
      degreesToRadians]
    convert roundedNumerical using 1
    all_goals ring_nf

end PhyXMiniProblems.ProblemPhyXMini0099
