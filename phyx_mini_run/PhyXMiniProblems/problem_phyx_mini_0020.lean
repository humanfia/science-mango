import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0020

/-- The two-dimensional Euclidean cross-section shown in the figure. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The real-valued readout of a physical length when expressed in SI units. -/
def siLengthValue (length : Dimensionful (WithDim Dimension.L𝓭 ℝ)) : ℝ :=
  (length UnitChoices.SI).val

/--
An oriented geometrical-optics ray. Its source and direction live in the
cylinder's Euclidean cross-section; the nonzero condition excludes a
degenerate path.
-/
structure LightRay where
  source : Plane
  direction : Plane
  direction_ne_zero : direction ≠ 0

/-- A point lies forward along an oriented light ray. -/
def LightRay.PassesThrough (ray : LightRay) (point : Plane) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ point = ray.source + t • ray.direction

/--
The half of a circular boundary lying in the nonnegative direction of a
chosen horizontal axis. This is the right mirrored semicircle in the figure.
-/
def rightSemicircle
    (center horizontalDirection : Plane) (radius : ℝ) : Set Plane :=
  {point |
    dist point center = radius ∧
      0 ≤ inner ℝ (point - center) horizontalDirection}

/--
All named physical quantities and figure labels for the transparent circular
cylinder. Lengths retain their physical dimension through Physlib's
`Dimensionful (WithDim L𝓭 ℝ)` type. Refractive indices and radian angle
readouts are dimensionless real numbers.
-/
structure CylinderMirrorExperiment where
  /-- Figure center `C`. -/
  center : Plane
  /-- Unit vector pointing to the right in the displayed cross-section. -/
  horizontalDirection : Plane
  horizontalDirection_unit : ‖horizontalDirection‖ = 1
  /-- Point where the incoming air ray first enters the cylinder. -/
  entryPoint : Plane
  /-- Point where the internal ray strikes the mirrored right boundary. -/
  mirrorPoint : Plane
  /-- Point where the reflected internal ray exits the cylinder. -/
  exitPoint : Plane
  /-- The mirrored right half of the circular boundary. -/
  mirroredSurface : Set Plane
  incomingRay : LightRay
  entryToMirrorRay : LightRay
  mirrorToExitRay : LightRay
  outgoingRay : LightRay
  /-- Figure label `R`, the cylinder radius. -/
  radius : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- Figure label `d`, the perpendicular separation of the external rays. -/
  raySeparation : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  radius_pos : 0 < siLengthValue radius
  raySeparation_pos : 0 < siLengthValue raySeparation
  airRefractiveIndex : ℝ
  materialRefractiveIndex : ℝ
  airRefractiveIndex_pos : 0 < airRefractiveIndex
  materialRefractiveIndex_gt_one : 1 < materialRefractiveIndex
  /-- Incidence angle in air at entry, measured from the radial normal. -/
  entryIncidenceAngle : ℝ
  /-- Transmitted angle in the material at entry, measured from the normal. -/
  entryRefractionAngle : ℝ
  /-- Internal incidence angle at the mirrored boundary. -/
  mirrorIncidenceAngle : ℝ
  /-- Internal reflection angle at the mirrored boundary. -/
  mirrorReflectionAngle : ℝ
  /-- Incidence angle in the material at the exit boundary. -/
  exitIncidenceAngle : ℝ
  /-- Refraction angle in air at exit, measured from the radial normal. -/
  exitRefractionAngle : ℝ

/--
Snell's law at an interface, using dimensionless refractive indices and angle
magnitudes measured in radians from the local surface normal.
-/
def SnellLawAtInterface
    (incidentRefractiveIndex transmittedRefractiveIndex : ℝ)
    (incidentAngle transmittedAngle : ℝ) : Prop :=
  incidentRefractiveIndex * Real.sin incidentAngle =
    transmittedRefractiveIndex * Real.sin transmittedAngle

/-- The optical law of specular reflection at the mirrored boundary. -/
def SpecularReflectionAtMirror
    (incidenceAngle reflectionAngle : ℝ) : Prop :=
  incidenceAngle = reflectionAngle

/--
The calibrated measurements and planar geometry read from the figure.

Besides the SI readouts `R = d = 2 m`, this records the circular boundary,
the rightmost mirror hit, the complete ray path, the opposite but parallel
external ray directions, and the normal-referenced angle relations. The
relation `mirrorIncidenceAngle = entryIncidenceAngle / 2` is the inscribed
half-angle relation for the chord from the entry point to the rightmost point
of the circle; together with the preceding angle decomposition it determines
the entry refraction angle without assuming the requested refractive index.
-/
def CylinderFigureReadout (s : CylinderMirrorExperiment) : Prop :=
  let R := siLengthValue s.radius
  let d := siLengthValue s.raySeparation
  R = 2 ∧
    d = 2 ∧
    s.airRefractiveIndex = 1 ∧
    s.mirroredSurface =
      rightSemicircle s.center s.horizontalDirection R ∧
    s.mirrorPoint ∈ s.mirroredSurface ∧
    s.mirrorPoint = s.center + R • s.horizontalDirection ∧
    dist s.entryPoint s.center = R ∧
    dist s.exitPoint s.center = R ∧
    dist s.entryPoint s.exitPoint = d ∧
    inner ℝ (s.entryPoint - s.exitPoint) s.horizontalDirection = 0 ∧
    s.entryPoint + s.exitPoint = (2 : ℝ) • s.center ∧
    s.incomingRay.PassesThrough s.entryPoint ∧
    s.entryToMirrorRay.source = s.entryPoint ∧
    s.entryToMirrorRay.PassesThrough s.mirrorPoint ∧
    s.mirrorToExitRay.source = s.mirrorPoint ∧
    s.mirrorToExitRay.PassesThrough s.exitPoint ∧
    s.outgoingRay.source = s.exitPoint ∧
    (∃ incomingScale outgoingScale : ℝ,
      0 < incomingScale ∧
        0 < outgoingScale ∧
        s.incomingRay.direction =
          incomingScale • s.horizontalDirection ∧
        s.outgoingRay.direction =
          (-outgoingScale) • s.horizontalDirection) ∧
    s.entryIncidenceAngle ∈ Set.Ioo 0 (Real.pi / 2) ∧
    s.entryRefractionAngle ∈ Set.Ioo 0 (Real.pi / 2) ∧
    s.mirrorIncidenceAngle ∈ Set.Ioo 0 (Real.pi / 2) ∧
    s.mirrorReflectionAngle ∈ Set.Ioo 0 (Real.pi / 2) ∧
    s.exitIncidenceAngle ∈ Set.Ioo 0 (Real.pi / 2) ∧
    s.exitRefractionAngle ∈ Set.Ioo 0 (Real.pi / 2) ∧
    d = 2 * R * Real.sin s.entryIncidenceAngle ∧
    s.mirrorIncidenceAngle =
      s.entryIncidenceAngle - s.entryRefractionAngle ∧
    s.mirrorIncidenceAngle = s.entryIncidenceAngle / 2 ∧
    s.mirrorReflectionAngle = s.entryIncidenceAngle / 2 ∧
    s.exitIncidenceAngle = s.entryRefractionAngle ∧
    s.exitRefractionAngle = s.entryIncidenceAngle

/--
The governing optical laws: Snell refraction at entry and exit and equal
incidence/reflection angles at the mirrored surface.
-/
def GeometricalOpticsLaws (s : CylinderMirrorExperiment) : Prop :=
  SnellLawAtInterface
      s.airRefractiveIndex s.materialRefractiveIndex
      s.entryIncidenceAngle s.entryRefractionAngle ∧
    SpecularReflectionAtMirror
      s.mirrorIncidenceAngle s.mirrorReflectionAngle ∧
    SnellLawAtInterface
      s.materialRefractiveIndex s.airRefractiveIndex
      s.exitIncidenceAngle s.exitRefractionAngle

/-- The four multiple-choice labels printed with the problem. -/
inductive AnswerChoice
  | A | B | C | D
  deriving DecidableEq

/-- The dimensionless refractive-index value printed for each answer choice. -/
def answerChoiceValue : AnswerChoice → ℝ
  | .A => 177 / 100
  | .B => 152 / 100
  | .C => 193 / 100
  | .D => 187 / 100

/-- A dimensionless value rounds to the reported value at the hundredth place. -/
def RoundsToNearestHundredth (value reportedValue : ℝ) : Prop :=
  |value - reportedValue| < 1 / 200

/--
For the cylinder and ray path in the figure, the material's dimensionless
index of refraction is exactly `sqrt (2 + sqrt 3)`. This is approximately
`1.93`, hence it selects answer choice C.

Blueprint: `thm:physics:phyx_mini_0020:target`.
-/
theorem refractiveIndex_eq_answerChoiceC
    (s : CylinderMirrorExperiment)
    (hFigure : CylinderFigureReadout s)
    (hOptics : GeometricalOpticsLaws s) :
    s.materialRefractiveIndex = Real.sqrt (2 + Real.sqrt 3) ∧
      RoundsToNearestHundredth
        s.materialRefractiveIndex (answerChoiceValue .C) := by
  dsimp [CylinderFigureReadout] at hFigure
  rcases hFigure with
    ⟨hR, hd, hair, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hEntryAngle, hRefractedAngle, _, _, _, _, hSeparation,
      hAngleDecomposition, hHalfAngle, _, _, _⟩
  dsimp [GeometricalOpticsLaws, SnellLawAtInterface,
    SpecularReflectionAtMirror] at hOptics
  rcases hOptics with ⟨hEntrySnell, _, _⟩
  -- The measured separation fixes the entry sine, while the inscribed-angle
  -- relation makes the refracted angle half of the entry angle.
  rw [hR, hd] at hSeparation
  have hSinEntry :
      Real.sin s.entryIncidenceAngle = (1 : ℝ) / 2 := by
    nlinarith only [hSeparation]
  have hRefractedEqHalf :
      s.entryRefractionAngle = s.entryIncidenceAngle / 2 := by
    nlinarith only [hAngleDecomposition, hHalfAngle]
  have hEntryEqTwiceRefracted :
      s.entryIncidenceAngle = 2 * s.entryRefractionAngle := by
    nlinarith only [hRefractedEqHalf]
  -- Apply Snell's law and the double-angle formula, cancelling the positive
  -- sine of the refracted angle.
  have hSinRefractedPos :
      0 < Real.sin s.entryRefractionAngle := by
    apply Real.sin_pos_of_pos_of_lt_pi hRefractedAngle.1
    nlinarith only [hRefractedAngle.2, Real.pi_pos]
  have hSinDouble := Real.sin_two_mul s.entryRefractionAngle
  rw [← hEntryEqTwiceRefracted] at hSinDouble
  rw [hair] at hEntrySnell
  norm_num at hEntrySnell
  have hIndexTimesSin :
      Real.sin s.entryRefractionAngle * s.materialRefractiveIndex =
        Real.sin s.entryRefractionAngle *
          (2 * Real.cos s.entryRefractionAngle) := by
    calc
      Real.sin s.entryRefractionAngle * s.materialRefractiveIndex =
          s.materialRefractiveIndex *
            Real.sin s.entryRefractionAngle := mul_comm _ _
      _ = Real.sin s.entryIncidenceAngle := hEntrySnell.symm
      _ = 2 * Real.sin s.entryRefractionAngle *
          Real.cos s.entryRefractionAngle := hSinDouble
      _ = Real.sin s.entryRefractionAngle *
          (2 * Real.cos s.entryRefractionAngle) := by ring
  have hIndexEqTwiceCos :
      s.materialRefractiveIndex =
        2 * Real.cos s.entryRefractionAngle :=
    mul_left_cancel₀ (ne_of_gt hSinRefractedPos) hIndexTimesSin
  -- The Pythagorean and cosine double-angle identities determine the square
  -- of the refractive index.
  have hCosEntryPos : 0 < Real.cos s.entryIncidenceAngle := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith only [hEntryAngle.1, Real.pi_pos]
    · exact hEntryAngle.2
  have hCosEntrySq :
      Real.cos s.entryIncidenceAngle ^ 2 = (3 : ℝ) / 4 := by
    nlinarith only [hSinEntry,
      Real.sin_sq_add_cos_sq s.entryIncidenceAngle]
  have hTwiceCosEntryNonneg :
      0 ≤ 2 * Real.cos s.entryIncidenceAngle := by
    positivity
  have hSqrtThreeEqTwiceCosEntry :
      Real.sqrt 3 = 2 * Real.cos s.entryIncidenceAngle := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) hTwiceCosEntryNonneg]
    nlinarith only [hCosEntrySq]
  have hCosDouble := Real.cos_two_mul s.entryRefractionAngle
  rw [← hEntryEqTwiceRefracted] at hCosDouble
  have hCosRefractedSq :
      Real.cos s.entryRefractionAngle ^ 2 =
        (2 + Real.sqrt 3) / 4 := by
    nlinarith only [hCosDouble, hSqrtThreeEqTwiceCosEntry]
  have hIndexSq :
      s.materialRefractiveIndex ^ 2 = 2 + Real.sqrt 3 := by
    rw [hIndexEqTwiceCos]
    nlinarith only [hCosRefractedSq]
  -- Positivity of a physical refractive index selects the positive root.
  have hRadicandNonneg : 0 ≤ 2 + Real.sqrt 3 := by
    positivity
  have hIndexNonneg : 0 ≤ s.materialRefractiveIndex := by
    nlinarith only [s.materialRefractiveIndex_gt_one]
  have hExact :
      s.materialRefractiveIndex = Real.sqrt (2 + Real.sqrt 3) := by
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq hRadicandNonneg hIndexNonneg]
    nlinarith only [hIndexSq]
  -- Rational square bounds certify rounding to the nearest hundredth.
  have hSqrtThreeSq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtThreeNonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hSqrtThreeLower : (1732 : ℝ) / 1000 < Real.sqrt 3 := by
    nlinarith only [hSqrtThreeSq, hSqrtThreeNonneg]
  have hSqrtThreeUpper : Real.sqrt 3 < (1733 : ℝ) / 1000 := by
    nlinarith only [hSqrtThreeSq, hSqrtThreeNonneg]
  have hIndexLower : (1925 : ℝ) / 1000 < s.materialRefractiveIndex := by
    nlinarith only [hIndexSq, s.materialRefractiveIndex_gt_one,
      hSqrtThreeLower]
  have hIndexUpper : s.materialRefractiveIndex < (1935 : ℝ) / 1000 := by
    nlinarith only [hIndexSq, s.materialRefractiveIndex_gt_one,
      hSqrtThreeUpper]
  -- The interval `(1.925, 1.935)` is exactly the rounding interval for `1.93`.
  refine ⟨hExact, ?_⟩
  dsimp [RoundsToNearestHundredth, answerChoiceValue]
  rw [abs_lt]
  constructor
  · nlinarith only [hIndexLower]
  · nlinarith only [hIndexUpper]

end PhyXMiniProblems.ProblemPhyXMini0020
