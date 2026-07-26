import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Speed

/-!
# Refraction from material X through water into air

This file formalizes `phyx_mini_0091`.  A light ray travels upward through a
slab of material X, a water layer, and then air.  Refractive indices are
dimensionless scalar readouts.  All angle fields are real radian readouts, and
their names record whether they are measured from a surface or its normal.

The source image is treated as primary evidence: its `65°` arc is drawn from
the horizontal X--water interface, whereas the `48°` arc is drawn from the
vertical normal in water.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0091

/-! ## Optical and geometric roles -/

/-- Convert a degree readout to the radian scalar used by `Real.sin`. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- The two-dimensional plane of the beaker cross-section. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/-- A propagation direction is represented by a nonzero vector. -/
abbrev RayDirection := RayVector ℝ DiagramPlane

/-- A light phase speed with its length-per-time dimension retained. -/
abbrev OpticalSpeed :=
  Dimensionful (WithDim (Dimension.L𝓭 * Dimension.T𝓭⁻¹) ℝ)

/-- The numerical value of a dimensionful speed in SI metres per second. -/
def speedInMetersPerSecond (speed : OpticalSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-- The three homogeneous optical media, in upward propagation order. -/
inductive OpticalMedium where
  | materialX
  | water
  | air
  deriving DecidableEq, Repr

/-- The two horizontal interfaces crossed by the ray. -/
inductive LayerInterface where
  | materialXWater
  | waterAir
  deriving DecidableEq, Repr

/-- The three directed portions of the same upward-traveling light ray. -/
inductive RaySegment where
  | inMaterialX
  | inWater
  | inAir
  deriving DecidableEq, Repr

/-- The optical medium containing each ray segment. -/
def segmentMedium : RaySegment → OpticalMedium
  | .inMaterialX => .materialX
  | .inWater => .water
  | .inAir => .air

/-- The incident medium at each interface, following the upward ray. -/
def incidentMedium : LayerInterface → OpticalMedium
  | .materialXWater => .materialX
  | .waterAir => .water

/-- The transmitted medium at each interface, following the upward ray. -/
def transmittedMedium : LayerInterface → OpticalMedium
  | .materialXWater => .water
  | .waterAir => .air

/-- The incident ray segment at each interface. -/
def incidentSegment : LayerInterface → RaySegment
  | .materialXWater => .inMaterialX
  | .waterAir => .inWater

/-- The transmitted ray segment at each interface. -/
def transmittedSegment : LayerInterface → RaySegment
  | .materialXWater => .inWater
  | .waterAir => .inAir

/-- A reference interface whose upward normal is used for each segment. -/
def referenceInterface : RaySegment → LayerInterface
  | .inMaterialX => .materialXWater
  | .inWater => .materialXWater
  | .inAir => .waterAir

/-- Physical quantities and labelled directions in the layered ray diagram. -/
structure LayeredRefractionDiagram where
  /-- Dimensionless refractive index of each homogeneous medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Dimensionful phase speed of light in each homogeneous medium. -/
  phaseSpeed : OpticalMedium → OpticalSpeed
  /-- Nonzero propagation direction of each part of the light ray. -/
  rayDirection : RaySegment → RayDirection
  /-- The vertical, upward-pointing normal at each horizontal interface. -/
  upwardNormalDirection : LayerInterface → RayDirection
  /-- A consistently rightward tangent direction along each interface. -/
  interfaceTangentDirection : LayerInterface → RayDirection
  /-- Radian angle between each ray segment and the upward normal. -/
  angleFromNormalRadians : RaySegment → ℝ
  /-- Radian angle between each ray segment and the horizontal interface. -/
  angleFromSurfaceRadians : RaySegment → ℝ

/-- The undirected radian angle between two nonzero diagram directions. -/
def angleBetweenDirections (first second : RayDirection) : ℝ :=
  InnerProductGeometry.angle first.1 second.1

/-- The principal geometrical-optics branch for an upward-traveling ray. -/
def IsPhysicalAcuteAngle (angleRadians : ℝ) : Prop :=
  0 ≤ angleRadians ∧ angleRadians ≤ Real.pi / 2

/-! ## Figure data and governing laws -/

/--
The refractive-index readout is the vacuum light speed divided by the phase
speed in the medium.  The equality is stated after taking SI scalar readouts;
both speeds themselves retain Physlib's length-per-time dimension.
-/
structure ModelsRefractiveIndexFromPhaseSpeed
    (diagram : LayeredRefractionDiagram) : Prop where
  phaseSpeedsPositive :
    ∀ medium, 0 < speedInMetersPerSecond (diagram.phaseSpeed medium)
  indexTimesPhaseSpeedEqualsVacuumSpeed :
    ∀ medium,
      diagram.refractiveIndex medium *
          speedInMetersPerSecond (diagram.phaseSpeed medium) =
        speedInMetersPerSecond DimSpeed.speedOfLight

/--
The two angle labels in the source image and the standard idealized indices of
water and air.  The unknown refractive index of material X is deliberately not
assigned a value, and no air-angle answer occurs in these data.
-/
structure MatchesProblemData (diagram : LayeredRefractionDiagram) : Prop where
  waterNormalAngleReadout :
    diagram.angleFromNormalRadians .inWater = degreesToRadians 48
  materialXSurfaceAngleReadout :
    diagram.angleFromSurfaceRadians .inMaterialX = degreesToRadians 65
  standardWaterRefractiveIndex :
    diagram.refractiveIndex .water = (4 / 3 : ℝ)
  standardAirRefractiveIndex :
    diagram.refractiveIndex .air = 1

/-- Positivity and principal-branch conditions for the optical quantities. -/
structure HasPhysicalOpticalParameters
    (diagram : LayeredRefractionDiagram) : Prop where
  refractiveIndicesPositive :
    ∀ medium, 0 < diagram.refractiveIndex medium
  normalAnglesPhysical :
    ∀ segment, IsPhysicalAcuteAngle (diagram.angleFromNormalRadians segment)
  surfaceAnglesPhysical :
    ∀ segment, IsPhysicalAcuteAngle (diagram.angleFromSurfaceRadians segment)

/--
Geometric relations represented by the horizontal interfaces, vertical dashed
normals, and the three piecewise-linear portions of the refracted ray.
-/
structure SatisfiesLayeredFigureGeometry
    (diagram : LayeredRefractionDiagram) : Prop where
  parallelInterfaceNormals :
    diagram.upwardNormalDirection .materialXWater =
      diagram.upwardNormalDirection .waterAir
  parallelInterfaceTangents :
    diagram.interfaceTangentDirection .materialXWater =
      diagram.interfaceTangentDirection .waterAir
  tangentNormalPerpendicular :
    ∀ interface,
      angleBetweenDirections
          (diagram.interfaceTangentDirection interface)
          (diagram.upwardNormalDirection interface) =
        Real.pi / 2
  normalAnglesFromDirections :
    ∀ segment,
      diagram.angleFromNormalRadians segment =
        angleBetweenDirections
          (diagram.rayDirection segment)
          (diagram.upwardNormalDirection (referenceInterface segment))
  surfaceAnglesFromDirections :
    ∀ segment,
      diagram.angleFromSurfaceRadians segment =
        angleBetweenDirections
          (diagram.rayDirection segment)
          (diagram.interfaceTangentDirection (referenceInterface segment))
  normalAndSurfaceAnglesComplementary :
    ∀ segment,
      diagram.angleFromNormalRadians segment +
          diagram.angleFromSurfaceRadians segment =
        Real.pi / 2

/-- Snell's law `n₁ sin θ₁ = n₂ sin θ₂` at one horizontal interface. -/
def SatisfiesSnellsLawAt
    (diagram : LayeredRefractionDiagram)
    (interface : LayerInterface) : Prop :=
  diagram.refractiveIndex (incidentMedium interface) *
      Real.sin (diagram.angleFromNormalRadians (incidentSegment interface)) =
    diagram.refractiveIndex (transmittedMedium interface) *
      Real.sin (diagram.angleFromNormalRadians (transmittedSegment interface))

/-- The upward-traveling light ray obeys Snell's law at both interfaces. -/
structure ObeysSnellsLaw (diagram : LayeredRefractionDiagram) : Prop where
  atInterface : ∀ interface, SatisfiesSnellsLawAt diagram interface

/-! ## Derived figure relation and multiple-choice target -/

/--
The `65°` surface-referenced label in material X corresponds to a `25°`
normal-referenced angle because the surface and its normal are perpendicular.
-/
lemma materialXNormalAngleIsTwentyFiveDegrees
    (diagram : LayeredRefractionDiagram)
    (hData : MatchesProblemData diagram)
    (hGeometry : SatisfiesLayeredFigureGeometry diagram) :
    diagram.angleFromNormalRadians .inMaterialX = degreesToRadians 25 := by
  have hComplement :=
    hGeometry.normalAndSurfaceAnglesComplementary RaySegment.inMaterialX
  rw [hData.materialXSurfaceAngleReadout] at hComplement
  dsimp [degreesToRadians] at hComplement ⊢
  linarith

/-- The four displayed answer labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Air-angle readout in degrees printed beside each answer choice. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 82
  | .B => 83
  | .C => 81
  | .D => 84

/-- Dataset metadata: the recorded answer label, not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- Absolute radian error between the physical air angle and one choice. -/
def angularErrorRadians
    (diagram : LayeredRefractionDiagram) (choice : AnswerChoice) : ℝ :=
  abs (diagram.angleFromNormalRadians .inAir -
    degreesToRadians choice.angleDegrees)

/--
For the depicted layered path, the standard water and air indices, the
principal angle branch, and Snell's law place the air angle within half a
degree of `82°`.  Consequently option A is the unique closest displayed
choice.

Blueprint: `thm:physics:phyx_mini_0091:target`.
-/
theorem airAngleRoundsToAnswerA
    (diagram : LayeredRefractionDiagram)
    (hData : MatchesProblemData diagram)
    (hIndexSpeed : ModelsRefractiveIndexFromPhaseSpeed diagram)
    (hPhysical : HasPhysicalOpticalParameters diagram)
    (hGeometry : SatisfiesLayeredFigureGeometry diagram)
    (hSnell : ObeysSnellsLaw diagram) :
    abs (diagram.angleFromNormalRadians .inAir -
        degreesToRadians AnswerChoice.A.angleDegrees) <
      degreesToRadians (1 / 2) ∧
    ∀ choice, choice ≠ .A →
      angularErrorRadians diagram .A < angularErrorRadians diagram choice := by
  have hPiLower : (3.14 : ℝ) < Real.pi := by
    have h0 :
        (9987961 : ℝ) / 10000000 <
          Real.cos ((157 : ℝ) / 3200) := by
      have hb := Real.cos_bound (x := (157 : ℝ) / 3200)
        (by norm_num [abs_of_nonneg])
      rw [abs_le] at hb
      norm_num [abs_of_nonneg] at hb ⊢
      linarith
    have h1 :
        (9951872 : ℝ) / 10000000 <
          Real.cos ((157 : ℝ) / 1600) := by
      rw [show (157 : ℝ) / 1600 = 2 * (157 / 3200) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h0]
    have h2 :
        (980795 : ℝ) / 1000000 <
          Real.cos ((157 : ℝ) / 800) := by
      rw [show (157 : ℝ) / 800 = 2 * (157 / 1600) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h1]
    have h3 :
        (923917 : ℝ) / 1000000 <
          Real.cos ((157 : ℝ) / 400) := by
      rw [show (157 : ℝ) / 400 = 2 * (157 / 800) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h2]
    have h4 :
        (70724 : ℝ) / 100000 <
          Real.cos ((157 : ℝ) / 200) := by
      rw [show (157 : ℝ) / 200 = 2 * (157 / 400) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h3]
    have h5 : 0 < Real.cos ((157 : ℝ) / 100) := by
      rw [show (157 : ℝ) / 100 = 2 * (157 / 200) by norm_num,
        Real.cos_two_mul]
      nlinarith only [h4]
    by_contra h
    have hpi : Real.pi / 2 ≤ (157 : ℝ) / 100 := by
      norm_num at h ⊢
      linarith
    have hnonpos :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hpi (by
        have htwo := Real.two_le_pi
        norm_num at htwo ⊢
        linarith)
    linarith only [h5, hnonpos]
  have hPiUpper : Real.pi < (3.15 : ℝ) := by
    have h0 :
        Real.cos ((315 : ℝ) / 6400) <
          (9987891 : ℝ) / 10000000 := by
      have hb := Real.cos_bound (x := (315 : ℝ) / 6400)
        (by norm_num [abs_of_nonneg])
      rw [abs_le] at hb
      norm_num [abs_of_nonneg] at hb ⊢
      linarith
    have h1 :
        Real.cos ((315 : ℝ) / 3200) <
          (9951594 : ℝ) / 10000000 := by
      rw [show (315 : ℝ) / 3200 = 2 * (315 / 6400) by norm_num,
        Real.cos_two_mul]
      have hcos : 0 ≤ Real.cos ((315 : ℝ) / 6400) :=
        Real.cos_nonneg_of_mem_Icc (by
          constructor <;> nlinarith [Real.one_le_pi_div_two])
      nlinarith only [h0, hcos]
    have h2 :
        Real.cos ((315 : ℝ) / 1600) <
          (9806845 : ℝ) / 10000000 := by
      rw [show (315 : ℝ) / 1600 = 2 * (315 / 3200) by norm_num,
        Real.cos_two_mul]
      have hcos : 0 ≤ Real.cos ((315 : ℝ) / 3200) :=
        Real.cos_nonneg_of_mem_Icc (by
          constructor <;> nlinarith [Real.one_le_pi_div_two])
      nlinarith only [h1, hcos]
    have h3 :
        Real.cos ((315 : ℝ) / 800) <
          (923485 : ℝ) / 1000000 := by
      rw [show (315 : ℝ) / 800 = 2 * (315 / 1600) by norm_num,
        Real.cos_two_mul]
      have hcos : 0 ≤ Real.cos ((315 : ℝ) / 1600) :=
        Real.cos_nonneg_of_mem_Icc (by
          constructor <;> nlinarith [Real.one_le_pi_div_two])
      nlinarith only [h2, hcos]
    have h4 :
        Real.cos ((315 : ℝ) / 400) <
          (70565 : ℝ) / 100000 := by
      rw [show (315 : ℝ) / 400 = 2 * (315 / 800) by norm_num,
        Real.cos_two_mul]
      have hcos : 0 ≤ Real.cos ((315 : ℝ) / 800) :=
        Real.cos_nonneg_of_mem_Icc (by
          constructor <;> nlinarith [Real.one_le_pi_div_two])
      nlinarith only [h3, hcos]
    have h5 : Real.cos ((315 : ℝ) / 200) < 0 := by
      rw [show (315 : ℝ) / 200 = 2 * (315 / 400) by norm_num,
        Real.cos_two_mul]
      have hcos : 0 ≤ Real.cos ((315 : ℝ) / 400) :=
        Real.cos_nonneg_of_mem_Icc (by
          constructor <;> nlinarith [Real.one_le_pi_div_two])
      nlinarith only [h4, hcos]
    by_contra h
    have hpi : (315 : ℝ) / 200 ≤ Real.pi / 2 := by
      norm_num at h ⊢
      linarith
    have hnonneg :=
      Real.cos_nonneg_of_mem_Icc (show
        (315 : ℝ) / 200 ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> nlinarith [Real.pi_pos])
    linarith only [h5, hnonneg]
  have smallTrigEnclosure :
      ∀ (x lo hi : ℝ), 0 ≤ lo → lo < x → x < hi → hi ≤ 1 →
        lo - hi ^ 3 / 6 - hi ^ 4 * (5 / 96) < Real.sin x ∧
        Real.sin x < hi - lo ^ 3 / 6 + hi ^ 4 * (5 / 96) ∧
        1 - hi ^ 2 / 2 - hi ^ 4 * (5 / 96) < Real.cos x ∧
        Real.cos x < 1 - lo ^ 2 / 2 + hi ^ 4 * (5 / 96) := by
    intro x lo hi hlo hloX hxHi hhi
    have hxPos : 0 < x := lt_of_le_of_lt hlo hloX
    have hx3Lower : lo ^ 3 < x ^ 3 :=
      pow_lt_pow_left₀ hloX hlo (by norm_num)
    have hx3Upper : x ^ 3 < hi ^ 3 :=
      pow_lt_pow_left₀ hxHi hxPos.le (by norm_num)
    have hx2Lower : lo ^ 2 < x ^ 2 :=
      pow_lt_pow_left₀ hloX hlo (by norm_num)
    have hx2Upper : x ^ 2 < hi ^ 2 :=
      pow_lt_pow_left₀ hxHi hxPos.le (by norm_num)
    have hx4Upper : x ^ 4 < hi ^ 4 :=
      pow_lt_pow_left₀ hxHi hxPos.le (by norm_num)
    have hsin := Real.sin_bound (x := x) (by
      rw [abs_of_pos hxPos]
      exact hxHi.le.trans hhi)
    have hcos := Real.cos_bound (x := x) (by
      rw [abs_of_pos hxPos]
      exact hxHi.le.trans hhi)
    rw [abs_of_pos hxPos, abs_le] at hsin hcos
    constructor
    · linarith only [hsin.1, hloX, hx3Upper, hx4Upper]
    constructor
    · linarith only [hsin.2, hxHi, hx3Lower, hx4Upper]
    constructor
    · linarith only [hcos.1, hx2Upper, hx4Upper]
    · linarith only [hcos.2, hx2Lower, hx4Upper]
  have hDelta := smallTrigEnclosure (Real.pi / 60)
    ((157 : ℝ) / 3000) ((21 : ℝ) / 400) (by norm_num)
    (by nlinarith only [hPiLower]) (by nlinarith only [hPiUpper])
    (by norm_num)
  have hLowerCorrection := smallTrigEnclosure (17 * Real.pi / 360)
    ((2669 : ℝ) / 18000) ((119 : ℝ) / 800) (by norm_num)
    (by nlinarith only [hPiLower]) (by nlinarith only [hPiUpper])
    (by norm_num)
  have hUpperCorrection := smallTrigEnclosure (Real.pi / 24)
    ((157 : ℝ) / 1200) ((21 : ℝ) / 160) (by norm_num)
    (by nlinarith only [hPiLower]) (by nlinarith only [hPiUpper])
    (by norm_num)
  norm_num at hDelta hLowerCorrection hUpperCorrection
  have hDeltaSumLower :
      (105092 : ℝ) / 100000 <
        Real.sin (Real.pi / 60) + Real.cos (Real.pi / 60) := by
    nlinarith only [hDelta.1, hDelta.2.2.1]
  have hDeltaSumUpper :
      Real.sin (Real.pi / 60) + Real.cos (Real.pi / 60) <
        (105111 : ℝ) / 100000 := by
    nlinarith only [hDelta.2.1, hDelta.2.2.2]
  have hSqrtTwoSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtTwoNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hSqrtTwoLower : (1.414212 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hSqrtTwoSq, hSqrtTwoNonnegative]
  have hSqrtTwoUpper : Real.sqrt 2 < (1.414214 : ℝ) := by
    nlinarith only [hSqrtTwoSq, hSqrtTwoNonnegative]
  have hHalfSqrtTwoLower :
      (0.707106 : ℝ) < Real.sqrt 2 / 2 := by
    linarith only [hSqrtTwoLower]
  have hHalfSqrtTwoUpper :
      Real.sqrt 2 / 2 < (0.707107 : ℝ) := by
    linarith only [hSqrtTwoUpper]
  have hSinFortyEightFormula :
      Real.sin (degreesToRadians 48) =
        (Real.sqrt 2 / 2) *
          (Real.sin (Real.pi / 60) + Real.cos (Real.pi / 60)) := by
    dsimp [degreesToRadians]
    rw [show 48 * Real.pi / 180 =
        Real.pi / 4 + Real.pi / 60 by ring,
      Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hProductLower :
      (0.707106 : ℝ) * (105092 / 100000) <
        (Real.sqrt 2 / 2) *
          (Real.sin (Real.pi / 60) + Real.cos (Real.pi / 60)) :=
    mul_lt_mul hHalfSqrtTwoLower hDeltaSumLower.le
      (by norm_num) (by linarith only [hSqrtTwoLower])
  have hProductUpper :
      (Real.sqrt 2 / 2) *
          (Real.sin (Real.pi / 60) + Real.cos (Real.pi / 60)) <
        (0.707107 : ℝ) * (105111 / 100000) :=
    mul_lt_mul hHalfSqrtTwoUpper hDeltaSumUpper.le
      (by linarith only [hDeltaSumLower]) (by norm_num)
  have hSinFortyEightLower :
      (0.7431 : ℝ) < Real.sin (degreesToRadians 48) := by
    rw [hSinFortyEightFormula]
    norm_num at hProductLower ⊢
    linarith only [hProductLower]
  have hSinFortyEightUpper :
      Real.sin (degreesToRadians 48) < (0.74325 : ℝ) := by
    rw [hSinFortyEightFormula]
    norm_num at hProductUpper ⊢
    linarith only [hProductUpper]
  have hLowerEndpointFormula :
      Real.sin (degreesToRadians (82 - 1 / 2)) =
        Real.cos (17 * Real.pi / 360) := by
    dsimp [degreesToRadians]
    rw [show (82 - (1 : ℝ) / 2) * Real.pi / 180 =
        Real.pi / 2 - 17 * Real.pi / 360 by ring,
      Real.sin_pi_div_two_sub]
  have hUpperEndpointFormula :
      Real.sin (degreesToRadians (82 + 1 / 2)) =
        Real.cos (Real.pi / 24) := by
    dsimp [degreesToRadians]
    rw [show (82 + (1 : ℝ) / 2) * Real.pi / 180 =
        Real.pi / 2 - Real.pi / 24 by ring,
      Real.sin_pi_div_two_sub]
  have hLowerEndpointSin :
      Real.sin (degreesToRadians (82 - 1 / 2)) <
        (98904 : ℝ) / 100000 := by
    rw [hLowerEndpointFormula]
    nlinarith only [hLowerCorrection.2.2.2]
  have hUpperEndpointSin :
      (99136 : ℝ) / 100000 <
        Real.sin (degreesToRadians (82 + 1 / 2)) := by
    rw [hUpperEndpointFormula]
    nlinarith only [hUpperCorrection.2.2.1]
  have hSnellWaterAir := hSnell.atInterface LayerInterface.waterAir
  change
    diagram.refractiveIndex .water *
        Real.sin (diagram.angleFromNormalRadians .inWater) =
      diagram.refractiveIndex .air *
        Real.sin (diagram.angleFromNormalRadians .inAir)
    at hSnellWaterAir
  rw [hData.standardWaterRefractiveIndex,
    hData.standardAirRefractiveIndex,
    hData.waterNormalAngleReadout] at hSnellWaterAir
  have hAirSine :
      Real.sin (diagram.angleFromNormalRadians .inAir) =
        (4 / 3 : ℝ) * Real.sin (degreesToRadians 48) := by
    norm_num at hSnellWaterAir ⊢
    linarith only [hSnellWaterAir]
  have hLowerSineComparison :
      Real.sin (degreesToRadians (82 - 1 / 2)) <
        Real.sin (diagram.angleFromNormalRadians .inAir) := by
    rw [hAirSine]
    nlinarith only [hLowerEndpointSin, hSinFortyEightLower]
  have hUpperSineComparison :
      Real.sin (diagram.angleFromNormalRadians .inAir) <
        Real.sin (degreesToRadians (82 + 1 / 2)) := by
    rw [hAirSine]
    nlinarith only [hUpperEndpointSin, hSinFortyEightUpper]
  have hAirPhysical := hPhysical.normalAnglesPhysical RaySegment.inAir
  change
    0 ≤ diagram.angleFromNormalRadians .inAir ∧
      diagram.angleFromNormalRadians .inAir ≤ Real.pi / 2
    at hAirPhysical
  have hAirAngleLower :
      degreesToRadians (82 - 1 / 2) <
        diagram.angleFromNormalRadians .inAir := by
    by_contra h
    have hAngleLe :
        diagram.angleFromNormalRadians .inAir ≤
          degreesToRadians (82 - 1 / 2) :=
      le_of_not_gt h
    have hSineLe := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := diagram.angleFromNormalRadians .inAir)
      (y := degreesToRadians (82 - 1 / 2))
      (by linarith only [hAirPhysical.1, Real.pi_pos])
      (by
        dsimp [degreesToRadians]
        nlinarith only [Real.pi_pos])
      hAngleLe
    linarith only [hLowerSineComparison, hSineLe]
  have hAirAngleUpper :
      diagram.angleFromNormalRadians .inAir <
        degreesToRadians (82 + 1 / 2) := by
    by_contra h
    have hAngleLe :
        degreesToRadians (82 + 1 / 2) ≤
          diagram.angleFromNormalRadians .inAir :=
      le_of_not_gt h
    have hSineLe := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := degreesToRadians (82 + 1 / 2))
      (y := diagram.angleFromNormalRadians .inAir)
      (by
        dsimp [degreesToRadians]
        nlinarith only [Real.pi_pos])
      hAirPhysical.2
      hAngleLe
    linarith only [hUpperSineComparison, hSineLe]
  have hClose :
      abs (diagram.angleFromNormalRadians .inAir -
          degreesToRadians 82) <
        degreesToRadians (1 / 2) := by
    rw [abs_lt]
    constructor
    · have h := hAirAngleLower
      dsimp [degreesToRadians] at h ⊢
      nlinarith only [h, Real.pi_pos]
    · have h := hAirAngleUpper
      dsimp [degreesToRadians] at h ⊢
      nlinarith only [h, Real.pi_pos]
  constructor
  · simpa only [AnswerChoice.angleDegrees] using hClose
  · intro choice hChoice
    cases choice with
    | A => exact (hChoice rfl).elim
    | B =>
        change
          abs (diagram.angleFromNormalRadians .inAir - degreesToRadians 82) <
            abs (diagram.angleFromNormalRadians .inAir - degreesToRadians 83)
        have hBNonpositive :
            diagram.angleFromNormalRadians .inAir - degreesToRadians 83 ≤ 0 := by
          have h := hAirAngleUpper
          dsimp [degreesToRadians] at h ⊢
          nlinarith only [h, Real.pi_pos]
        have hBFar :
            degreesToRadians (1 / 2) <
              abs (diagram.angleFromNormalRadians .inAir -
                degreesToRadians 83) := by
          rw [abs_of_nonpos hBNonpositive]
          have h := hAirAngleUpper
          dsimp [degreesToRadians] at h ⊢
          nlinarith only [h, Real.pi_pos]
        exact hClose.trans hBFar
    | C =>
        change
          abs (diagram.angleFromNormalRadians .inAir - degreesToRadians 82) <
            abs (diagram.angleFromNormalRadians .inAir - degreesToRadians 81)
        have hCNonnegative :
            0 ≤ diagram.angleFromNormalRadians .inAir - degreesToRadians 81 := by
          have h := hAirAngleLower
          dsimp [degreesToRadians] at h ⊢
          nlinarith only [h, Real.pi_pos]
        have hCFar :
            degreesToRadians (1 / 2) <
              abs (diagram.angleFromNormalRadians .inAir -
                degreesToRadians 81) := by
          rw [abs_of_nonneg hCNonnegative]
          have h := hAirAngleLower
          dsimp [degreesToRadians] at h ⊢
          nlinarith only [h, Real.pi_pos]
        exact hClose.trans hCFar
    | D =>
        change
          abs (diagram.angleFromNormalRadians .inAir - degreesToRadians 82) <
            abs (diagram.angleFromNormalRadians .inAir - degreesToRadians 84)
        have hDNonpositive :
            diagram.angleFromNormalRadians .inAir - degreesToRadians 84 ≤ 0 := by
          have h := hAirAngleUpper
          dsimp [degreesToRadians] at h ⊢
          nlinarith only [h, Real.pi_pos]
        have hDFar :
            degreesToRadians (1 / 2) <
              abs (diagram.angleFromNormalRadians .inAir -
                degreesToRadians 84) := by
          rw [abs_of_nonpos hDNonpositive]
          have h := hAirAngleUpper
          dsimp [degreesToRadians] at h ⊢
          nlinarith only [h, Real.pi_pos]
        exact hClose.trans hDFar

end PhyXMiniProblems.ProblemPhyXMini0091
