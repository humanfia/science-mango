import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0137

/-!
# Apparent depth of goggles in a swimming pool

The diagram shows goggles at real depth `d = 1.0 m` below a planar
water--air interface.  Two physical rays leave the goggles and refract into
air; extending the emerging rays backward gives a virtual image at apparent
depth `d'`.  The two horizontal offsets are both labelled `x`.  The angle
labels are `θ₁` for the ray from the goggles, `θ₂` for its apparent backward
projection, and `θ₂'` for the emerging ray in air.

Lengths below are genuine dimensionful quantities.  Refractive indices and
radian angle readouts are dimensionless real numbers.  The numerical answer
is the first-order axis intercept of an exact near-axis Snell-law ray family;
no finite-angle identity such as `sin θ = θ` or `tan θ = θ` is assumed.
-/

open Dimension Filter
open scoped Topology

/-! ## Physical quantities and figure labels -/

/-- A physical length, represented independently of any choice of unit. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (quantity : DimLength) : ℝ :=
  (quantity ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The scalar readout of a physical length in metres. -/
def lengthInMetres (quantity : DimLength) : ℝ :=
  lengthReadout LengthUnit.meters quantity

/-- The homogeneous optical media on the two sides of the pool surface. -/
inductive OpticalMedium where
  | poolWater
  | ambientAir
  deriving DecidableEq, Repr

/-- Labels for the physical and apparent ray paths drawn in the figure. -/
inductive RayPathLabel where
  | leftPhysicalRay
  | rightPhysicalRay
  | apparentBackProjection
  deriving DecidableEq, Repr

/-- The three angle labels printed in the figure. -/
inductive FigureAngleLabel where
  | thetaOne
  | thetaTwo
  | thetaTwoPrime
  deriving DecidableEq, Repr

/-- Whether the viewing axis is normal or oblique to the water surface. -/
inductive ViewingRegime where
  | straightDownParaxial
  | oblique
  deriving DecidableEq, Repr

/--
The dimensionful distances and dimensionless optical readouts appearing in
the water--air apparent-depth diagram.  `lateralOffset` is the common figure
label `x`; `realDepth` and `apparentDepth` are the labels `d` and `d'`.

The angle field describes a family of rays by the scalar readout of their
lateral interface offset in a selected length unit.  The zero offset is the
straight-down optical axis.  No numerical value of `apparentDepth` is stored
in this setup.
-/
structure PoolGogglesDiagram where
  /-- Figure label `d`: vertical distance from the goggles to the surface. -/
  realDepth : DimLength
  /-- Figure label `d'`: depth of the virtual image below the surface. -/
  apparentDepth : DimLength
  /-- Common horizontal offset `x` on either side of the viewing axis. -/
  lateralOffset : DimLength
  /-- Dimensionless refractive index of each homogeneous medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Radian angle of a ray at a given scalar lateral-offset readout. -/
  angleRadiansAtOffset : LengthUnit → FigureAngleLabel → ℝ → ℝ
  /-- The direction from which the observer views the pool bottom. -/
  viewingRegime : ViewingRegime

/-! ## Figure data and physical assumptions -/

/--
Readouts supplied by the problem and diagram: `d = 1.0 m`, normal viewing,
and equality of the emerging-ray angle `θ₂'` with the corresponding angle
`θ₂` of its backward extension relative to the parallel vertical normals.
The last relation is exact near the optical axis; it is not a small-angle
approximation.
-/
structure MatchesPoolGogglesFigure (diagram : PoolGogglesDiagram) : Prop where
  realDepthReadoutMetres : lengthInMetres diagram.realDepth = 1.0
  viewingStraightDown : diagram.viewingRegime = .straightDownParaxial
  backProjectionAngle :
    ∀ unit : LengthUnit,
      ∀ᶠ offsetReadout : ℝ in 𝓝 0,
        diagram.angleRadiansAtOffset unit .thetaTwo offsetReadout =
          diagram.angleRadiansAtOffset unit .thetaTwoPrime offsetReadout

/-- Standard dimensionless refractive-index data used for water and air. -/
structure UsesStandardWaterAirIndices (diagram : PoolGogglesDiagram) : Prop where
  waterIndexReadout : diagram.refractiveIndex .poolWater = 4 / 3
  airIndexReadout : diagram.refractiveIndex .ambientAir = 1

/-- Positivity conditions selecting the physical apparent-depth branch. -/
structure HasPhysicalApparentDepthParameters
    (diagram : PoolGogglesDiagram) : Prop where
  refractiveIndexPositive :
    ∀ medium, 0 < diagram.refractiveIndex medium
  realDepthPositive :
    ∀ unit : LengthUnit, 0 < lengthReadout unit diagram.realDepth
  apparentDepthPositive :
    ∀ unit : LengthUnit, 0 < lengthReadout unit diagram.apparentDepth
  depictedLateralOffsetPositive :
    ∀ unit : LengthUnit, 0 < lengthReadout unit diagram.lateralOffset

/-! ## Governing optical laws -/

/--
Exact Snell law for the water-to-air interface,
`n_water sin θ₁ = n_air sin θ₂'`, for all sufficiently near-axis members of
the ray family.  Restricting the modeled ray family to a neighborhood of the
axis does not linearize the sine functions.
-/
def SatisfiesExactWaterAirSnellLaw
    (diagram : PoolGogglesDiagram) : Prop :=
  ∀ unit : LengthUnit,
    ∀ᶠ offsetReadout : ℝ in 𝓝 0,
      diagram.refractiveIndex .poolWater *
          Real.sin
            (diagram.angleRadiansAtOffset unit .thetaOne offsetReadout) =
        diagram.refractiveIndex .ambientAir *
          Real.sin
            (diagram.angleRadiansAtOffset unit .thetaTwoPrime offsetReadout)

/--
Local first-order geometry of the straight-down ray family.  All three angle
functions vanish on the optical axis.  The derivative of `θ₁` with respect
to lateral offset is `1/d`, while the derivative of the apparent backward
angle `θ₂` is `1/d'`.

`HasDerivAt` includes a little-o remainder at zero, so these fields express
the paraxial limit rather than globally asserting `x = d θ₁` or
`x = d' θ₂` at the depicted finite ray.  They are required in every length
unit, making the inverse-length slopes unit-consistent.
-/
structure SatisfiesParaxialApparentDepthLaws
    (diagram : PoolGogglesDiagram) : Prop where
  anglesVanishOnAxis :
    ∀ (unit : LengthUnit) (label : FigureAngleLabel),
      diagram.angleRadiansAtOffset unit label 0 = 0
  realRayAngleDerivative :
    ∀ unit : LengthUnit,
      HasDerivAt
        (diagram.angleRadiansAtOffset unit .thetaOne)
        (1 / lengthReadout unit diagram.realDepth) 0
  apparentBackProjectionAngleDerivative :
    ∀ unit : LengthUnit,
      HasDerivAt
        (diagram.angleRadiansAtOffset unit .thetaTwo)
        (1 / lengthReadout unit diagram.apparentDepth) 0

/-! ## Derived relation and answer -/

/--
Differentiating exact Snell refraction on the optical axis and using the two
local ray-geometry slopes gives the paraxial apparent-depth relation
`n_water d' = n_air d` in any length unit.
-/
lemma apparent_depth_index_relation
    (diagram : PoolGogglesDiagram)
    (figure : MatchesPoolGogglesFigure diagram)
    (physical : HasPhysicalApparentDepthParameters diagram)
    (exactOptics : SatisfiesExactWaterAirSnellLaw diagram)
    (optics : SatisfiesParaxialApparentDepthLaws diagram)
    (unit : LengthUnit) :
    diagram.refractiveIndex .poolWater *
        lengthReadout unit diagram.apparentDepth =
      diagram.refractiveIndex .ambientAir *
        lengthReadout unit diagram.realDepth := by
  have sinDerivativeAtZero : HasDerivAt Real.sin 1 0 := by
    rw [hasDerivAt_iff_tendsto]
    simp only [Real.sin_zero, sub_zero, smul_eq_mul, mul_one]
    apply squeeze_zero' (g := fun x : ℝ => x ^ 2)
    · exact
        Filter.Eventually.of_forall fun x =>
          mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (norm_nonneg _)
    · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one] with x hx
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
      by_cases hzero : x = 0
      · simp [hzero]
      · have hpos : 0 < |x| := abs_pos.mpr hzero
        have sinBound := Real.sin_bound hx
        have triangleBound :
            |Real.sin x - x| ≤
              |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := by
          calc
            |Real.sin x - x| =
                |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by
                  ring_nf
            _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| :=
              abs_sub _ _
        have cubeAbs : |x ^ 3 / 6| = |x| ^ 3 / 6 := by
          rw [abs_div, abs_pow]
          norm_num
        have mainBound : |Real.sin x - x| ≤ |x| ^ 3 := by
          rw [cubeAbs] at triangleBound
          nlinarith
            [abs_nonneg (Real.sin x - (x - x ^ 3 / 6)), abs_nonneg x]
        simp only [Real.norm_eq_abs]
        rw [inv_mul_le_iff₀ hpos]
        calc
          |Real.sin x - x| ≤ |x| ^ 3 := mainBound
          _ = |x| * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
    · have squareTendsToZero :
          Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) :=
        (continuous_id.pow 2).continuousAt
      norm_num at squareTendsToZero ⊢
      exact squareTendsToZero
  have sineOfDerivative
      {f : ℝ → ℝ} {slope : ℝ}
      (hf : HasDerivAt f slope 0) (hf0 : f 0 = 0) :
      HasDerivAt (fun x => Real.sin (f x)) slope 0 := by
    apply HasDerivAt.of_isLittleO
    simp only [hf0, Real.sin_zero, sub_zero, smul_eq_mul]
    have sinRemainder :
        (fun y : ℝ => Real.sin y - y) =o[𝓝 0] (fun y : ℝ => y) := by
      simpa only [Real.sin_zero, sub_zero, smul_eq_mul, mul_one] using
        sinDerivativeAtZero.isLittleO
    have fTendsToZero : Tendsto f (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, hf0] using hf.continuousAt
    have composedRemainder :=
      Asymptotics.IsLittleO.comp_tendsto sinRemainder fTendsToZero
    have composedRemainder' :
        (fun x => Real.sin (f x) - f x) =o[𝓝 0] (fun x => f x) := by
      change
        (fun x => Real.sin (f x) - f x) =o[𝓝 0] (fun x => f x)
        at composedRemainder
      exact composedRemainder
    have fIsBigO : (fun x => f x) =O[𝓝 0] (fun x : ℝ => x) := by
      simpa only [hf0, sub_zero] using hf.isBigO_sub
    have firstRemainder :
        (fun x => Real.sin (f x) - f x) =o[𝓝 0] (fun x : ℝ => x) :=
      Asymptotics.IsLittleO.trans_isBigO composedRemainder' fIsBigO
    have secondRemainder :
        (fun x => f x - x * slope) =o[𝓝 0] (fun x : ℝ => x) := by
      simpa only [hf0, sub_zero, smul_eq_mul] using hf.isLittleO
    have combinedRemainder :=
      Asymptotics.IsLittleO.add firstRemainder secondRemainder
    exact
      Asymptotics.IsLittleO.congr_left combinedRemainder
        (fun x => by ring)
  have constTimesDerivative
      {f : ℝ → ℝ} {slope constant : ℝ}
      (hf : HasDerivAt f slope 0) :
      HasDerivAt (fun x => constant * f x) (constant * slope) 0 := by
    apply HasDerivAt.of_isLittleO
    have scaledRemainder :=
      Asymptotics.IsLittleO.const_mul_left hf.isLittleO constant
    exact
      Asymptotics.IsLittleO.congr_left scaledRemainder
        (fun x => by
          simp only [smul_eq_mul]
          ring)
  have thetaOneDerivative :=
    optics.realRayAngleDerivative unit
  have thetaTwoDerivative :=
    optics.apparentBackProjectionAngleDerivative unit
  have thetaTwoPrimeDerivative :
      HasDerivAt
        (diagram.angleRadiansAtOffset unit .thetaTwoPrime)
        (1 / lengthReadout unit diagram.apparentDepth) 0 :=
    thetaTwoDerivative.congr_of_eventuallyEq
      (Filter.EventuallyEq.symm (figure.backProjectionAngle unit))
  have leftDerivative :
      HasDerivAt
        (fun offset =>
          diagram.refractiveIndex .poolWater *
            Real.sin
              (diagram.angleRadiansAtOffset unit .thetaOne offset))
        (diagram.refractiveIndex .poolWater *
          (1 / lengthReadout unit diagram.realDepth)) 0 :=
    constTimesDerivative
      (sineOfDerivative thetaOneDerivative
        (optics.anglesVanishOnAxis unit .thetaOne))
  have rightDerivative :
      HasDerivAt
        (fun offset =>
          diagram.refractiveIndex .ambientAir *
            Real.sin
              (diagram.angleRadiansAtOffset unit .thetaTwoPrime offset))
        (diagram.refractiveIndex .ambientAir *
          (1 / lengthReadout unit diagram.apparentDepth)) 0 :=
    constTimesDerivative
      (sineOfDerivative thetaTwoPrimeDerivative
        (optics.anglesVanishOnAxis unit .thetaTwoPrime))
  have slopeRelation :
      diagram.refractiveIndex .poolWater *
          (1 / lengthReadout unit diagram.realDepth) =
        diagram.refractiveIndex .ambientAir *
          (1 / lengthReadout unit diagram.apparentDepth) :=
    (leftDerivative.congr_of_eventuallyEq
      (Filter.EventuallyEq.symm (exactOptics unit))).unique rightDerivative
  have realDepthNonzero :
      lengthReadout unit diagram.realDepth ≠ 0 :=
    ne_of_gt (physical.realDepthPositive unit)
  have apparentDepthNonzero :
      lengthReadout unit diagram.apparentDepth ≠ 0 :=
    ne_of_gt (physical.apparentDepthPositive unit)
  field_simp [realDepthNonzero, apparentDepthNonzero] at slopeRelation
  simpa [mul_comm] using slopeRelation

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Apparent depth in metres printed next to each answer choice. -/
def displayedApparentDepthMetres : AnswerChoice → ℝ
  | .A => 0.79
  | .B => 0.77
  | .C => 0.75
  | .D => 0.73

/-- A displayed answer agrees with the apparent-depth readout of the model. -/
def IsDisplayedApparentDepthAnswer
    (diagram : PoolGogglesDiagram) (choice : AnswerChoice) : Prop :=
  lengthInMetres diagram.apparentDepth =
    displayedApparentDepthMetres choice

/--
For goggles at real depth `1.0 m`, with `n_water = 4/3` and `n_air = 1`,
the first-order straight-down axis intercept gives apparent depth `0.75 m`,
answer C.

Blueprint: `thm:physics:phyx_mini_0137:target`.
-/
theorem problem_phyx_mini_0137
    (diagram : PoolGogglesDiagram)
    (figure : MatchesPoolGogglesFigure diagram)
    (indices : UsesStandardWaterAirIndices diagram)
    (physical : HasPhysicalApparentDepthParameters diagram)
    (exactOptics : SatisfiesExactWaterAirSnellLaw diagram)
    (optics : SatisfiesParaxialApparentDepthLaws diagram) :
    lengthInMetres diagram.apparentDepth = 0.75 ∧
      IsDisplayedApparentDepthAnswer diagram .C := by
  have indexRelation :=
    apparent_depth_index_relation diagram figure physical exactOptics optics
      LengthUnit.meters
  have realDepthValue :
      lengthReadout LengthUnit.meters diagram.realDepth = 1 :=
    calc
      lengthReadout LengthUnit.meters diagram.realDepth = 1.0 := by
        simpa [lengthInMetres] using figure.realDepthReadoutMetres
      _ = 1 := by norm_num
  have apparentDepthValue :
      lengthInMetres diagram.apparentDepth = 0.75 := by
    unfold lengthInMetres
    rw [indices.waterIndexReadout, indices.airIndexReadout,
      realDepthValue] at indexRelation
    norm_num at indexRelation ⊢
    linarith
  constructor
  · exact apparentDepthValue
  · simpa [IsDisplayedApparentDepthAnswer, displayedApparentDepthMetres] using
      apparentDepthValue

end PhyXMiniProblems.ProblemPhyXMini0137
