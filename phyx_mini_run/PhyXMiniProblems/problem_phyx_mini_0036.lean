import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0036

/-!
# Reflection and refraction at a water--glass interface

The diagram shows three directed rays in a two-dimensional plane of incidence.
The incident and reflected rays lie in water, while the refracted ray enters
glass.  Their physical directions are represented by unit vectors based at the
common point of incidence.  The displayed angles are real radian readouts of
the corresponding undirected angles to the appropriate side of the normal.

Refractive indices are dimensionless physical quantities, represented using
Physlib's dimension-tagged type `WithDim (1 : Dimension) ℝ`.  Snell's law and
the law of reflection are explicit governing-law hypotheses because the
available Physlib optics module does not yet supply geometrical-optics laws.
-/

/-- The two homogeneous optical media labelled `a` and `b` in the figure. -/
inductive OpticalMedium where
  | waterA
  | glassB
  deriving DecidableEq, Repr

/-- The three directed ray segments meeting at the water--glass interface. -/
inductive InterfaceRay where
  | incidentInWater
  | reflectedInWater
  | refractedInGlass
  deriving DecidableEq, Repr

/-- The medium traversed by each labelled ray segment in the figure. -/
def InterfaceRay.medium : InterfaceRay → OpticalMedium
  | .incidentInWater => .waterA
  | .reflectedInWater => .waterA
  | .refractedInGlass => .glassB

/-- Convert a scalar degree readout to a real-valued radian readout. -/
def degreesToRadians (degreeMeasure : ℝ) : ℝ :=
  degreeMeasure * Real.pi / 180

/--
The water--glass interface and the directed propagation vectors depicted in the
plane of incidence.  `normalTowardWater` points upward in the figure and
`tangentTowardRight` points to the right along the interface.
-/
structure WaterGlassInterfaceDiagram where
  /-- Common point at which all three directed rays meet the interface. -/
  incidencePoint : EuclideanSpace ℝ (Fin 2)
  /-- Displayed dashed normal, oriented from the glass toward the water. -/
  normalTowardWater : EuclideanSpace ℝ (Fin 2)
  /-- Rightward tangent direction along the planar interface. -/
  tangentTowardRight : EuclideanSpace ℝ (Fin 2)
  /-- Propagation direction of each labelled ray segment. -/
  propagationDirection : InterfaceRay → EuclideanSpace ℝ (Fin 2)
  /-- Dimensionless refractive index of each optical medium. -/
  refractiveIndex : OpticalMedium → WithDim (1 : Dimension) ℝ

/-- The figure label `θ_a`, measured between the incoming ray and the normal. -/
def thetaA (diagram : WaterGlassInterfaceDiagram) : ℝ :=
  InnerProductGeometry.angle
    (-diagram.propagationDirection .incidentInWater)
    diagram.normalTowardWater

/-- The figure label `θ_r`, measured between the reflected ray and the normal. -/
def thetaR (diagram : WaterGlassInterfaceDiagram) : ℝ :=
  InnerProductGeometry.angle
    (diagram.propagationDirection .reflectedInWater)
    diagram.normalTowardWater

/-- The figure label `θ_b`, measured from the normal directed into the glass. -/
def thetaB (diagram : WaterGlassInterfaceDiagram) : ℝ :=
  InnerProductGeometry.angle
    (diagram.propagationDirection .refractedInGlass)
    (-diagram.normalTowardWater)

/--
Primary-image and problem-statement readouts.  The unit and inner-product
conditions make the displayed normal and tangent a perpendicular frame.  The
sign conditions place the incident/reflected rays in water and the refracted
ray in glass, while all three propagate toward the right as drawn.

Only the incident angle and material indices are numerically specified here;
neither requested outgoing angle occurs as a figure readout.
-/
structure MatchesWaterGlassFigure
    (diagram : WaterGlassInterfaceDiagram) : Prop where
  normalUnit : ‖diagram.normalTowardWater‖ = 1
  tangentUnit : ‖diagram.tangentTowardRight‖ = 1
  normalPerpendicularToInterface :
    inner ℝ diagram.normalTowardWater diagram.tangentTowardRight = 0
  rayDirectionsUnit :
    ∀ ray : InterfaceRay, ‖diagram.propagationDirection ray‖ = 1
  raysPropagateRightward :
    ∀ ray : InterfaceRay,
      0 < inner ℝ (diagram.propagationDirection ray)
        diagram.tangentTowardRight
  incidentRayApproachesInterface :
    inner ℝ (diagram.propagationDirection .incidentInWater)
      diagram.normalTowardWater < 0
  reflectedRayRemainsInWater :
    0 < inner ℝ (diagram.propagationDirection .reflectedInWater)
      diagram.normalTowardWater
  refractedRayEntersGlass :
    inner ℝ (diagram.propagationDirection .refractedInGlass)
      diagram.normalTowardWater < 0
  waterIndexReadout :
    diagram.refractiveIndex .waterA = ⟨(133 : ℝ) / 100⟩
  glassIndexReadout :
    diagram.refractiveIndex .glassB = ⟨(38 : ℝ) / 25⟩
  incidentAngleReadout :
    thetaA diagram = degreesToRadians 60

/-- Positivity and principal optical-branch conditions for the ray model. -/
structure HasPhysicalOpticalParameters
    (diagram : WaterGlassInterfaceDiagram) : Prop where
  refractiveIndicesPositive :
    ∀ medium : OpticalMedium, 0 < (diagram.refractiveIndex medium).val
  rayAnglesOnPrincipalBranch :
    thetaA diagram ∈ Set.Icc 0 (Real.pi / 2) ∧
      thetaR diagram ∈ Set.Icc 0 (Real.pi / 2) ∧
      thetaB diagram ∈ Set.Icc 0 (Real.pi / 2)

/-- The law of reflection: the reflected and incident normal angles agree. -/
def SatisfiesLawOfReflection
    (diagram : WaterGlassInterfaceDiagram) : Prop :=
  thetaR diagram = thetaA diagram

/--
Snell's law at the labelled water--glass interface.  The `.val` projections are
scalar readouts of dimensionless Physlib quantities, so both sides are
dimensionless.
-/
def SatisfiesSnellLaw
    (diagram : WaterGlassInterfaceDiagram) : Prop :=
  (diagram.refractiveIndex .waterA).val * Real.sin (thetaA diagram) =
    (diagram.refractiveIndex .glassB).val * Real.sin (thetaB diagram)

/-- Labels of the four numerical answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The degree readout printed beside each answer-choice label. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 60
  | .B => (493 : ℝ) / 10
  | .C => 68
  | .D => (674 : ℝ) / 10

/-- Dataset metadata: the recorded multiple-choice answer is B. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A radian angle matches a one-decimal display to the nearest tenth degree. -/
def MatchesAnswerToNearestTenth
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |angleRadians - degreesToRadians choice.angleDegrees| ≤
    degreesToRadians ((1 : ℝ) / 20)

/--
For the depicted water-to-glass ray, reflection produces a `60°` outgoing
normal angle.  Snell's law produces the displayed principal-branch arcsine
formula for the refracted direction, whose nearest-tenth-degree readout is
`49.3°`, answer choice B.

This formalizes `thm:physics:phyx_mini_0036:target`.
-/
theorem reflectedAndRefractedDirections
    (diagram : WaterGlassInterfaceDiagram)
    (_figure : MatchesWaterGlassFigure diagram)
    (_parameters : HasPhysicalOpticalParameters diagram)
    (_reflection : SatisfiesLawOfReflection diagram)
    (_snell : SatisfiesSnellLaw diagram) :
    thetaR diagram = degreesToRadians 60 ∧
      thetaB diagram =
        Real.arcsin
          ((diagram.refractiveIndex .waterA).val /
              (diagram.refractiveIndex .glassB).val *
            Real.sin (thetaA diagram)) ∧
      MatchesAnswerToNearestTenth (thetaB diagram) .B := by
  have hIndexGlass :
      (diagram.refractiveIndex .glassB).val ≠ 0 :=
    ne_of_gt (_parameters.refractiveIndicesPositive .glassB)
  have hSinThetaB :
      Real.sin (thetaB diagram) =
        (diagram.refractiveIndex .waterA).val /
            (diagram.refractiveIndex .glassB).val *
          Real.sin (thetaA diagram) := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hIndexGlass).2
    simpa [mul_comm] using _snell.symm
  have hThetaB :
      thetaB diagram =
        Real.arcsin
          ((diagram.refractiveIndex .waterA).val /
              (diagram.refractiveIndex .glassB).val *
            Real.sin (thetaA diagram)) := by
    symm
    apply Real.arcsin_eq_of_sin_eq hSinThetaB
    exact
      ⟨by
        linarith [Real.pi_pos,
          _parameters.rayAnglesOnPrincipalBranch.2.2.1],
        _parameters.rayAnglesOnPrincipalBranch.2.2.2⟩
  constructor
  · exact _reflection.trans _figure.incidentAngleReadout
  constructor
  · exact hThetaB
  · rw [hThetaB]
    have sinBoundsSmall :
        ∀ {x : ℝ}, 0 < x → x ≤ 1 →
          Real.sin x < x ∧ x - x ^ 3 / 4 < Real.sin x := by
      intro x hx hxOne
      have habs : |x| ≤ 1 := by
        simpa [abs_of_nonneg hx.le] using hxOne
      have hu := le_of_abs_le (Real.sin_bound habs)
      have hl := neg_le_of_abs_le (Real.sin_bound habs)
      rw [abs_of_nonneg hx.le, sub_le_iff_le_add'] at hu
      rw [le_sub_iff_add_le, abs_of_nonneg hx.le] at hl
      have hxPow : x ^ 4 ≤ x ^ 3 := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hx.le 3) hxOne
      have hxCube : 0 < x ^ 3 := pow_pos hx 3
      constructor <;> nlinarith
    have hu1 : Real.sqrt 2 ≤ (338 / 239 : ℝ) := by
      apply (Real.sqrt_le_left (by norm_num)).2
      norm_num
    have hu2 :
        Real.sqrt (2 + Real.sqrt 2) ≤ (704 / 381 : ℝ) := by
      calc
        Real.sqrt (2 + Real.sqrt 2) ≤
            Real.sqrt (2 + (338 / 239 : ℝ)) :=
          Real.sqrt_le_sqrt (by linarith)
        _ ≤ 704 / 381 := by
          apply (Real.sqrt_le_left (by norm_num)).2
          norm_num
    have hu3 :
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) ≤
          (1940 / 989 : ℝ) := by
      calc
        _ ≤ Real.sqrt (2 + (704 / 381 : ℝ)) :=
          Real.sqrt_le_sqrt (by linarith)
        _ ≤ 1940 / 989 := by
          apply (Real.sqrt_le_left (by norm_num)).2
          norm_num
    have hu4 :
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ≤
          (1447 / 727 : ℝ) := by
      calc
        _ ≤ Real.sqrt (2 + (1940 / 989 : ℝ)) :=
          Real.sqrt_le_sqrt (by linarith)
        _ ≤ 1447 / 727 := by
          apply (Real.sqrt_le_left (by norm_num)).2
          norm_num
    have hSeriesUpper :
        Real.sqrtTwoAddSeries 0 4 ≤ (1447 / 727 : ℝ) := by
      simpa [Real.sqrtTwoAddSeries] using hu4
    have hl1 : (41 / 29 : ℝ) ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have hl2 :
        (109 / 59 : ℝ) ≤ Real.sqrt (2 + Real.sqrt 2) := by
      calc
        (109 / 59 : ℝ) ≤ Real.sqrt (2 + (41 / 29 : ℝ)) := by
          apply Real.le_sqrt_of_sq_le
          norm_num
        _ ≤ Real.sqrt (2 + Real.sqrt 2) :=
          Real.sqrt_le_sqrt (by linarith)
    have hl3 :
        (865 / 441 : ℝ) ≤
          Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
      calc
        (865 / 441 : ℝ) ≤ Real.sqrt (2 + (109 / 59 : ℝ)) := by
          apply Real.le_sqrt_of_sq_le
          norm_num
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    have hl4 :
        (412 / 207 : ℝ) ≤
          Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
      calc
        (412 / 207 : ℝ) ≤ Real.sqrt (2 + (865 / 441 : ℝ)) := by
          apply Real.le_sqrt_of_sq_le
          norm_num
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    have hSeriesLower :
        (412 / 207 : ℝ) ≤ Real.sqrtTwoAddSeries 0 4 := by
      simpa [Real.sqrtTwoAddSeries] using hl4
    have hSeriesForLowerPi :
        Real.sqrtTwoAddSeries 0 4 ≤
          (2 : ℝ) - ((3.14 : ℝ) / 32) ^ 2 :=
      hSeriesUpper.trans (by norm_num)
    have hRadLower :
        (3.14 : ℝ) / 32 ≤
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hSinLt :=
      (sinBoundsSmall (x := Real.pi / 64) (by positivity)
        (by nlinarith [Real.pi_le_four])).1
    rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
      Real.sin_pi_over_two_pow_succ] at hSinLt
    have hPiLower : (3.14 : ℝ) < Real.pi := by
      nlinarith
    have hSeriesForUpperPi :
        (2 : ℝ) - (((3.15 : ℝ) - 1 / 256) / 32) ^ 2 ≤
          Real.sqrtTwoAddSeries 0 4 := by
      exact
        (by
          norm_num :
          (2 : ℝ) - (((3.15 : ℝ) - 1 / 256) / 32) ^ 2 ≤
            412 / 207).trans hSeriesLower
    have hRadUpper :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) ≤
          ((3.15 : ℝ) - 1 / 256) / 32 := by
      apply (Real.sqrt_le_left (by norm_num)).2
      nlinarith
    have hSinLower :=
      (sinBoundsSmall (x := Real.pi / 64) (by positivity)
        (by nlinarith [Real.pi_le_four])).2
    rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
      Real.sin_pi_over_two_pow_succ] at hSinLower
    have hPiCube : Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 :=
      pow_le_pow_left₀ Real.pi_nonneg Real.pi_le_four 3
    have hPiUpper : Real.pi < (3.15 : ℝ) := by
      nlinarith
    have hArgument :
        (diagram.refractiveIndex .waterA).val /
              (diagram.refractiveIndex .glassB).val *
            Real.sin (thetaA diagram) =
          133 * Real.sqrt 3 / 304 := by
      rw [_figure.waterIndexReadout, _figure.glassIndexReadout,
        _figure.incidentAngleReadout]
      change
        ((133 : ℝ) / 100) / ((38 : ℝ) / 25) *
            Real.sin (60 * Real.pi / 180) =
          _
      rw [show (60 : ℝ) * Real.pi / 180 = Real.pi / 3 by ring,
        Real.sin_pi_div_three]
      ring
    rw [hArgument]
    have hSqrtTwoUpper :
        Real.sqrt 2 ≤ (11482 / 8119 : ℝ) := by
      apply (Real.sqrt_le_left (by norm_num)).2
      norm_num
    have hSqrtTwoLower :
        (1393 / 985 : ℝ) ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have hSqrtThreeLower :
        (13775 / 7953 : ℝ) ≤ Real.sqrt 3 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have hSqrtThreeUpper :
        Real.sqrt 3 ≤ (1351 / 780 : ℝ) := by
      apply (Real.sqrt_le_left (by norm_num)).2
      norm_num
    let dLower : ℝ := 17 * Real.pi / 720
    have hdLowerPos : 0 < dLower := by
      dsimp [dLower]
      positivity
    have hdLowerLeOne : dLower ≤ 1 := by
      dsimp [dLower]
      nlinarith [Real.pi_le_four]
    have hSinDLower :
        Real.sin dLower ≤
          dLower - dLower ^ 3 / 6 + dLower ^ 4 * (5 / 96) := by
      have h :=
        le_of_abs_le
          (Real.sin_bound (x := dLower)
            (by
              simpa [abs_of_nonneg hdLowerPos.le] using hdLowerLeOne))
      rw [abs_of_nonneg hdLowerPos.le] at h
      linarith
    have hCosDLower :
        Real.cos dLower ≤
          1 - dLower ^ 2 / 2 + dLower ^ 4 * (5 / 96) := by
      have h :=
        le_of_abs_le
          (Real.cos_bound (x := dLower)
            (by
              simpa [abs_of_nonneg hdLowerPos.le] using hdLowerLeOne))
      rw [abs_of_nonneg hdLowerPos.le] at h
      linarith
    have hdLowerBound :
        (17 : ℝ) * 3.14 / 720 ≤ dLower := by
      dsimp [dLower]
      nlinarith
    have hdLowerUpperBound :
        dLower ≤ (17 : ℝ) * 3.15 / 720 := by
      dsimp [dLower]
      nlinarith
    have hdLowerBoundSq :
        ((17 : ℝ) * 3.14 / 720) ^ 2 ≤ dLower ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hdLowerBound 2
    have hdLowerBoundCube :
        ((17 : ℝ) * 3.14 / 720) ^ 3 ≤ dLower ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hdLowerBound 3
    have hdLowerUpperFourth :
        dLower ^ 4 ≤ ((17 : ℝ) * 3.15 / 720) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hdLowerUpperBound 4
    have hLowerTrigSumUpper :
        Real.cos dLower + Real.sin dLower ≤
          1 + (17 : ℝ) * 3.15 / 720 -
            ((17 : ℝ) * 3.14 / 720) ^ 2 / 2 -
            ((17 : ℝ) * 3.14 / 720) ^ 3 / 6 +
            2 * (((17 : ℝ) * 3.15 / 720) ^ 4 * (5 / 96)) := by
      linarith only [hSinDLower, hCosDLower, hdLowerUpperBound,
        hdLowerBoundSq, hdLowerBoundCube, hdLowerUpperFourth]
    have hLowerTrigIdentity :
        Real.sin (197 * Real.pi / 720) =
          Real.sqrt 2 / 2 *
            (Real.cos dLower + Real.sin dLower) := by
      dsimp [dLower]
      rw [show
          (197 : ℝ) * Real.pi / 720 =
            Real.pi / 4 + 17 * Real.pi / 720 by ring,
        Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
      ring
    have hdLowerLtPi : dLower < Real.pi := by
      dsimp [dLower]
      nlinarith only [Real.pi_pos]
    have hLowerTrigSumNonneg :
        0 ≤ Real.cos dLower + Real.sin dLower := by
      have hs : 0 ≤ Real.sin dLower :=
        (Real.sin_pos_of_pos_of_lt_pi hdLowerPos hdLowerLtPi).le
      have hc : 0 ≤ Real.cos dLower :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by
            dsimp [dLower]
            nlinarith only [Real.pi_pos],
          by
            dsimp [dLower]
            nlinarith only [Real.pi_pos]⟩
      linarith only [hs, hc]
    have hLowerProductUpper :
        Real.sqrt 2 / 2 *
              (Real.cos dLower + Real.sin dLower) ≤
            (11482 / 8119 : ℝ) / 2 *
              (1 + (17 : ℝ) * 3.15 / 720 -
                ((17 : ℝ) * 3.14 / 720) ^ 2 / 2 -
                ((17 : ℝ) * 3.14 / 720) ^ 3 / 6 +
                2 *
                  (((17 : ℝ) * 3.15 / 720) ^ 4 * (5 / 96))) := by
      apply mul_le_mul
      · nlinarith only [hSqrtTwoUpper]
      · exact hLowerTrigSumUpper
      · exact hLowerTrigSumNonneg
      · norm_num
    have hLowerRationalComparison :
        (11482 / 8119 : ℝ) / 2 *
              (1 + (17 : ℝ) * 3.15 / 720 -
                ((17 : ℝ) * 3.14 / 720) ^ 2 / 2 -
                ((17 : ℝ) * 3.14 / 720) ^ 3 / 6 +
                2 *
                  (((17 : ℝ) * 3.15 / 720) ^ 4 * (5 / 96))) ≤
            133 * Real.sqrt 3 / 304 := by
      calc
        _ ≤ 133 * (13775 / 7953 : ℝ) / 304 := by norm_num
        _ ≤ _ := by nlinarith only [hSqrtThreeLower]
    have hSinAtLower :
        Real.sin (197 * Real.pi / 720) ≤
          133 * Real.sqrt 3 / 304 := by
      rw [hLowerTrigIdentity]
      exact hLowerProductUpper.trans hLowerRationalComparison
    let dUpper : ℝ := 29 * Real.pi / 1200
    have hdUpperPos : 0 < dUpper := by
      dsimp [dUpper]
      positivity
    have hdUpperLeOne : dUpper ≤ 1 := by
      dsimp [dUpper]
      nlinarith only [Real.pi_le_four]
    have hSinDUpper :
        dUpper - dUpper ^ 3 / 6 - dUpper ^ 4 * (5 / 96) ≤
          Real.sin dUpper := by
      have h :=
        neg_le_of_abs_le
          (Real.sin_bound (x := dUpper)
            (by
              simpa [abs_of_nonneg hdUpperPos.le] using hdUpperLeOne))
      rw [abs_of_nonneg hdUpperPos.le] at h
      linarith
    have hCosDUpper :
        1 - dUpper ^ 2 / 2 - dUpper ^ 4 * (5 / 96) ≤
          Real.cos dUpper := by
      have h :=
        neg_le_of_abs_le
          (Real.cos_bound (x := dUpper)
            (by
              simpa [abs_of_nonneg hdUpperPos.le] using hdUpperLeOne))
      rw [abs_of_nonneg hdUpperPos.le] at h
      linarith
    have hdUpperLowerBound :
        (29 : ℝ) * 3.14 / 1200 ≤ dUpper := by
      dsimp [dUpper]
      nlinarith only [hPiLower]
    have hdUpperBound :
        dUpper ≤ (29 : ℝ) * 3.15 / 1200 := by
      dsimp [dUpper]
      nlinarith only [hPiUpper]
    have hdUpperBoundSq :
        dUpper ^ 2 ≤ ((29 : ℝ) * 3.15 / 1200) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdUpperBound 2
    have hdUpperBoundCube :
        dUpper ^ 3 ≤ ((29 : ℝ) * 3.15 / 1200) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hdUpperBound 3
    have hdUpperBoundFourth :
        dUpper ^ 4 ≤ ((29 : ℝ) * 3.15 / 1200) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hdUpperBound 4
    have hUpperTrigSumLower :
        1 + (29 : ℝ) * 3.14 / 1200 -
              ((29 : ℝ) * 3.15 / 1200) ^ 2 / 2 -
              ((29 : ℝ) * 3.15 / 1200) ^ 3 / 6 -
              2 * (((29 : ℝ) * 3.15 / 1200) ^ 4 * (5 / 96)) ≤
            Real.cos dUpper + Real.sin dUpper := by
      linarith only [hSinDUpper, hCosDUpper, hdUpperLowerBound,
        hdUpperBoundSq, hdUpperBoundCube, hdUpperBoundFourth]
    have hUpperTrigIdentity :
        Real.sin (329 * Real.pi / 1200) =
          Real.sqrt 2 / 2 *
            (Real.cos dUpper + Real.sin dUpper) := by
      dsimp [dUpper]
      rw [show
          (329 : ℝ) * Real.pi / 1200 =
            Real.pi / 4 + 29 * Real.pi / 1200 by ring,
        Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
      ring
    have hUpperRationalComparison :
        133 * Real.sqrt 3 / 304 ≤
            (1393 / 985 : ℝ) / 2 *
              (1 + (29 : ℝ) * 3.14 / 1200 -
                ((29 : ℝ) * 3.15 / 1200) ^ 2 / 2 -
                ((29 : ℝ) * 3.15 / 1200) ^ 3 / 6 -
                2 *
                  (((29 : ℝ) * 3.15 / 1200) ^ 4 * (5 / 96))) := by
      calc
        _ ≤ 133 * (1351 / 780 : ℝ) / 304 := by
          nlinarith only [hSqrtThreeUpper]
        _ ≤ _ := by norm_num
    have hUpperProductLower :
        (1393 / 985 : ℝ) / 2 *
              (1 + (29 : ℝ) * 3.14 / 1200 -
                ((29 : ℝ) * 3.15 / 1200) ^ 2 / 2 -
                ((29 : ℝ) * 3.15 / 1200) ^ 3 / 6 -
                2 *
                  (((29 : ℝ) * 3.15 / 1200) ^ 4 * (5 / 96))) ≤
            Real.sqrt 2 / 2 *
              (Real.cos dUpper + Real.sin dUpper) := by
      apply mul_le_mul
      · nlinarith only [hSqrtTwoLower]
      · exact hUpperTrigSumLower
      · norm_num
      · positivity
    have hSinAtUpper :
        133 * Real.sqrt 3 / 304 ≤
          Real.sin (329 * Real.pi / 1200) := by
      rw [hUpperTrigIdentity]
      exact hUpperRationalComparison.trans hUpperProductLower
    have hLowerAngleMem :
        (197 * Real.pi / 720 : ℝ) ∈
          Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have hUpperAngleMem :
        (329 * Real.pi / 1200 : ℝ) ∈
          Set.Ico (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [Real.pi_pos]
    have hArcsinLower :
        197 * Real.pi / 720 ≤
          Real.arcsin (133 * Real.sqrt 3 / 304) :=
      (Real.le_arcsin_iff_sin_le' hLowerAngleMem).2 hSinAtLower
    have hArcsinUpper :
        Real.arcsin (133 * Real.sqrt 3 / 304) ≤
          329 * Real.pi / 1200 :=
      (Real.arcsin_le_iff_le_sin' hUpperAngleMem).2 hSinAtUpper
    unfold MatchesAnswerToNearestTenth AnswerChoice.angleDegrees
      degreesToRadians
    rw [abs_le]
    constructor <;>
      nlinarith only [hArcsinLower, hArcsinUpper, Real.pi_pos]

end PhyXMiniProblems.ProblemPhyXMini0036
