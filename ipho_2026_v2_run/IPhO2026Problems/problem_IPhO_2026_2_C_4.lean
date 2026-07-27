import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit

open Filter Topology

namespace IPhO2026Problems
namespace IPhO2026_2_C_4

noncomputable section

/--
The coordinate convention of Figure 2g.

The mirror is the upper half of the circle centered at the origin, the positive
`x`-axis points to the right, and the positive `y`-axis points upward.  All
length-valued real numbers below are numerical readouts in `lengthUnit`.
-/
structure Figure2gFrame where
  lengthUnit : LengthUnit
  radiusReadout : ℝ
  radiusReadout_pos : 0 < radiusReadout

/--
The scalar data of a reflected ray in Figure 2g.

The slope is dimensionless, while `interceptReadout` is a length readout in the
unit fixed by `Figure2gFrame`.
-/
structure ReflectedRayReadout where
  incidentAngle : ℝ
  slope : ℝ
  interceptReadout : ℝ

/-- The `y`-coordinate readout on a reflected line at the given `x` readout. -/
def reflectedLineYReadout (ray : ReflectedRayReadout) (xReadout : ℝ) : ℝ :=
  ray.slope * xReadout + ray.interceptReadout

/-- The `x` readout of the mirror point labelled by `θ` in Figure 2g. -/
def mirrorPointXReadout (frame : Figure2gFrame) (θ : ℝ) : ℝ :=
  frame.radiusReadout * Real.sin θ

/-- The `y` readout of the mirror point labelled by `θ` in Figure 2g. -/
def mirrorPointYReadout (frame : Figure2gFrame) (θ : ℝ) : ℝ :=
  frame.radiusReadout * Real.cos θ

/--
The specular-reflection law for the vertical, mutually parallel incident rays
in Figure 2g.

For nondegenerate angles the reflected line has slope `cot (2θ)`, intercept
`R / (2 cos θ)`, and passes through the corresponding point of the
half-cylindrical mirror.  The equations make this interface mathematically
constraining; the angle `θ = 0` is excluded from the finite-slope chart.
-/
def SatisfiesFigure2gReflectionLaw
    (frame : Figure2gFrame) (rayFamily : ℝ → ReflectedRayReadout) : Prop :=
  (∀ θ, (rayFamily θ).incidentAngle = θ) ∧
    (∀ θ, Real.sin (2 * θ) ≠ 0 →
      (rayFamily θ).slope = Real.cos (2 * θ) / Real.sin (2 * θ)) ∧
    (∀ θ, Real.cos θ ≠ 0 →
      (rayFamily θ).interceptReadout =
        frame.radiusReadout / (2 * Real.cos θ)) ∧
    (∀ θ, Real.sin (2 * θ) ≠ 0 → Real.cos θ ≠ 0 →
      reflectedLineYReadout (rayFamily θ) (mirrorPointXReadout frame θ) =
        mirrorPointYReadout frame θ)

/--
Neighboring reflected rays at angles `θ` (ray A) and `θ + Δθ` (ray B)
intersect at the supplied readouts, and these intersections tend to the
caustic as `Δθ → 0`, with `Δθ ≠ 0`.

The restriction `0 < |θ| < 1` is the nondegenerate small-angle chart used in
part C.4.
-/
def FormsNeighboringRayCaustic
    (rayFamily : ℝ → ReflectedRayReadout)
    (intersectionXReadout intersectionYReadout : ℝ → ℝ → ℝ)
    (causticXReadout causticYReadout : ℝ → ℝ) : Prop :=
  ∀ θ, 0 < |θ| → |θ| < 1 →
    (∀ᶠ Δθ in 𝓝[≠] (0 : ℝ),
      reflectedLineYReadout (rayFamily θ) (intersectionXReadout θ Δθ) =
          intersectionYReadout θ Δθ ∧
        reflectedLineYReadout (rayFamily (θ + Δθ))
            (intersectionXReadout θ Δθ) =
          intersectionYReadout θ Δθ) ∧
      Tendsto (fun Δθ => intersectionXReadout θ Δθ) (𝓝[≠] (0 : ℝ))
        (𝓝 (causticXReadout θ)) ∧
      Tendsto (fun Δθ => intersectionYReadout θ Δθ) (𝓝[≠] (0 : ℝ))
        (𝓝 (causticYReadout θ))

/--
The reusable result of part C.3, restated locally as required by the
natural-language-prerequisite policy.
-/
def HasPreviousPartC3Coordinates
    (frame : Figure2gFrame)
    (causticXReadout causticYReadout : ℝ → ℝ) : Prop :=
  (∀ θ, causticXReadout θ =
      frame.radiusReadout * (Real.sin θ) ^ 3) ∧
    (∀ θ, causticYReadout θ =
      (frame.radiusReadout / 2) * Real.cos θ *
        (2 - Real.cos (2 * θ)))

/--
A complete local optical model for Figure 2g and the caustic used in part C.4.
-/
structure Figure2gCausticModel where
  frame : Figure2gFrame
  reflectedRay : ℝ → ReflectedRayReadout
  intersectionXReadout : ℝ → ℝ → ℝ
  intersectionYReadout : ℝ → ℝ → ℝ
  causticXReadout : ℝ → ℝ
  causticYReadout : ℝ → ℝ
  reflectionLaw :
    SatisfiesFigure2gReflectionLaw frame reflectedRay
  neighboringRayEnvelope :
    FormsNeighboringRayCaustic reflectedRay intersectionXReadout
      intersectionYReadout causticXReadout causticYReadout
  previousPartC3 :
    HasPreviousPartC3Coordinates frame causticXReadout causticYReadout

/-- Figure label A: the reflected member of the family incident at `θ`. -/
def reflectedRayA (model : Figure2gCausticModel) (θ : ℝ) :
    ReflectedRayReadout :=
  model.reflectedRay θ

/--
Figure label B: the neighboring reflected member incident at `θ + Δθ`.
-/
def reflectedRayB (model : Figure2gCausticModel) (θ Δθ : ℝ) :
    ReflectedRayReadout :=
  model.reflectedRay (θ + Δθ)

/--
Candidate parameters for a leading small-angle power law
`Y_c = v |X_c|^(p/q) + u`.

`uReadout` is a length readout.  `vScaleReadout` is the numerical coefficient
in the selected length unit; for the answer `p/q = 2/3`, it has the associated
dimensional role `length^(1/3)`.
-/
structure CausticPowerLawParameters where
  uReadout : ℝ
  vScaleReadout : ℝ
  exponentNumerator : ℕ
  exponentDenominator : ℕ

/--
The rigorous meaning of the source's small-angle normal form: after removing
the vertical offset, the two sides are asymptotically equivalent as `θ → 0`
through nonzero angles.  The exponent is required to be a reduced fraction.
-/
def HasSmallAnglePowerLaw
    (model : Figure2gCausticModel)
    (parameters : CausticPowerLawParameters) : Prop :=
  parameters.exponentDenominator ≠ 0 ∧
    Nat.Coprime parameters.exponentNumerator
      parameters.exponentDenominator ∧
    Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ => model.causticYReadout θ - parameters.uReadout)
      (fun θ =>
        parameters.vScaleReadout *
          Real.rpow |model.causticXReadout θ|
            ((parameters.exponentNumerator : ℝ) /
              (parameters.exponentDenominator : ℝ)))

/--
As `Δθ → 0`, every fixed nonzero `θ` eventually satisfies the source
hierarchy `|Δθ| < |θ|`, the precise local content needed from `Δθ ≪ θ`.
-/
theorem deltaThetaEventuallySmallerThanTheta (θ : ℝ) (hθ : θ ≠ 0) :
    ∀ᶠ Δθ in 𝓝 (0 : ℝ), |Δθ| < |θ| := by
  rw [Metric.eventually_nhds_iff]
  exact
    ⟨|θ|, abs_pos.mpr hθ,
      by
        intro Δθ hΔθ
        simpa [Real.dist_eq] using hΔθ⟩

/--
IPhO 2026 problem 2, part C.4.

The C.3 caustic has offset `u = R/2`, coefficient
`v = (3/4) R^(1/3)`, and reduced exponent `p/q = 2/3`.
-/
theorem smallAngleCausticPowerLaw (model : Figure2gCausticModel) :
    HasSmallAnglePowerLaw model
      { uReadout := model.frame.radiusReadout / 2
        vScaleReadout :=
          ((3 : ℝ) / 4) *
            Real.rpow model.frame.radiusReadout ((1 : ℝ) / 3)
        exponentNumerator := 2
        exponentDenominator := 3 } := by
  unfold HasSmallAnglePowerLaw
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num only [Nat.cast_ofNat]
  have harg : Tendsto (fun θ : ℝ => θ / 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun θ : ℝ => θ / 2) 0 :=
      continuousAt_id.div_const 2
    simpa only [zero_div] using
      hc.tendsto.mono_left
        (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hhalf : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ => Real.sin (θ / 2)) (fun θ => θ / 2) := by
    change Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (Real.sin ∘ fun θ : ℝ => θ / 2)
      (id ∘ fun θ : ℝ => θ / 2)
    exact Real.isEquivalent_sin.comp_tendsto harg
  have hhalfSq : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ => Real.sin (θ / 2) ^ 2) (fun θ => (θ / 2) ^ 2) := by
    change Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      ((Real.sin ∘ fun θ : ℝ => θ / 2) ^ 2)
      ((id ∘ fun θ : ℝ => θ / 2) ^ 2)
    exact hhalf.pow 2
  have hpoly : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ : ℝ => 2 * (Real.cos θ) ^ 2 + 2 * Real.cos θ - 1)
      (fun _ : ℝ => 3) := by
    have hc : ContinuousAt
        (fun θ : ℝ => 2 * (Real.cos θ) ^ 2 + 2 * Real.cos θ - 1) 0 := by
      fun_prop
    have ht : Tendsto
        (fun θ : ℝ => 2 * (Real.cos θ) ^ 2 + 2 * Real.cos θ - 1)
        (𝓝[≠] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
      convert hc.tendsto.mono_left
        (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left) using 1
      all_goals norm_num
    exact
      (Asymptotics.isEquivalent_const_iff_tendsto
        (by norm_num : (3 : ℝ) ≠ 0)).2 ht
  have hYexplicit : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ =>
        model.frame.radiusReadout / 2 * Real.cos θ *
            (2 - Real.cos (2 * θ)) -
          model.frame.radiusReadout / 2)
      (fun θ =>
        ((3 : ℝ) / 4) * model.frame.radiusReadout * θ ^ 2) := by
    have hprod :=
      (Asymptotics.IsEquivalent.refl
        (u := fun _ : ℝ => model.frame.radiusReadout)).mul
          (hhalfSq.mul hpoly)
    refine hprod.congr_left ?_ |>.congr_right ?_
    · filter_upwards [] with θ
      have hcos2 :
          Real.cos (2 * θ) = 2 * (Real.cos θ) ^ 2 - 1 :=
        Real.cos_two_mul θ
      have hcosHalf :
          Real.cos θ = 1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
        convert Real.cos_two_mul_eq_one_sub (θ / 2) using 1
        all_goals ring_nf
      simp only [Pi.mul_apply]
      rw [hcos2, hcosHalf]
      ring
    · filter_upwards [] with θ
      simp only [Pi.mul_apply]
      ring
  have hYcoordinates :
      (fun θ =>
        model.frame.radiusReadout / 2 * Real.cos θ *
            (2 - Real.cos (2 * θ)) -
          model.frame.radiusReadout / 2) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun θ =>
          model.causticYReadout θ - model.frame.radiusReadout / 2) := by
    filter_upwards [] with θ
    rw [model.previousPartC3.2 θ]
  have hY := hYexplicit.congr_left hYcoordinates
  have hsinSq : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ => (Real.sin θ) ^ 2) (fun θ => θ ^ 2) := by
    change Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (Real.sin ^ 2) (id ^ 2)
    exact (Real.isEquivalent_sin.mono inf_le_left).pow 2
  have hscaledSin : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ =>
        ((3 : ℝ) / 4) * model.frame.radiusReadout * (Real.sin θ) ^ 2)
      (fun θ =>
        ((3 : ℝ) / 4) * model.frame.radiusReadout * θ ^ 2) := by
    exact
      (Asymptotics.IsEquivalent.refl
        (u := fun _ : ℝ =>
          ((3 : ℝ) / 4) * model.frame.radiusReadout)).mul hsinSq
  have hpowerCoordinates :
      (fun θ =>
        ((3 : ℝ) / 4) *
            Real.rpow model.frame.radiusReadout ((1 : ℝ) / 3) *
          Real.rpow |model.causticXReadout θ| ((2 : ℝ) / 3)) =ᶠ[
          𝓝[≠] (0 : ℝ)]
        (fun θ =>
          ((3 : ℝ) / 4) * model.frame.radiusReadout *
            (Real.sin θ) ^ 2) := by
    filter_upwards [] with θ
    rw [model.previousPartC3.1 θ]
    rw [abs_mul, abs_of_pos model.frame.radiusReadout_pos, abs_pow]
    have hm :
        Real.rpow
            (model.frame.radiusReadout * |Real.sin θ| ^ 3)
            ((2 : ℝ) / 3) =
          Real.rpow model.frame.radiusReadout ((2 : ℝ) / 3) *
            Real.rpow (|Real.sin θ| ^ 3) ((2 : ℝ) / 3) := by
      change
        (model.frame.radiusReadout * |Real.sin θ| ^ 3) ^
            ((2 : ℝ) / 3) =
          model.frame.radiusReadout ^ ((2 : ℝ) / 3) *
            (|Real.sin θ| ^ 3) ^ ((2 : ℝ) / 3)
      exact
        Real.mul_rpow model.frame.radiusReadout_pos.le
          (pow_nonneg (abs_nonneg (Real.sin θ)) 3)
    have hRprod :
        Real.rpow model.frame.radiusReadout ((1 : ℝ) / 3) *
            Real.rpow model.frame.radiusReadout ((2 : ℝ) / 3) =
          model.frame.radiusReadout := by
      change
        model.frame.radiusReadout ^ ((1 : ℝ) / 3) *
            model.frame.radiusReadout ^ ((2 : ℝ) / 3) =
          model.frame.radiusReadout
      rw [← Real.rpow_add model.frame.radiusReadout_pos]
      norm_num
    have hs : 0 ≤ |Real.sin θ| := abs_nonneg _
    have hsprod :
        Real.rpow (|Real.sin θ| ^ 3) ((2 : ℝ) / 3) =
          (Real.sin θ) ^ 2 := by
      change
        (|Real.sin θ| ^ 3) ^ ((2 : ℝ) / 3) =
          (Real.sin θ) ^ 2
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hs]
      norm_num
    rw [hm, hsprod]
    nlinarith [hRprod]
  exact hY.trans (hscaledSin.congr_left hpowerCoordinates.symm).symm

end
end IPhO2026_2_C_4
end IPhO2026Problems
