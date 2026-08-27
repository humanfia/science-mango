import ArchonPhysics.ResonantThreeWaveKineticEquilibrium
import ArchonPhysics.ResonantThreeWaveKineticL1Stability
import ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity

/-!
# Continuity of canonical L-infinity logarithmic entropy production

The positive-floor representative turns the inverse-action singularity into
a uniformly Lipschitz scalar operation.  On every bounded `L-infinity` ball,
the quadratic three-wave flux and the inverse-action mismatch therefore give
an explicit Lipschitz bound for the genuine collision-measure integral.

In particular, for every strictly positive repair floor the canonical
logarithmic entropy production is locally Lipschitz, hence continuous, on the
whole canonical `L-infinity` phase space.  No continuity assumption on the
production functional is used.
-/

namespace ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity

open Filter MeasureTheory Metric Set
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticL1Stability
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThreeWaveCollisionAlgebra
open scoped ENNReal MeasureTheory NNReal

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Inversion is Lipschitz away from zero, with the sharp elementary
`floor⁻²` coefficient. -/
theorem norm_inv_sub_inv_le_of_floor
    {floor x y : Real} (hfloor : 0 < floor)
    (hx : floor ≤ x) (hy : floor ≤ y) :
    ‖x⁻¹ - y⁻¹‖ ≤ floor⁻¹ ^ 2 * ‖x - y‖ := by
  have hxpos : 0 < x := hfloor.trans_le hx
  have hypos : 0 < y := hfloor.trans_le hy
  have hxinv : ‖x⁻¹‖ ≤ floor⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    exact (inv_le_inv₀ hxpos hfloor).2 hx
  have hyinv : ‖y⁻¹‖ ≤ floor⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hypos)]
    exact (inv_le_inv₀ hypos hfloor).2 hy
  rw [inv_sub_inv' hxpos.ne' hypos.ne', norm_mul, norm_mul]
  calc
    ‖x⁻¹‖ * ‖y - x‖ * ‖y⁻¹‖ ≤
        floor⁻¹ * ‖y - x‖ * floor⁻¹ := by
      gcongr
    _ = floor⁻¹ ^ 2 * ‖x - y‖ := by
      rw [norm_sub_rev]
      ring

/-- A positive-floor inverse-action mismatch is uniformly bounded. -/
theorem norm_inverseActionMismatch_le_of_floor
    {floor x₀ x₁ x₂ : Real} (hfloor : 0 < floor)
    (hx₀ : floor ≤ x₀) (hx₁ : floor ≤ x₁) (hx₂ : floor ≤ x₂) :
    ‖inverseActionMismatch x₀ x₁ x₂‖ ≤ 3 * floor⁻¹ := by
  have hinv (x : Real) (hx : floor ≤ x) : ‖x⁻¹‖ ≤ floor⁻¹ := by
    have hxpos : 0 < x := hfloor.trans_le hx
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    exact (inv_le_inv₀ hxpos hfloor).2 hx
  unfold inverseActionMismatch
  calc
    ‖x₀⁻¹ - x₁⁻¹ - x₂⁻¹‖ ≤
        ‖x₀⁻¹ - x₁⁻¹‖ + ‖x₂⁻¹‖ := norm_sub_le _ _
    _ ≤ ‖x₀⁻¹‖ + ‖x₁⁻¹‖ + ‖x₂⁻¹‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ floor⁻¹ + floor⁻¹ + floor⁻¹ := by
      gcongr
      · exact hinv x₀ hx₀
      · exact hinv x₁ hx₁
      · exact hinv x₂ hx₂
    _ = 3 * floor⁻¹ := by ring

/-- Three coordinatewise perturbations control the inverse-action mismatch
perturbation on a common positive box. -/
theorem norm_inverseActionMismatch_sub_le_of_floor
    {floor epsilon x₀ x₁ x₂ y₀ y₁ y₂ : Real}
    (hfloor : 0 < floor)
    (hx₀ : floor ≤ x₀) (hx₁ : floor ≤ x₁) (hx₂ : floor ≤ x₂)
    (hy₀ : floor ≤ y₀) (hy₁ : floor ≤ y₁) (hy₂ : floor ≤ y₂)
    (h₀ : ‖x₀ - y₀‖ ≤ epsilon)
    (h₁ : ‖x₁ - y₁‖ ≤ epsilon)
    (h₂ : ‖x₂ - y₂‖ ≤ epsilon) :
    ‖inverseActionMismatch x₀ x₁ x₂ -
        inverseActionMismatch y₀ y₁ y₂‖ ≤
      3 * floor⁻¹ ^ 2 * epsilon := by
  have hq : 0 ≤ floor⁻¹ ^ 2 := sq_nonneg _
  have hi₀ : ‖x₀⁻¹ - y₀⁻¹‖ ≤ floor⁻¹ ^ 2 * epsilon :=
    (norm_inv_sub_inv_le_of_floor hfloor hx₀ hy₀).trans
      (mul_le_mul_of_nonneg_left h₀ hq)
  have hi₁ : ‖x₁⁻¹ - y₁⁻¹‖ ≤ floor⁻¹ ^ 2 * epsilon :=
    (norm_inv_sub_inv_le_of_floor hfloor hx₁ hy₁).trans
      (mul_le_mul_of_nonneg_left h₁ hq)
  have hi₂ : ‖x₂⁻¹ - y₂⁻¹‖ ≤ floor⁻¹ ^ 2 * epsilon :=
    (norm_inv_sub_inv_le_of_floor hfloor hx₂ hy₂).trans
      (mul_le_mul_of_nonneg_left h₂ hq)
  unfold inverseActionMismatch
  calc
    ‖(x₀⁻¹ - x₁⁻¹ - x₂⁻¹) - (y₀⁻¹ - y₁⁻¹ - y₂⁻¹)‖ =
        ‖(x₀⁻¹ - y₀⁻¹) - (x₁⁻¹ - y₁⁻¹) -
          (x₂⁻¹ - y₂⁻¹)‖ := by ring_nf
    _ ≤ ‖x₀⁻¹ - y₀⁻¹‖ + ‖x₁⁻¹ - y₁⁻¹‖ +
        ‖x₂⁻¹ - y₂⁻¹‖ := by
      calc
        _ ≤ ‖(x₀⁻¹ - y₀⁻¹) - (x₁⁻¹ - y₁⁻¹)‖ +
            ‖x₂⁻¹ - y₂⁻¹‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ floor⁻¹ ^ 2 * epsilon + floor⁻¹ ^ 2 * epsilon +
        floor⁻¹ ^ 2 * epsilon := by gcongr
    _ = 3 * floor⁻¹ ^ 2 * epsilon := by ring

omit [MeasurableSpace Mode] in
/-- Pointwise Lipschitz bound for the exact three-wave entropy integrand on
a positive bounded box. -/
theorem norm_continuumLogEntropyIntegrand_sub_le
    {action₁ action₂ : Mode → Real} {floor radius epsilon : Real}
    (hfloor : 0 < floor) (hradius : 0 ≤ radius)
    (haction₁ : ∀ mode, ‖action₁ mode‖ ≤ radius)
    (haction₂ : ∀ mode, ‖action₂ mode‖ ≤ radius)
    (haction₁Floor : ∀ mode, floor ≤ action₁ mode)
    (haction₂Floor : ∀ mode, floor ≤ action₂ mode)
    {triad : Fin 3 → Mode}
    (hdistance : ∀ leg : Fin 3,
      ‖action₁ (triad leg) - action₂ (triad leg)‖ ≤ epsilon) :
    ‖continuumLogEntropyIntegrand action₁ triad -
        continuumLogEntropyIntegrand action₂ triad‖ ≤
      (18 * radius * floor⁻¹ + 9 * radius ^ 2 * floor⁻¹ ^ 2) * epsilon := by
  have hepsilon : 0 ≤ epsilon :=
    (norm_nonneg (action₁ (triad 0) - action₂ (triad 0))).trans
      (hdistance 0)
  have hfluxDifference :
      ‖triadFlux action₁ triad - triadFlux action₂ triad‖ ≤
        6 * radius * epsilon := by
    calc
      _ ≤ 2 * radius *
          (‖action₁ (triad 0) - action₂ (triad 0)‖ +
            ‖action₁ (triad 1) - action₂ (triad 1)‖ +
            ‖action₁ (triad 2) - action₂ (triad 2)‖) :=
        norm_triadFlux_sub_le_sum hradius haction₁ haction₂ triad
      _ ≤ 2 * radius * (epsilon + epsilon + epsilon) := by
        gcongr <;> apply hdistance
      _ = 6 * radius * epsilon := by ring
  have hmismatch₁ :
      ‖inverseActionMismatch
          (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2))‖ ≤
        3 * floor⁻¹ :=
    norm_inverseActionMismatch_le_of_floor hfloor
      (haction₁Floor (triad 0)) (haction₁Floor (triad 1))
      (haction₁Floor (triad 2))
  have hflux₂ : ‖triadFlux action₂ triad‖ ≤ 3 * radius ^ 2 :=
    norm_triadFlux_le haction₂ triad
  have hmismatchDifference :
      ‖inverseActionMismatch
          (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2)) -
        inverseActionMismatch
          (action₂ (triad 0)) (action₂ (triad 1)) (action₂ (triad 2))‖ ≤
        3 * floor⁻¹ ^ 2 * epsilon :=
    norm_inverseActionMismatch_sub_le_of_floor hfloor
      (haction₁Floor (triad 0)) (haction₁Floor (triad 1))
      (haction₁Floor (triad 2)) (haction₂Floor (triad 0))
      (haction₂Floor (triad 1)) (haction₂Floor (triad 2))
      (hdistance 0) (hdistance 1) (hdistance 2)
  change ‖triadFlux action₁ triad *
      inverseActionMismatch
        (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2)) -
    triadFlux action₂ triad *
      inverseActionMismatch
        (action₂ (triad 0)) (action₂ (triad 1)) (action₂ (triad 2))‖ ≤ _
  calc
    _ = ‖(triadFlux action₁ triad - triadFlux action₂ triad) *
          inverseActionMismatch
            (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2)) +
        triadFlux action₂ triad *
          (inverseActionMismatch
              (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2)) -
            inverseActionMismatch
              (action₂ (triad 0)) (action₂ (triad 1))
                (action₂ (triad 2)))‖ := by ring_nf
    _ ≤ ‖(triadFlux action₁ triad - triadFlux action₂ triad) *
          inverseActionMismatch
            (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2))‖ +
        ‖triadFlux action₂ triad *
          (inverseActionMismatch
              (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2)) -
            inverseActionMismatch
              (action₂ (triad 0)) (action₂ (triad 1))
                (action₂ (triad 2)))‖ := norm_add_le _ _
    _ = ‖triadFlux action₁ triad - triadFlux action₂ triad‖ *
          ‖inverseActionMismatch
            (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2))‖ +
        ‖triadFlux action₂ triad‖ *
          ‖inverseActionMismatch
              (action₁ (triad 0)) (action₁ (triad 1)) (action₁ (triad 2)) -
            inverseActionMismatch
              (action₂ (triad 0)) (action₂ (triad 1))
                (action₂ (triad 2))‖ := by rw [norm_mul, norm_mul]
    _ ≤ (6 * radius * epsilon) * (3 * floor⁻¹) +
        (3 * radius ^ 2) * (3 * floor⁻¹ ^ 2 * epsilon) := by
      gcongr
    _ = (18 * radius * floor⁻¹ +
        9 * radius ^ 2 * floor⁻¹ ^ 2) * epsilon := by ring

/-- Taking the maximum with a common floor does not increase the canonical
essential-supremum distance. -/
theorem positiveFloorRepresentative_sub_norm_le_ae
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action₁ action₂ : CanonicalLInfinity collision) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖positiveFloorRepresentative collision floor action₁ mode -
          positiveFloorRepresentative collision floor action₂ mode‖ ≤
        ‖action₁ - action₂‖ := by
  filter_upwards
    [linfinityRepresentative_sub_norm_le_ae collision action₁ action₂]
      with mode hmode
  unfold positiveFloorRepresentative
  rw [Real.norm_eq_abs]
  calc
    |max floor (linfinityRepresentative collision action₁ mode) -
        max floor (linfinityRepresentative collision action₂ mode)| =
        |max (linfinityRepresentative collision action₁ mode) floor -
          max (linfinityRepresentative collision action₂ mode) floor| := by
      rw [max_comm floor, max_comm floor]
    _ ≤ |linfinityRepresentative collision action₁ mode -
        linfinityRepresentative collision action₂ mode| :=
      abs_max_sub_max_le_abs _ _ _
    _ = ‖linfinityRepresentative collision action₁ mode -
        linfinityRepresentative collision action₂ mode‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ‖action₁ - action₂‖ := hmode

/-- The reference-measure essential bound transports simultaneously to all
three collision legs. -/
theorem positiveFloorRepresentative_sub_norm_le_ae_collisionMeasure
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action₁ action₂ : CanonicalLInfinity collision) :
    ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
      ∀ leg : Fin 3,
        ‖positiveFloorRepresentative collision floor action₁ (triad leg) -
            positiveFloorRepresentative collision floor action₂ (triad leg)‖ ≤
          ‖action₁ - action₂‖ := by
  let predicate : Mode → Prop := fun mode ↦
    ‖positiveFloorRepresentative collision floor action₁ mode -
        positiveFloorRepresentative collision floor action₂ mode‖ ≤
      ‖action₁ - action₂‖
  have href : ∀ᵐ mode ∂collisionReferenceMeasure collision, predicate mode :=
    positiveFloorRepresentative_sub_norm_le_ae
      collision floor action₁ action₂
  have hleg (leg : Fin 3) : ∀ᵐ mode ∂legMarginal collision leg, predicate mode :=
    (ae_mono (legMarginal_le_collisionReferenceMeasure collision leg)) href
  have htriad (leg : Fin 3) :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
        predicate (triad leg) := by
    have hleg' := hleg leg
    unfold legMarginal at hleg'
    exact ae_of_ae_map (measurable_triadLeg leg).aemeasurable hleg'
  filter_upwards [htriad 0, htriad 1, htriad 2]
    with triad h₀ h₁ h₂
  intro leg
  fin_cases leg
  · exact h₀
  · exact h₁
  · exact h₂

/-- The explicit real coefficient in the bounded-ball entropy-production
estimate, including the finite collision mass. -/
def canonicalLogEntropyProductionLipschitzCoefficient
    (collision : ResonantThreeWaveMeasure Mode) (floor radius : Real) : Real :=
  (18 * max floor radius * floor⁻¹ +
      9 * (max floor radius) ^ 2 * floor⁻¹ ^ 2) *
    (collision.collisionMeasure : Measure (Fin 3 → Mode)).real univ

/-- Bundled nonnegative Lipschitz coefficient. -/
def canonicalLogEntropyProductionLipschitzConstant
    (collision : ResonantThreeWaveMeasure Mode) (floor radius : Real) : NNReal :=
  Real.toNNReal
    (canonicalLogEntropyProductionLipschitzCoefficient collision floor radius)

theorem canonicalLogEntropyProductionLipschitzCoefficient_nonneg
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor) (radius : Real) :
    0 ≤ canonicalLogEntropyProductionLipschitzCoefficient
      collision floor radius := by
  unfold canonicalLogEntropyProductionLipschitzCoefficient
  positivity

/-- Quantitative quotient-level estimate on a common `L-infinity` ball. -/
theorem norm_canonicalLogEntropyProduction_sub_le
    (collision : ResonantThreeWaveMeasure Mode)
    {floor radius : Real} (hfloor : 0 < floor) (hradius : 0 ≤ radius)
    (action₁ action₂ : CanonicalLInfinity collision)
    (haction₁ : ‖action₁‖ ≤ radius) (haction₂ : ‖action₂‖ ≤ radius) :
    ‖canonicalLogEntropyProduction collision floor action₁ -
        canonicalLogEntropyProduction collision floor action₂‖ ≤
      canonicalLogEntropyProductionLipschitzCoefficient collision floor radius *
        ‖action₁ - action₂‖ := by
  let representative₁ := positiveFloorRepresentative collision floor action₁
  let representative₂ := positiveFloorRepresentative collision floor action₂
  let commonRadius := max floor radius
  have hcommonRadius : 0 ≤ commonRadius := by
    exact hradius.trans (le_max_right _ _)
  have hrepresentative₁Bound : ∀ mode, ‖representative₁ mode‖ ≤ commonRadius :=
    fun mode ↦
      (norm_positiveFloorRepresentative_le collision hfloor.le action₁ mode).trans
        (max_le_max_left floor haction₁)
  have hrepresentative₂Bound : ∀ mode, ‖representative₂ mode‖ ≤ commonRadius :=
    fun mode ↦
      (norm_positiveFloorRepresentative_le collision hfloor.le action₂ mode).trans
        (max_le_max_left floor haction₂)
  have hrepresentative₁Floor : ∀ mode, floor ≤ representative₁ mode :=
    floor_le_positiveFloorRepresentative collision floor action₁
  have hrepresentative₂Floor : ∀ mode, floor ≤ representative₂ mode :=
    floor_le_positiveFloorRepresentative collision floor action₂
  have hbounded₁ : IsBoundedMeasurable representative₁ :=
    positiveFloorRepresentative_isBoundedMeasurable collision hfloor.le action₁
  have hbounded₂ : IsBoundedMeasurable representative₂ :=
    positiveFloorRepresentative_isBoundedMeasurable collision hfloor.le action₂
  have hintegrable₁ : Integrable (continuumLogEntropyIntegrand representative₁)
      collision.collisionMeasure :=
    integrable_continuumLogEntropyIntegrand collision hbounded₁ floor hfloor
      hrepresentative₁Floor
  have hintegrable₂ : Integrable (continuumLogEntropyIntegrand representative₂)
      collision.collisionMeasure :=
    integrable_continuumLogEntropyIntegrand collision hbounded₂ floor hfloor
      hrepresentative₂Floor
  have hdistance :=
    positiveFloorRepresentative_sub_norm_le_ae_collisionMeasure
      collision floor action₁ action₂
  have hpointwise :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
        ‖continuumLogEntropyIntegrand representative₁ triad -
            continuumLogEntropyIntegrand representative₂ triad‖ ≤
          (18 * commonRadius * floor⁻¹ +
              9 * commonRadius ^ 2 * floor⁻¹ ^ 2) *
            ‖action₁ - action₂‖ := by
    filter_upwards [hdistance] with triad htriad
    exact norm_continuumLogEntropyIntegrand_sub_le hfloor hcommonRadius
      hrepresentative₁Bound hrepresentative₂Bound
      hrepresentative₁Floor hrepresentative₂Floor htriad
  change ‖continuumLogEntropyProduction collision representative₁ -
      continuumLogEntropyProduction collision representative₂‖ ≤ _
  rw [continuumLogEntropyProduction_eq_integral,
    continuumLogEntropyProduction_eq_integral,
    ← integral_sub hintegrable₁ hintegrable₂]
  calc
    _ ≤ ((18 * commonRadius * floor⁻¹ +
          9 * commonRadius ^ 2 * floor⁻¹ ^ 2) *
        ‖action₁ - action₂‖) *
      (collision.collisionMeasure : Measure (Fin 3 → Mode)).real univ :=
      norm_integral_le_of_norm_le_const hpointwise
    _ = canonicalLogEntropyProductionLipschitzCoefficient
        collision floor radius * ‖action₁ - action₂‖ := by
      unfold canonicalLogEntropyProductionLipschitzCoefficient
      dsimp [commonRadius]
      ring

/-- On each origin-centered bounded ball, the genuine canonical entropy
production is Lipschitz with an explicit collision-mass-dependent constant. -/
theorem lipschitzOnWith_canonicalLogEntropyProduction_closedBall_zero
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (radius : Real) (hradius : 0 ≤ radius) :
    LipschitzOnWith
      (canonicalLogEntropyProductionLipschitzConstant collision floor radius)
      (canonicalLogEntropyProduction collision floor)
      (closedBall (0 : CanonicalLInfinity collision) radius) := by
  refine LipschitzOnWith.of_dist_le_mul
    fun action₁ haction₁ action₂ haction₂ ↦ ?_
  have hnorm₁ : ‖action₁‖ ≤ radius := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using haction₁
  have hnorm₂ : ‖action₂‖ ≤ radius := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using haction₂
  have hbound := norm_canonicalLogEntropyProduction_sub_le collision
    hfloor hradius action₁ action₂ hnorm₁ hnorm₂
  simpa only [dist_eq_norm, canonicalLogEntropyProductionLipschitzConstant,
    Real.coe_toNNReal _
      (canonicalLogEntropyProductionLipschitzCoefficient_nonneg
        collision hfloor radius)] using hbound

/-- A strictly positive repair floor makes canonical entropy production
locally Lipschitz on the whole canonical `L-infinity` phase space. -/
theorem locallyLipschitz_canonicalLogEntropyProduction
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor) :
    LocallyLipschitz (canonicalLogEntropyProduction collision floor) := by
  intro action
  let radius : Real := ‖action‖ + 1
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    positivity
  have hmem : action ∈ ball (0 : CanonicalLInfinity collision) radius := by
    rw [mem_ball, dist_zero_right]
    dsimp [radius]
    linarith
  refine ⟨canonicalLogEntropyProductionLipschitzConstant
      collision floor radius,
    ball (0 : CanonicalLInfinity collision) radius,
    isOpen_ball.mem_nhds hmem, ?_⟩
  exact (lipschitzOnWith_canonicalLogEntropyProduction_closedBall_zero
    collision hfloor radius hradius).mono ball_subset_closedBall

/-- The continuity assumption formerly required by compact entropy
relaxation is automatic for every positive repair floor. -/
theorem continuous_canonicalLogEntropyProduction
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor) :
    Continuous (canonicalLogEntropyProduction collision floor) :=
  (locallyLipschitz_canonicalLogEntropyProduction collision hfloor).continuous

/-- Direct `ContinuousOn` adapter for an arbitrary state set.  This is the
drop-in replacement for `hproductionContinuous` in compact relaxation. -/
theorem continuousOn_canonicalLogEntropyProduction
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (states : Set (CanonicalLInfinity collision)) :
    ContinuousOn (canonicalLogEntropyProduction collision floor) states :=
  (continuous_canonicalLogEntropyProduction collision hfloor).continuousOn

end

end ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity
