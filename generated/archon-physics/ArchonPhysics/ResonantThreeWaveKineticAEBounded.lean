import ArchonPhysics.ResonantThreeWaveKineticL1Stability
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Almost-everywhere L-infinity bounds for the RN collision vector

The canonical reference measure is the sum of all three collision-leg
marginals.  Consequently a triad flux bounded by `K` produces a net signed
collision measure whose variation is bounded by `K` times that reference
measure: the three leg contributions are already accounted for in the
definition of the reference, so there is no additional factor of three.

For an action bounded by `R`, the quadratic flux bound gives `K = 3 * R^2`.
The Radon--Nikodym collision vector therefore has norm at most `3 * R^2`
almost everywhere.  This is explicitly an almost-everywhere conclusion, not
a statement about the totalized RN representative at every point.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticAEBounded

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticL1Stability
open scoped MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A bounded action makes the variation of its signed triad flux measure
dominated by the sharp flux bound times the collision measure. -/
theorem fluxSignedTriadMeasure_variation_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : forall mode, norm (action mode) <= radius) :
    (fluxSignedTriadMeasure collision action).variation <=
      ENNReal.ofReal (3 * radius ^ 2) •
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)) := by
  have hbounded : IsBoundedMeasurable action :=
    ⟨haction_measurable, ⟨radius, haction⟩⟩
  have hflux := integrable_triadFlux collision hbounded
  rw [fluxSignedTriadMeasure, Measure.variation_withDensityᵥ hflux,
    ← withDensity_const]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (fun triad => by
    change ‖triadFlux action triad‖ₑ <= ENNReal.ofReal (3 * radius ^ 2)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_triadFlux_le haction triad))

/-- Pushing the bounded signed flux through one leg gives the same sharp
constant times that leg marginal. -/
theorem legFluxSignedMeasure_variation_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : forall mode, norm (action mode) <= radius)
    (leg : Fin 3) :
    (legFluxSignedMeasure collision action leg).variation <=
      ENNReal.ofReal (3 * radius ^ 2) • legMarginal collision leg := by
  calc
    _ <= (fluxSignedTriadMeasure collision action).variation.map (triadLeg leg) :=
      VectorMeasure.variation_map_le
    _ <= (ENNReal.ofReal (3 * radius ^ 2) •
        (collision.collisionMeasure : Measure (Fin 3 -> Mode))).map (triadLeg leg) :=
      Measure.map_mono
        (fluxSignedTriadMeasure_variation_le collision haction_measurable haction)
        (measurable_triadLeg leg)
    _ = _ := by
      rw [Measure.map_smul]
      rfl

/-- The net signed collision measure has variation at most the sharp flux
constant times the full three-leg reference measure. -/
theorem signedCollisionMeasure_variation_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : forall mode, norm (action mode) <= radius) :
    (signedCollisionMeasure collision action).variation <=
      ENNReal.ofReal (3 * radius ^ 2) • collisionReferenceMeasure collision := by
  let leg₀ := legFluxSignedMeasure collision action 0
  let leg₁ := legFluxSignedMeasure collision action 1
  let leg₂ := legFluxSignedMeasure collision action 2
  let K := ENNReal.ofReal (3 * radius ^ 2)
  have h₀₁ : (leg₀ - leg₁).variation <= leg₀.variation + leg₁.variation :=
    VectorMeasure.variation_sub_le
  have h₀₁₂ : ((leg₀ - leg₁) - leg₂).variation <=
      (leg₀ - leg₁).variation + leg₂.variation :=
    VectorMeasure.variation_sub_le
  have htotal : ((leg₀ - leg₁) - leg₂).variation <=
      (leg₀.variation + leg₁.variation) + leg₂.variation :=
    h₀₁₂.trans (add_le_add h₀₁ le_rfl)
  change ((leg₀ - leg₁) - leg₂).variation <= _
  calc
    _ <= (leg₀.variation + leg₁.variation) + leg₂.variation := htotal
    _ <= (K • legMarginal collision 0 + K • legMarginal collision 1) +
        K • legMarginal collision 2 := by
      apply add_le_add
      · apply add_le_add
        · exact legFluxSignedMeasure_variation_le
            collision haction_measurable haction 0
        · exact legFluxSignedMeasure_variation_le
            collision haction_measurable haction 1
      · exact legFluxSignedMeasure_variation_le
          collision haction_measurable haction 2
    _ = K • collisionReferenceMeasure collision := by
      rw [collisionReferenceMeasure, smul_add, smul_add]

/-- The variation of the RN representation is exactly the reference measure
with density equal to the collision-vector enorm. -/
theorem withDensity_enorm_collisionVector_eq_variation
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real) :
    (collisionReferenceMeasure collision).withDensity
        (fun mode => ‖collisionVector collision action mode‖ₑ) =
      (signedCollisionMeasure collision action).variation := by
  rw [← Measure.variation_withDensityᵥ
    (integrable_collisionVector collision action),
    withDensity_collisionVector_eq_signedCollisionMeasure]

/-- Measure-level domination of the collision-vector norm density. -/
theorem withDensity_enorm_collisionVector_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : forall mode, norm (action mode) <= radius) :
    (collisionReferenceMeasure collision).withDensity
        (fun mode => ‖collisionVector collision action mode‖ₑ) <=
      ENNReal.ofReal (3 * radius ^ 2) • collisionReferenceMeasure collision := by
  rw [withDensity_enorm_collisionVector_eq_variation]
  exact signedCollisionMeasure_variation_le collision haction_measurable haction

/-- ENNReal form of the sharp almost-everywhere collision-vector bound. -/
theorem collisionVector_enorm_le_ae
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : forall mode, norm (action mode) <= radius) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖collisionVector collision action mode‖ₑ <=
        ENNReal.ofReal (3 * radius ^ 2) := by
  have hmeasure := withDensity_enorm_collisionVector_le
    collision haction_measurable haction
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (measurable_collisionVector collision action).enorm
  intro s hs _
  rw [← withDensity_apply _ hs, ← withDensity_apply _ hs,
    withDensity_const]
  exact hmeasure s

/-- Real-norm form: a bounded action produces an RN collision vector bounded
by `3 * radius^2` almost everywhere in the canonical reference measure. -/
theorem collisionVector_norm_le_ae
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : forall mode, norm (action mode) <= radius) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      norm (collisionVector collision action mode) <= 3 * radius ^ 2 := by
  filter_upwards [collisionVector_enorm_le_ae
    collision haction_measurable haction] with mode hmode
  rw [← ofReal_norm] at hmode
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmode

end

end ArchonPhysics.ResonantThreeWaveKineticAEBounded
