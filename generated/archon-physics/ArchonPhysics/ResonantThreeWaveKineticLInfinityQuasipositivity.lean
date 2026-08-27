import ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Quasipositivity of the canonical RN three-wave collision map

For a nonnegative action bounded by `R`, every ordered collision leg has a
gain--loss decomposition whose loss is at most `2 R` times the action on that
leg.  After transporting the three legs and taking the signed
Radon--Nikodym derivative this gives

`Q(n) + 2 R n ≥ 0` almost everywhere.

The final theorem is stated directly on the canonical `L-infinity` quotient.
Exceptional values are repaired by taking the positive part of the canonical
representative; this does not change either the quotient state or its RN
collision vector.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityQuasipositivity

open Filter MeasureTheory Set
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticL1Lipschitz
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThreeWaveCollisionAlgebra
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Integrating a bounded measurable mode function against the sum of the
three leg marginals is the sum of its three pullbacks to triad space. -/
theorem integral_collisionReferenceMeasure_eq_sum_legs
    (collision : ResonantThreeWaveMeasure Mode)
    {f : Mode → Real} (hf : Measurable f) (bound : Real)
    (hbound : ∀ mode, ‖f mode‖ ≤ bound) :
    (∫ mode, f mode ∂collisionReferenceMeasure collision) =
      ∫ (triad : Fin 3 → Mode), f (triad 0) + f (triad 1) + f (triad 2)
        ∂collision.collisionMeasure := by
  have hleg (leg : Fin 3) : Integrable f (legMarginal collision leg) :=
    Integrable.of_bound hf.aestronglyMeasurable bound
      (Filter.Eventually.of_forall hbound)
  have hpull (leg : Fin 3) :
      Integrable (fun triad : Fin 3 → Mode ↦ f (triad leg))
        collision.collisionMeasure :=
    Integrable.of_bound
      (hf.comp (measurable_triadLeg leg)).aestronglyMeasurable bound
      (Filter.Eventually.of_forall fun triad ↦ hbound (triad leg))
  have hmap (leg : Fin 3) :
      (∫ mode, f mode ∂legMarginal collision leg) =
        ∫ (triad : Fin 3 → Mode), f (triad leg) ∂collision.collisionMeasure := by
    unfold legMarginal
    exact integral_map (measurable_triadLeg leg).aemeasurable
      hf.aestronglyMeasurable
  rw [collisionReferenceMeasure,
    integral_add_measure ((hleg 0).add_measure (hleg 1)) (hleg 2),
    integral_add_measure (hleg 0) (hleg 1), hmap 0, hmap 1, hmap 2,
    ← integral_add (hpull 0) (hpull 1)]
  exact (integral_add ((hpull 0).add (hpull 1)) (hpull 2)).symm

/-- Pointwise gain--loss algebra, retained separately from the measure/RN
argument. -/
theorem legwise_quasipositive
    {R n₀ n₁ n₂ test₀ test₁ test₂ : Real}
    (hR : 0 ≤ R)
    (hn₀ : 0 ≤ n₀) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂)
    (_hn₀R : n₀ ≤ R) (hn₁R : n₁ ≤ R) (hn₂R : n₂ ≤ R)
    (htest₀ : 0 ≤ test₀) (htest₁ : 0 ≤ test₁)
    (htest₂ : 0 ≤ test₂) :
    0 ≤ collisionFlux n₀ n₁ n₂ * (test₀ - test₁ - test₂) +
      2 * R * (test₀ * n₀ + test₁ * n₁ + test₂ * n₂) := by
  have hparent : 0 ≤ collisionFlux n₀ n₁ n₂ + 2 * R * n₀ := by
    unfold collisionFlux
    nlinarith [mul_nonneg hn₁ hn₂,
      mul_nonneg hn₀ (sub_nonneg.mpr hn₁R),
      mul_nonneg hn₀ (sub_nonneg.mpr hn₂R)]
  have hchild₁ : 0 ≤ -collisionFlux n₀ n₁ n₂ + 2 * R * n₁ := by
    unfold collisionFlux
    nlinarith [mul_nonneg hn₀ hn₁, mul_nonneg hn₀ hn₂,
      mul_nonneg hn₁ (sub_nonneg.mpr hn₂R)]
  have hchild₂ : 0 ≤ -collisionFlux n₀ n₁ n₂ + 2 * R * n₂ := by
    unfold collisionFlux
    nlinarith [mul_nonneg hn₀ hn₁, mul_nonneg hn₀ hn₂,
      mul_nonneg hn₂ (sub_nonneg.mpr hn₁R)]
  nlinarith [mul_nonneg htest₀ hparent,
    mul_nonneg htest₁ hchild₁, mul_nonneg htest₂ hchild₂]

/-- A globally nonnegative bounded representative has an almost-everywhere
quasipositive RN collision vector. -/
theorem collisionVector_add_two_mul_nonnegative_ae
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode → Real} {radius : Real} (hradius : 0 ≤ radius)
    (hactionMeasurable : Measurable action)
    (hactionNonnegative : ∀ mode, 0 ≤ action mode)
    (hactionBound : ∀ mode, action mode ≤ radius) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      0 ≤ collisionVector collision action mode +
        2 * radius * action mode := by
  have hactionNorm : ∀ mode, ‖action mode‖ ≤ radius := by
    intro mode
    rw [Real.norm_eq_abs, abs_of_nonneg (hactionNonnegative mode)]
    exact hactionBound mode
  have hactionBM : IsBoundedMeasurable action :=
    ⟨hactionMeasurable, ⟨radius, hactionNorm⟩⟩
  have hactionIntegrable : Integrable action
      (collisionReferenceMeasure collision) :=
    Integrable.of_bound hactionMeasurable.aestronglyMeasurable radius
      (Filter.Eventually.of_forall hactionNorm)
  have hcombinedIntegrable : Integrable
      (fun mode ↦ collisionVector collision action mode +
        2 * radius * action mode) (collisionReferenceMeasure collision) :=
    (integrable_collisionVector collision action).add
      (hactionIntegrable.const_mul (2 * radius))
  apply ae_nonneg_of_forall_setIntegral_nonneg hcombinedIntegrable
  intro s hs _hsfinite
  let test : Mode → Real := s.indicator (fun _ ↦ 1)
  have htestMeasurable : Measurable test :=
    Measurable.indicator measurable_const hs
  have htestNonnegative : ∀ mode, 0 ≤ test mode := by
    intro mode
    by_cases hmode : mode ∈ s <;> simp [test, hmode]
  have htestNorm : ∀ mode, ‖test mode‖ ≤ 1 := by
    intro mode
    by_cases hmode : mode ∈ s <;> simp [test, hmode]
  have htestBM : IsBoundedMeasurable test :=
    ⟨htestMeasurable, ⟨1, htestNorm⟩⟩
  have hcollisionSet :
      (∫ mode in s, collisionVector collision action mode
        ∂collisionReferenceMeasure collision) =
        weakCollisionSlope collision test action := by
    rw [← integral_test_mul_collisionVector_eq_weakCollisionSlope
      collision htestBM hactionBM, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards with mode
    by_cases hmode : mode ∈ s <;> simp [test, hmode]
  have hactionSet :
      (∫ mode in s, action mode ∂collisionReferenceMeasure collision) =
        ∫ (triad : Fin 3 → Mode),
          test (triad 0) * action (triad 0) +
          test (triad 1) * action (triad 1) +
          test (triad 2) * action (triad 2)
          ∂collision.collisionMeasure := by
    calc
      (∫ mode in s, action mode ∂collisionReferenceMeasure collision) =
          ∫ mode, test mode * action mode
            ∂collisionReferenceMeasure collision := by
        rw [← integral_indicator hs]
        apply integral_congr_ae
        filter_upwards with mode
        by_cases hmode : mode ∈ s <;> simp [test, hmode]
      _ = ∫ (triad : Fin 3 → Mode),
          test (triad 0) * action (triad 0) +
          test (triad 1) * action (triad 1) +
          test (triad 2) * action (triad 2)
          ∂collision.collisionMeasure := by
        apply integral_collisionReferenceMeasure_eq_sum_legs collision
          (htestMeasurable.mul hactionMeasurable) radius
        intro mode
        rw [Real.norm_eq_abs]
        have htestCases : test mode = 0 ∨ test mode = 1 := by
          by_cases hmode : mode ∈ s
          · exact Or.inr (by simp [test, hmode])
          · exact Or.inl (by simp [test, hmode])
        rcases htestCases with hzero | hone
        · simp [hzero, hradius]
        · simp [hone, abs_of_nonneg (hactionNonnegative mode),
            hactionBound mode]
  have hfluxIntegrable : Integrable
      (fun triad ↦ triadWeakObservableIntegrand test action triad)
      collision.collisionMeasure := by
    exact (integrable_triadFlux collision hactionBM).mul_bdd (c := 3)
      (htestMeasurable.comp (measurable_triadLeg 0) |>.sub
        (htestMeasurable.comp (measurable_triadLeg 1)) |>.sub
        (htestMeasurable.comp (measurable_triadLeg 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun triad ↦ by
        have h₀ := htestNorm (triad 0)
        have h₁ := htestNorm (triad 1)
        have h₂ := htestNorm (triad 2)
        rw [Real.norm_eq_abs] at h₀ h₁ h₂ ⊢
        have h₀₁ := abs_sub (test (triad 0)) (test (triad 1))
        have h₀₁₂ := abs_sub (test (triad 0) - test (triad 1)) (test (triad 2))
        linarith)
  let legSum : (Fin 3 → Mode) → Real := fun triad ↦
    test (triad 0) * action (triad 0) +
      test (triad 1) * action (triad 1) +
      test (triad 2) * action (triad 2)
  have hlegSumIntegrable : Integrable legSum collision.collisionMeasure := by
    apply Integrable.of_bound
      (((htestMeasurable.comp (measurable_triadLeg 0)).mul
          (hactionMeasurable.comp (measurable_triadLeg 0))).add
        ((htestMeasurable.comp (measurable_triadLeg 1)).mul
          (hactionMeasurable.comp (measurable_triadLeg 1))) |>.add
        ((htestMeasurable.comp (measurable_triadLeg 2)).mul
          (hactionMeasurable.comp (measurable_triadLeg 2)))).aestronglyMeasurable
      (3 * radius)
    filter_upwards with triad
    have h₀ := hactionNorm (triad 0)
    have h₁ := hactionNorm (triad 1)
    have h₂ := hactionNorm (triad 2)
    have ht₀ := htestNorm (triad 0)
    have ht₁ := htestNorm (triad 1)
    have ht₂ := htestNorm (triad 2)
    calc
      ‖test (triad 0) * action (triad 0) +
          test (triad 1) * action (triad 1) +
          test (triad 2) * action (triad 2)‖ ≤
          ‖test (triad 0)‖ * ‖action (triad 0)‖ +
          ‖test (triad 1)‖ * ‖action (triad 1)‖ +
          ‖test (triad 2)‖ * ‖action (triad 2)‖ := by
        simpa only [norm_mul] using
          (norm_add_le
            (test (triad 0) * action (triad 0) +
              test (triad 1) * action (triad 1))
            (test (triad 2) * action (triad 2))).trans
            (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 3 * radius := by
        have hp₀ : ‖test (triad 0)‖ * ‖action (triad 0)‖ ≤ radius := by
          calc
            ‖test (triad 0)‖ * ‖action (triad 0)‖ ≤ 1 * radius :=
              mul_le_mul ht₀ h₀ (norm_nonneg _) zero_le_one
            _ = radius := one_mul radius
        have hp₁ : ‖test (triad 1)‖ * ‖action (triad 1)‖ ≤ radius := by
          calc
            ‖test (triad 1)‖ * ‖action (triad 1)‖ ≤ 1 * radius :=
              mul_le_mul ht₁ h₁ (norm_nonneg _) zero_le_one
            _ = radius := one_mul radius
        have hp₂ : ‖test (triad 2)‖ * ‖action (triad 2)‖ ≤ radius := by
          calc
            ‖test (triad 2)‖ * ‖action (triad 2)‖ ≤ 1 * radius :=
              mul_le_mul ht₂ h₂ (norm_nonneg _) zero_le_one
            _ = radius := one_mul radius
        linarith
  rw [integral_add
    (integrable_collisionVector collision action).integrableOn
    (hactionIntegrable.const_mul (2 * radius)).integrableOn]
  rw [integral_const_mul, hcollisionSet, hactionSet]
  unfold weakCollisionSlope
  rw [← integral_const_mul]
  rw [← integral_add hfluxIntegrable (hlegSumIntegrable.const_mul (2 * radius))]
  apply integral_nonneg
  intro triad
  dsimp only [legSum, triadWeakObservableIntegrand]
  exact legwise_quasipositive hradius
    (hactionNonnegative (triad 0))
    (hactionNonnegative (triad 1))
    (hactionNonnegative (triad 2))
    (hactionBound (triad 0))
    (hactionBound (triad 1))
    (hactionBound (triad 2))
    (htestNonnegative (triad 0))
    (htestNonnegative (triad 1))
    (htestNonnegative (triad 2))

/-- A pointwise nonnegative representative of an essentially nonnegative
canonical `L-infinity` class. -/
def nonnegativeRepresentative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) : Mode → Real :=
  fun mode ↦ max (linfinityRepresentative collision action mode) 0

theorem measurable_nonnegativeRepresentative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    Measurable (nonnegativeRepresentative collision action) :=
  (measurable_linfinityRepresentative collision action).max measurable_const

theorem nonnegativeRepresentative_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) (mode : Mode) :
    0 ≤ nonnegativeRepresentative collision action mode :=
  le_max_right _ _

theorem nonnegativeRepresentative_le_norm
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) (mode : Mode) :
    nonnegativeRepresentative collision action mode ≤ ‖action‖ := by
  apply max_le
  · exact le_trans (le_abs_self _) (by
      simpa only [Real.norm_eq_abs] using
        norm_linfinityRepresentative_le collision action mode)
  · exact norm_nonneg action

theorem nonnegativeRepresentative_ae_eq
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision)
    (haction : AENonnegative collision action) :
    nonnegativeRepresentative collision action =ᵐ[
      collisionReferenceMeasure collision] action := by
  filter_upwards [linfinityRepresentative_ae_eq collision action, haction]
    with mode hrep hnonneg
  simp only [nonnegativeRepresentative, hrep, max_eq_left hnonneg]

/-- Quotient-level quasipositivity of the genuine unclipped RN collision map. -/
theorem collisionMap_add_two_mul_nonnegative_ae
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision)
    (haction : AENonnegative collision action) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      0 ≤ collisionMap collision action mode +
        2 * ‖action‖ * action mode := by
  let representative := nonnegativeRepresentative collision action
  have hrepMeasurable : Measurable representative :=
    measurable_nonnegativeRepresentative collision action
  have hrepNonnegative : ∀ mode, 0 ≤ representative mode :=
    nonnegativeRepresentative_nonnegative collision action
  have hrepBound : ∀ mode, representative mode ≤ ‖action‖ :=
    nonnegativeRepresentative_le_norm collision action
  have hrepNorm : ∀ mode, ‖representative mode‖ ≤ ‖action‖ := by
    intro mode
    rw [Real.norm_eq_abs, abs_of_nonneg (hrepNonnegative mode)]
    exact hrepBound mode
  have hrepAE := nonnegativeRepresentative_ae_eq collision action haction
  have hquasi := collisionVector_add_two_mul_nonnegative_ae collision
    (norm_nonneg action) hrepMeasurable hrepNonnegative hrepBound
  filter_upwards [coeFn_collisionMap_ae_eq collision action,
    collisionVector_ae_eq_of_action_ae_eq collision (norm_nonneg action)
      (measurable_linfinityRepresentative collision action) hrepMeasurable
      (norm_linfinityRepresentative_le collision action) hrepNorm
      ((linfinityRepresentative_ae_eq collision action).trans hrepAE.symm),
    hrepAE, hquasi] with mode hcollision hcollisionRep hrep hbound
  rw [hcollision, hcollisionRep]
  change representative mode = action mode at hrep
  rw [← hrep]
  exact hbound

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityQuasipositivity
