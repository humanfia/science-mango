import ArchonPhysics.CanonicalCollisionFourierLipschitz
import ArchonPhysics.CanonicalCollisionMeasureWeakLimit
import ArchonPhysics.LipschitzPointwiseCompactUniform

/-!
# Compact-uniform limit of the canonical collision Fourier transform

The almost-sure weak limit of the genuine per-site collision finite measures
gives simultaneous pointwise convergence of all their Fourier characters.
The volume-independent Lipschitz estimate then upgrades that convergence to
uniform convergence on every compact Fourier-time set.
-/

namespace ArchonPhysics.CanonicalCollisionFourierCompactUniformLimit

open scoped BoundedContinuousFunction

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionFourierLipschitz
open ArchonPhysics.CanonicalCollisionFourierPerSiteLimit
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.LipschitzPointwiseCompactUniform
open ArchonPhysics.ModalPhaseMismatch
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The complex Fourier character as a globally bounded continuous function. -/
def collisionFourierCharacter (time : Real) : Real →ᵇ Complex :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : Real => Complex.exp
        (Complex.I * ((time * x : Real) : Complex)), by fun_prop⟩
    2 (by
      intro x y
      rw [dist_eq_norm]
      calc
        ‖Complex.exp (Complex.I * ((time * x : Real) : Complex)) -
            Complex.exp (Complex.I * ((time * y : Real) : Complex))‖ <=
            ‖Complex.exp (Complex.I * ((time * x : Real) : Complex))‖ +
              ‖Complex.exp (Complex.I * ((time * y : Real) : Complex))‖ :=
          norm_sub_le _ _
        _ = 2 := by
          norm_num [Complex.norm_exp, Complex.mul_re])

/-- Fourier transform of the deterministic limiting per-site finite measure. -/
def canonicalCollisionPerSiteMeasureLimitFourier
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) : Complex :=
  ∫ x : Real, collisionFourierCharacter time x
    ∂(canonicalCollisionPerSiteMeasureLimit ensemble sign : Measure Real)

/-- Weak convergence of the finite collision measures gives, on one
probability-one event, pointwise Fourier convergence simultaneously at every
real frequency. -/
theorem canonicalCollisionPerSiteFourierIntegral_tendsto_limit_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability, forall time : Real,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionPerSiteFourierIntegral
            ensemble sign time (n + 1) omega)
        atTop
        (nhds
          (canonicalCollisionPerSiteMeasureLimitFourier
            ensemble sign time)) := by
  filter_upwards
    [canonicalCollisionPerSiteFiniteMeasure_tendsto_limit_ae
      ensemble sign] with omega hmeasure
  intro time
  have htest :=
    (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto Complex).mp
      hmeasure (collisionFourierCharacter time)
  simpa [canonicalCollisionPerSiteMeasureLimitFourier,
    canonicalCollisionPerSiteFourierIntegral, collisionFourierCharacter] using htest

/-- The deterministic finite-measure Fourier transform is exactly the
previously selected deterministic per-site Fourier limit. -/
theorem canonicalCollisionPerSiteMeasureLimitFourier_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    canonicalCollisionPerSiteMeasureLimitFourier ensemble sign time =
      canonicalCollisionFourierLimit ensemble sign time := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionPerSiteFourierIntegral
            ensemble sign time (n + 1) omega)
        atTop
        (nhds
          (canonicalCollisionPerSiteMeasureLimitFourier
            ensemble sign time)) ∧
      Tendsto
        (fun n : Nat =>
          canonicalCollisionFourierPerSite
            ensemble sign time (n + 1) omega)
        atTop
        (nhds (canonicalCollisionFourierLimit ensemble sign time)) := by
    filter_upwards
      [canonicalCollisionPerSiteFourierIntegral_tendsto_limit_ae
        ensemble sign,
      canonicalCollisionFourierPerSite_shift_tendsto_chosenLimit_ae
        ensemble sign time] with omega hintegral hselected
    exact ⟨hintegral time, hselected⟩
  obtain ⟨omega, hintegral, hselected⟩ := hevent.exists
  have hselectedIntegral : Tendsto
      (fun n : Nat =>
        canonicalCollisionPerSiteFourierIntegral
          ensemble sign time (n + 1) omega)
      atTop
      (nhds (canonicalCollisionFourierLimit ensemble sign time)) := by
    apply hselected.congr'
    exact Eventually.of_forall fun n =>
      (canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div
        ensemble sign time (n + 1) omega).symm
  exact tendsto_nhds_unique hintegral hselectedIntegral

/-- On one probability-one event, the exact per-site Fourier sums converge
pointwise at every real frequency to the deterministic selected limit. -/
theorem canonicalCollisionFourierPerSite_tendsto_all_real_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability, forall time : Real,
      Tendsto
        (fun n : Nat =>
          canonicalCollisionFourierPerSite
            ensemble sign time (n + 1) omega)
        atTop
        (nhds (canonicalCollisionFourierLimit ensemble sign time)) := by
  filter_upwards
    [canonicalCollisionPerSiteFourierIntegral_tendsto_limit_ae
      ensemble sign] with omega hintegral
  intro time
  have h := hintegral time
  rw [canonicalCollisionPerSiteMeasureLimitFourier_eq] at h
  apply h.congr'
  exact Eventually.of_forall fun n =>
    canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div
      ensemble sign time (n + 1) omega

/-- The genuine finite-volume collision Fourier transforms converge almost
surely, uniformly on every compact Fourier-time set. -/
theorem canonicalCollisionFourierPerSite_tendstoUniformlyOn_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) {S : Set Real}
    (hS : IsCompact S) :
    ∀ᵐ omega ∂ensemble.probability,
      TendstoUniformlyOn
        (fun n time =>
          canonicalCollisionFourierPerSite
            ensemble sign time (n + 1) omega)
        (canonicalCollisionFourierLimit ensemble sign)
        atTop S := by
  filter_upwards
    [canonicalCollisionFourierPerSite_lipschitzWith_ae ensemble sign,
      canonicalCollisionFourierPerSite_tendsto_all_real_ae
        ensemble sign] with omega hlipschitz hpointwise
  apply tendstoUniformlyOn_of_lipschitzWith_of_pointwise
    (K := canonicalCollisionFourierLipschitzConstant)
  · intro n
    exact hlipschitz (n + 1)
  · exact hpointwise
  · exact hS

end

end ArchonPhysics.CanonicalCollisionFourierCompactUniformLimit
