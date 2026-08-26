import ArchonPhysics.ENNRealWindowConvergence

/-!
# Hitting-time transfer through an almost-everywhere measurable version

The deterministic stability theorem applies to the raw closed hitting
functional.  For random spectral models that functional may only have an
explicit measurable version agreeing almost everywhere.  Probability-window
measures are unchanged by this replacement, so no measurability or dense-entry
condition is needed for the raw functional itself.
-/

namespace ArchonPhysics

open Filter MeasureTheory Set Topology
open ENNRealWindowConvergence
open ProbabilisticHittingTransfer
open ThermalizationTransfer

noncomputable section

/-- Local-uniform approximation transfers to any measurable sequence that is
almost everywhere the raw closed hitting time of the approximation path. -/
theorem random_local_uniform_error_implies_ae_identified_hitting_time_convergence
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {limit : Real → Real} (approximation : Nat → Omega → Real → Real)
    (localUniformError : Real → Nat → Omega → ENNReal)
    (X : Nat → Omega → ENNReal)
    (delta tauStar : Real)
    (hcross : RobustKineticFirstCrossing limit delta tauStar)
    (herror : ∀ T, 0 < T →
      ConvergesInProbabilityTo P (localUniformError T) 0)
    (hcontrols : ∀ T eta, 0 < T → 0 < eta →
      ∀ n omega,
        localUniformError T n omega < ENNReal.ofReal eta →
          UniformlyCloseOnNonnegativeWindow
            (approximation n omega) limit T eta)
    (hXmeasurable : ∀ n, Measurable (X n))
    (hXeq : ∀ n, X n =ᵐ[P]
      fun omega => distanceThresholdHittingTime
        (approximation n omega) delta) :
    ConvergesInProbabilityTo P X (ENNReal.ofReal tauStar) := by
  apply convergesInProbabilityTo_of_tendsto_real_windows
    P X tauStar hcross.tauStar_pos hXmeasurable
  intro epsilon hepsilon_pos hepsilon_lt
  have heq :
      (fun n => P (X n ⁻¹'
        Icc (ENNReal.ofReal (tauStar - epsilon))
          (ENNReal.ofReal (tauStar + epsilon)))) =
      (fun n => P (hittingTimeWindowEvent approximation
        delta tauStar epsilon n)) := by
    funext n
    exact measure_congr ((hXeq n).preimage
      (Icc (ENNReal.ofReal (tauStar - epsilon))
        (ENNReal.ofReal (tauStar + epsilon))))
  rw [heq]
  exact random_local_uniform_error_implies_hitting_window
    P approximation localUniformError delta tauStar hcross herror hcontrols
    epsilon hepsilon_pos hepsilon_lt

end

end ArchonPhysics
