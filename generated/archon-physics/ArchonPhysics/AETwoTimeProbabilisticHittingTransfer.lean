import ArchonPhysics.AEIdentifiedHittingTimeTransfer
import ArchonPhysics.TwoTimeProbabilisticHittingTransfer

/-!
# Two-time hitting transfer through an almost-everywhere identification

The canonical random-spectrum hitting time is represented by an everywhere
measurable random variable which agrees almost everywhere with the raw closed
hitting functional.  Probability windows are invariant under this replacement.
This module combines that observation with the robust two-time transfer, so no
unique kinetic crossing or strict monotonicity is required.
-/

namespace ArchonPhysics.AETwoTimeProbabilisticHittingTransfer

open ArchonPhysics
open ArchonPhysics.ProbabilisticHittingTransfer
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.TwoTimeKineticHittingBounds
open ArchonPhysics.TwoTimeProbabilisticHittingTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-- Local-uniform approximation transfers a robust kinetic window to any
measurable-version random time that agrees almost everywhere with the raw
closed hitting functional. -/
theorem random_local_uniform_error_implies_ae_identified_twoTime_window
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    {limit : Real → Real}
    (approximation : Nat → Omega → Real → Real)
    (localUniformError : Nat → Omega → ENNReal)
    (X : Nat → Omega → ENNReal)
    (delta lower upper : Real)
    (window : RobustKineticHittingWindow limit delta lower upper)
    (herror : ConvergesInProbabilityTo probability localUniformError 0)
    (hcontrols : ∀ eta : Real, 0 < eta → ∀ n omega,
      localUniformError n omega < ENNReal.ofReal eta →
        UniformlyCloseOnNonnegativeWindow
          (approximation n omega) limit upper eta)
    (hXeq : ∀ n, X n =ᵐ[probability]
      fun omega => distanceThresholdHittingTime
        (approximation n omega) delta) :
    Tendsto
      (fun n => probability
        (X n ⁻¹' Icc (Real.toNNReal lower : ENNReal)
          (Real.toNNReal upper : ENNReal)))
      atTop (nhds 1) := by
  have hraw := random_local_uniform_error_implies_twoTime_hitting_window
    probability approximation localUniformError delta lower upper window
    herror hcontrols
  have heq :
      (fun n => probability
        (X n ⁻¹' Icc (Real.toNNReal lower : ENNReal)
          (Real.toNNReal upper : ENNReal))) =
      (fun n => probability
        (twoTimeHittingWindowEvent approximation
          delta lower upper n)) := by
    funext n
    exact measure_congr ((hXeq n).preimage
      (Icc (Real.toNNReal lower : ENNReal)
        (Real.toNNReal upper : ENNReal)))
  rw [heq]
  exact hraw

end

end ArchonPhysics.AETwoTimeProbabilisticHittingTransfer
