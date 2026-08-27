import ArchonPhysics.CanonicalOnShellMarginalDominatedRigidity
import ArchonPhysics.FrequencyMarginalWeakLimitDomination
import ArchonPhysics.FrequencyMismatchKernelMarginalDomination

/-!
# Canonical on-shell frequency marginals from joint raw density

For each marked collision leg, a uniform two-dimensional density bound for
the deterministic raw `(frequency, mismatch)` law gives a time-independent
frequency-density bound after resonance broadening.  Continuous pushforward
and finite-measure portmanteau then pass this bound to every supplied
large-time on-shell cluster.

This is a sufficient backend for marginal balance rigidity.  Its full-raw-law
hypothesis is intentionally not claimed for the canonical model: a repeated
parent--child sector can make one (frequency, mismatch) pair singular.  The
model-facing closure must apply this backend to the all-distinct and
child-repeated sectors and carry the two parent--child sectors as broadened
vanishing errors.  No absolute continuity of the generally singular joint
child-pair law is asserted.
-/

open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalOnShellFrequencyMarginalBridge

open ArchonPhysics
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.FrequencyMarginalWeakLimitDomination
open ArchonPhysics.FrequencyMismatchKernelMarginalDomination
open ArchonPhysics.MeasurableThreeWaveBalanceMarginalRigidity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open Filter MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The scalar harmonic frequency carried by one leg of a marked triad. -/
def markedLegFrequency (leg : Fin 3)
    (triad : Fin 3 → RankFrequencyMark) : Real :=
  (triad leg).2

theorem measurable_markedLegFrequency (leg : Fin 3) :
    Measurable (markedLegFrequency leg) := by
  unfold markedLegFrequency
  fun_prop

theorem continuous_markedLegFrequency (leg : Fin 3) :
    Continuous (markedLegFrequency leg) := by
  unfold markedLegFrequency
  fun_prop

/-- A uniform raw joint density bound passes to the same one-leg frequency
bound on a supplied large-time on-shell weak cluster. -/
theorem canonicalBroadenedWeakLimit_markedLegFrequency_le_volume_of_rawJointDomination
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n ↦
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target))
    (C : ENNReal) (hC : C ≠ ∞)
    (hjoint : ∀ leg : Fin 3,
      Measure.map
          (frequencyMismatchCoordinates (markedLegFrequency leg)
            (markedFrequencyMismatch decayInteractionSign))
          (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
            Measure (Fin 3 → RankFrequencyMark)) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real)))
    (leg : Fin 3) :
    (target.map (markedLegFrequency leg) : Measure Real) ≤
      C • (volume : Measure Real) := by
  apply map_le_smul_volume_of_tendsto_of_uniform_map_le
    (fun n ↦ canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
      ensemble decayInteractionSign (time n) (htime_pos n))
    target hweak (markedLegFrequency leg)
      (continuous_markedLegFrequency leg) C hC
  intro n
  change Measure.map (markedLegFrequency leg)
      (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble decayInteractionSign (time n) (htime_pos n) :
          Measure (Fin 3 → RankFrequencyMark)) ≤
    C • (volume : Measure Real)
  simpa only [canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit] using
    map_frequency_broadenedResonanceMeasure_le_volume_of_joint_le
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
      (measurable_markedFrequencyMismatch decayInteractionSign)
      (htime_pos n) (markedLegFrequency leg)
      (measurable_markedLegFrequency leg) C (hjoint leg)

/-- Hence every leg-frequency marginal of the on-shell collision reference
is absolutely continuous with respect to Lebesgue measure. -/
theorem canonicalBroadenedWeakLimit_frequencyReference_absolutelyContinuous_of_rawJointDomination
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n ↦
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target))
    (C : ENNReal) (hC : C ≠ ∞)
    (hjoint : ∀ leg : Fin 3,
      Measure.map
          (frequencyMismatchCoordinates (markedLegFrequency leg)
            (markedFrequencyMismatch decayInteractionSign))
          (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
            Measure (Fin 3 → RankFrequencyMark)) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    Measure.map collision.frequency (collisionReferenceMeasure collision) ≪
      (volume : Measure Real) := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  change Measure.map collision.frequency
      (collisionReferenceMeasure collision) ≪ (volume : Measure Real)
  apply map_frequency_collisionReference_absolutelyContinuous_of_legs
    collision (volume : Measure Real)
  intro leg
  have htarget :
      (target.map (markedLegFrequency leg) : Measure Real) ≪
        (volume : Measure Real) :=
    (canonicalBroadenedWeakLimit_markedLegFrequency_le_volume_of_rawJointDomination
      ensemble time htime_pos target hweak C hC hjoint leg).absolutelyContinuous.trans
        Measure.smul_absolutelyContinuous
  unfold legMarginal
  rw [Measure.map_map collision.measurable_frequency
    (measurable_triadLeg leg)]
  change Measure.map (markedLegFrequency leg)
      (target : Measure (Fin 3 → RankFrequencyMark)) ≪
        (volume : Measure Real)
  exact htarget

end

end ArchonPhysics.CanonicalOnShellFrequencyMarginalBridge
