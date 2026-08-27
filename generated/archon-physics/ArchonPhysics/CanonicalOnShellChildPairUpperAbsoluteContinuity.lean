import ArchonPhysics.CanonicalOnShellChildPairTrace
import ArchonPhysics.MeasurableThreeWaveBalanceRigidity

/-!
# Automatic upper control for canonical on-shell child-pair traces

At every fixed positive observation time, the broadened canonical measure is
obtained from the raw marked measure by a bounded density.  This module pushes
that bound through the child-frequency projection.  It also records that weak
convergence of the marked broadened measures passes through this continuous
projection, and that the resulting on-shell limiting child measure is carried
by the physical additive triangle.

These statements isolate the two genuinely model-specific inputs still needed
for absolute continuity with respect to planar Lebesgue measure: absolute
continuity of the raw child-frequency law, and uniform absolute-continuity
control strong enough to survive the large-time weak limit.  The elementary
fixed-time bound below grows linearly with the observation time, so it does not
provide the latter input by itself.
-/

namespace ArchonPhysics.CanonicalOnShellChildPairUpperAbsoluteContinuity

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.MeasurableThreeWaveBalanceRigidity
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter
open scoped ENNReal

noncomputable section

variable {X Y Omega : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Omega]

/-- The child-frequency projection is continuous, not merely measurable. -/
theorem continuous_markedChildFrequencyPair :
    Continuous markedChildFrequencyPair := by
  unfold markedChildFrequencyPair
  fun_prop

/-- A fixed-time broadened measure is bounded by the resonance-kernel height
times its underlying raw measure. -/
theorem broadenedResonanceMeasure_le_smul
    (mu : FiniteMeasure X) {mismatch : X -> Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T) :
    (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) <=
      ENNReal.ofReal ((T / 2) * sincSquareMass⁻¹) • (mu : Measure X) := by
  change
    (mu : Measure X).withDensity (broadenedResonanceDensity mismatch T) <=
      ENNReal.ofReal ((T / 2) * sincSquareMass⁻¹) • (mu : Measure X)
  rw [← withDensity_const]
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun x =>
    broadenedResonanceDensity_le mismatch hT x

/-- The same fixed-time quantitative bound survives every measurable
pushforward. -/
theorem map_broadenedResonanceMeasure_le_smul
    (mu : FiniteMeasure X) {mismatch : X -> Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T)
    (f : X -> Y) (hf : Measurable f) :
    Measure.map f
        (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) <=
      ENNReal.ofReal ((T / 2) * sincSquareMass⁻¹) •
        Measure.map f (mu : Measure X) := by
  calc
    _ <= Measure.map f
        (ENNReal.ofReal ((T / 2) * sincSquareMass⁻¹) •
          (mu : Measure X)) :=
      Measure.map_mono
        (broadenedResonanceMeasure_le_smul mu hmismatch hT) hf
    _ = _ := by rw [Measure.map_smul]

/-- Hence every fixed-time pushed-forward broadened measure is absolutely
continuous with respect to the corresponding pushed-forward raw measure. -/
theorem map_broadenedResonanceMeasure_absolutelyContinuous
    (mu : FiniteMeasure X) {mismatch : X -> Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T)
    (f : X -> Y) (hf : Measurable f) :
    Measure.map f
        (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) ≪
      Measure.map f (mu : Measure X) := by
  exact Measure.absolutelyContinuous_of_le_smul
    (map_broadenedResonanceMeasure_le_smul
      mu hmismatch hT f hf)

/-- Canonical specialization of the quantitative fixed-time child-pair
domination.  It has no spectral-regularity hypothesis. -/
theorem canonicalRankFrequencyMarkedBroadened_childPair_le_raw
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    {T : Real} (hT : 0 < T) :
    Measure.map markedChildFrequencyPair
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble sign T hT :
            Measure (Fin 3 -> RankFrequencyMark)) <=
      ENNReal.ofReal ((T / 2) * sincSquareMass⁻¹) •
        Measure.map markedChildFrequencyPair
          (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
            Measure (Fin 3 -> RankFrequencyMark)) := by
  exact map_broadenedResonanceMeasure_le_smul
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
    (measurable_markedFrequencyMismatch sign) hT
    markedChildFrequencyPair measurable_markedChildFrequencyPair

/-- In particular the fixed-time canonical child trace is absolutely
continuous relative to the raw canonical child-frequency law. -/
theorem canonicalRankFrequencyMarkedBroadened_childPair_absolutelyContinuous_raw
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    {T : Real} (hT : 0 < T) :
    Measure.map markedChildFrequencyPair
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble sign T hT :
            Measure (Fin 3 -> RankFrequencyMark)) ≪
      Measure.map markedChildFrequencyPair
        (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
          Measure (Fin 3 -> RankFrequencyMark)) := by
  exact Measure.absolutelyContinuous_of_le_smul
    (canonicalRankFrequencyMarkedBroadened_childPair_le_raw
      ensemble sign hT)

/-- Weak convergence of canonical marked measures passes through the child
projection because that projection is continuous. -/
theorem canonicalRankFrequencyMarkedBroadened_childPair_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target)) :
    Tendsto
      (fun n =>
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n)).map markedChildFrequencyPair)
      atTop (nhds (target.map markedChildFrequencyPair)) := by
  exact FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ hweak
    continuous_markedChildFrequencyPair

/-- The child-pair measure of an on-shell canonical weak limit is carried by
the physical additive triangle, hence restricting to that triangle changes
nothing. -/
theorem canonicalBroadenedWeakLimit_childPair_restrict_triangle_eq_self
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target)) :
    (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) =
      Measure.map markedChildFrequencyPair target := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  have htargetSupport :
      (target : Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 :=
    canonicalBroadenedWeakLimit_compl_uniformSupport_eq_zero
      ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
      time htime_pos target hweak
  have hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈
            Icc (0 : Real) collisionFrequencyCeiling := by
    change ∀ᵐ triad ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
      forall leg : Fin 3,
        (triad leg).2 ∈ Icc (0 : Real) collisionFrequencyCeiling
    exact target_frequency_mem_uniformBand_ae htargetSupport
  have hmem := childPair_ae_mem_triangle collision hfrequencyCollision
  have hrestrict := Measure.restrict_eq_self_of_ae_mem hmem
  simpa [collision,
    childFrequencyPairMeasure_ofCanonicalBroadenedWeakLimit] using hrestrict

/-- Strongest automatic upper-control package currently available for the
actual canonical large-time weak limit: projected weak convergence,
fixed-time quantitative domination by the raw child law, and exact on-shell
triangle support of the limiting child law. -/
theorem canonicalBroadenedWeakLimit_childPair_automatic_upperControl
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target)) :
    Tendsto
        (fun n =>
          (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
            ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
              (time n) (htime_pos n)).map markedChildFrequencyPair)
        atTop (nhds (target.map markedChildFrequencyPair)) ∧
      (forall n,
        Measure.map markedChildFrequencyPair
            (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
              ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
                (time n) (htime_pos n) :
              Measure (Fin 3 -> RankFrequencyMark)) <=
          ENNReal.ofReal
              (((time n) / 2) * sincSquareMass⁻¹) •
            Measure.map markedChildFrequencyPair
              (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
                Measure (Fin 3 -> RankFrequencyMark))) ∧
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) =
        Measure.map markedChildFrequencyPair target := by
  refine ⟨canonicalRankFrequencyMarkedBroadened_childPair_tendsto
      ensemble time htime_pos target hweak, ?_,
    canonicalBroadenedWeakLimit_childPair_restrict_triangle_eq_self
      ensemble time htime_pos htime target hweak⟩
  intro n
  exact canonicalRankFrequencyMarkedBroadened_childPair_le_raw
    ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
      (htime_pos n)

end

end ArchonPhysics.CanonicalOnShellChildPairUpperAbsoluteContinuity
