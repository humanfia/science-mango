import ArchonPhysics.CanonicalOnShellMarkedCluster
import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
import ArchonPhysics.CanonicalRankFrequencyMarkedLimitCompactSupport
import ArchonPhysics.PositiveMassCompactSupportedFiniteMeasureSubsequence
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Existence of canonical on-shell clusters from scalar mass convergence

The deterministic marked collision measure and all of its positive-time
broadenings live in one compact rank-frequency box.  Therefore convergence
of the scalar broadened total mass is enough to extract a finite marked weak
cluster.  Along a time sequence tending to infinity, the cluster is then an
actual `ResonantThreeWaveMeasure` by the exact-support theorem.

The only model-specific premise left exposed here is convergence of the
scalar broadened collision coefficient.  No density or trace is assumed
silently.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalOnShellMarkedClusterExistence

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedLimitCompactSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.PositiveMassCompactSupportedFiniteMeasureSubsequence
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic normalized marked thermodynamic limit retains the
same common compact box as every finite-volume marked measure. -/
theorem markedLimit_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedMeasureLimit ensemble :
      Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  exact
    canonicalRankFrequencyMarkedMeasureLimit_compl_uniformSupport_eq_zero
      ensemble

/-- Restoring the deterministic per-site collision mass preserves the common
compact marked support. -/
theorem canonicalRankFrequencyMarkedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
      Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  unfold canonicalRankFrequencyMarkedPerSiteMeasureLimit
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change _ * (canonicalRankFrequencyMarkedMeasureLimit ensemble : Measure _)
    collisionRankFrequencyTripleSupportᶜ = 0
  rw [markedLimit_compl_uniformSupport_eq_zero]
  simp

/-- Weighting by a finite-time resonance density cannot create mass outside
the compact support of the raw marked collision limit. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (T : Real) (hT : 0 < T) :
    (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign T hT : Measure (Fin 3 -> RankFrequencyMark))
      collisionRankFrequencyTripleSupportᶜ = 0 := by
  change
    ((canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble : Measure _).withDensity
      (broadenedResonanceDensity
        (CanonicalRankFrequencyMarkedResonanceLimit.markedFrequencyMismatch sign) T))
      collisionRankFrequencyTripleSupportᶜ = 0
  exact withDensity_absolutelyContinuous _ _
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
      ensemble)

/-- If the deterministic scalar broadened masses converge along a positive
time sequence, the corresponding marked broadenings have a finite weakly
convergent subsequence. -/
theorem exists_canonicalMarkedBroadened_weaklyConvergent_subsequence_of_scalarMass_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (massLimit : NNReal)
    (hmassLimit : 0 < massLimit)
    (hmass : Tendsto
      (fun n => (canonicalBroadenedCollisionPerSiteMeasureLimit
        ensemble sign (time n) (htime_pos n)).mass)
      atTop (nhds massLimit)) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble sign (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) := by
  let mu : Nat -> FiniteMeasure (Fin 3 -> RankFrequencyMark) := fun n =>
    canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
      ensemble sign (time n) (htime_pos n)
  have hmarkedMass : Tendsto (fun n => (mu n).mass)
      atTop (nhds massLimit) := by
    apply hmass.congr'
    exact Eventually.of_forall fun n => by
      apply NNReal.eq
      exact
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_eq_scalar
          ensemble sign (time n) (htime_pos n)).symm
  obtain ⟨target, subsequence, hmono, hweak⟩ :=
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_tendsto_pos
      mu massLimit hmassLimit collisionRankFrequencyTripleSupport
      collisionRankFrequencyTripleSupport_isCompact hmarkedMass
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
          ensemble sign (time n) (htime_pos n))
  exact ⟨target, subsequence, hmono, hweak⟩

/-- Scalar broadened-mass convergence along times tending to infinity
produces a genuine finite canonical resonant three-wave cluster. -/
theorem exists_canonicalOnShellMarkedCluster_of_scalarMass_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (massLimit : NNReal)
    (hmassLimit : 0 < massLimit)
    (hmass : Tendsto
      (fun n => (canonicalBroadenedCollisionPerSiteMeasureLimit
        ensemble decayInteractionSign (time n) (htime_pos n)).mass)
      atTop (nhds massLimit)) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble decayInteractionSign (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) /\
          exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
            collision.collisionMeasure = target := by
  obtain ⟨target, subsequence, hmono, hweak⟩ :=
    exists_canonicalMarkedBroadened_weaklyConvergent_subsequence_of_scalarMass_tendsto
      ensemble decayInteractionSign time htime_pos massLimit hmassLimit hmass
  let collision : ResonantThreeWaveMeasure RankFrequencyMark :=
    ofCanonicalBroadenedWeakLimit ensemble
      (fun j => time (subsequence j))
      (fun j => htime_pos (subsequence j))
      (htime.comp hmono.tendsto_atTop) target hweak
  exact ⟨target, subsequence, hmono, hweak, collision, rfl⟩

end

end ArchonPhysics.CanonicalOnShellMarkedClusterExistence
