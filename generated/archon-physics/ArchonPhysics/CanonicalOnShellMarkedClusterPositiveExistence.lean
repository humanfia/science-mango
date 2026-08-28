import ArchonPhysics.CanonicalOnShellMarkedClusterExistence

/-!
# Positive canonical on-shell marked clusters

The compactness construction preserves the limiting broadened mass.  Thus a
strictly positive scalar on-shell coefficient produces a nonzero resonant
three-wave collision measure, rather than merely a possibly zero cluster.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalOnShellMarkedClusterPositiveExistence

open ArchonPhysics
open ArchonPhysics.CanonicalOnShellMarkedClusterExistence
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A positive scalar broadened-mass limit along times tending to infinity
produces a nonzero resonant marked collision measure with exactly that mass. -/
theorem exists_positive_canonicalOnShellMarkedCluster_of_scalarMass_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (massLimit : NNReal) (hmassLimit : 0 < massLimit)
    (hmass : Tendsto
      (fun n => (canonicalBroadenedCollisionPerSiteMeasureLimit
        ensemble decayInteractionSign (time n) (htime_pos n)).mass)
      atTop (nhds massLimit)) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble decayInteractionSign (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          collision.collisionMeasure.mass = massLimit /\
          collision.collisionMeasure ≠ 0 := by
  obtain ⟨target, subsequence, hmono, hweak, collision, hcollision⟩ :=
    exists_canonicalOnShellMarkedCluster_of_scalarMass_tendsto
      ensemble time htime_pos htime massLimit hmassLimit hmass
  have hscalarSub : Tendsto
      (fun j => (canonicalBroadenedCollisionPerSiteMeasureLimit
        ensemble decayInteractionSign (time (subsequence j))
          (htime_pos (subsequence j))).mass)
      atTop (nhds massLimit) :=
    hmass.comp hmono.tendsto_atTop
  have hmarkedSub : Tendsto
      (fun j =>
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time (subsequence j))
            (htime_pos (subsequence j))).mass)
      atTop (nhds massLimit) := by
    apply hscalarSub.congr'
    exact Eventually.of_forall fun j => by
      apply NNReal.eq
      exact
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_eq_scalar
          ensemble decayInteractionSign (time (subsequence j))
            (htime_pos (subsequence j))).symm
  have htargetMass : target.mass = massLimit :=
    tendsto_nhds_unique hweak.mass hmarkedSub
  have hcollisionMass : collision.collisionMeasure.mass = massLimit := by
    rw [hcollision, htargetMass]
  have hcollisionNonzero : collision.collisionMeasure ≠ 0 := by
    apply collision.collisionMeasure.mass_nonzero_iff.mp
    rw [hcollisionMass]
    exact hmassLimit.ne'
  exact ⟨target, subsequence, collision, hmono, hweak, hcollision,
    hcollisionMass, hcollisionNonzero⟩

end

end ArchonPhysics.CanonicalOnShellMarkedClusterPositiveExistence
