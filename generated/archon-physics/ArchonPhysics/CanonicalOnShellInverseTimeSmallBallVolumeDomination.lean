import ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower

/-!
# Positive canonical on-shell clusters from lower small balls and volume domination

This module combines the inverse-time lower small-ball bridge with the
time-uniform upper bound supplied by domination of the scalar thermodynamic
mismatch measure by a finite multiple of Lebesgue measure.  No independent
broadened-mass upper-bound premise remains.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalOnShellInverseTimeSmallBallVolumeDomination

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- An inverse-time lower small-ball estimate and finite Lebesgue domination
of the scalar mismatch limit produce a nonzero canonical on-shell marked
cluster.  Lebesgue domination supplies the upper broadened-mass bound via the
unit-mass normalization of the resonance kernel. -/
theorem exists_positive_canonicalOnShellMarkedCluster_of_inverseTimeSmallBallLower_of_volumeDomination
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (slope : Real) (hslope : 0 < slope)
    (dominationConstant : NNReal)
    (hsmallBall : ∀ᶠ n in atTop,
      slope / time n <=
        (canonicalCollisionPerSiteMeasureLimit
          ensemble
            RandomMassThreeWaveCollisionNetwork.decayInteractionSign : Measure Real).real
          (absoluteMismatchSublevel (1 / (4 * time n))))
    (hdomination :
      (canonicalCollisionPerSiteMeasureLimit
        ensemble
          RandomMassThreeWaveCollisionNetwork.decayInteractionSign : Measure Real) <=
        dominationConstant • (volume : Measure Real)) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
                  (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          Real.toNNReal (slope / (4 * Real.pi)) <=
            collision.collisionMeasure.mass /\
          collision.collisionMeasure.mass <= dominationConstant /\
          collision.collisionMeasure ≠ 0 := by
  have hmassUpper : ∀ᶠ n in atTop,
      (canonicalBroadenedCollisionPerSiteMeasureLimit
        ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
          (time n) (htime_pos n)).mass <= dominationConstant :=
    Eventually.of_forall fun n => by
      apply NNReal.coe_le_coe.mp
      simpa [canonicalBroadenedCollisionPerSiteMeasureLimit] using
        broadenedResonanceMeasure_mass_le_of_le_smul_volume
          (canonicalCollisionPerSiteMeasureLimit
            ensemble
              RandomMassThreeWaveCollisionNetwork.decayInteractionSign)
          dominationConstant hdomination (htime_pos n)
  exact
    exists_positive_canonicalOnShellMarkedCluster_of_inverseTimeSmallBallLower
      ensemble time htime_pos htime slope hslope dominationConstant
      hsmallBall hmassUpper

end

end ArchonPhysics.CanonicalOnShellInverseTimeSmallBallVolumeDomination
