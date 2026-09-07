import ArchonPhysics

/-!
# Consumer: canonical supervolume uniform no-hit theorem

This consumer locks the unconditional obstruction to the frozen full
positive-mode `g^2` hitting-time law.  It intentionally uses the public
`ArchonPhysics` barrel rather than importing the implementation module.
-/

namespace ArchonPhysicsConsumers.Thermalization.R32CanonicalSupervolumeUniformNoHit

open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.R32CanonicalSupervolumeUniformNoHitV1
open ArchonPhysics.ThermalizationTransfer

noncomputable section

local instance canonicalProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure
      canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

theorem problem_r32_canonical_supervolume_uniform_no_hit
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    {mu delta : Real} (hmu : 0 ≤ mu) (hmuOne : mu < 1)
    (hdelta : delta < (1 : Real) / 8) :
    ¬ ∃ (sizeCutoff : Real → Nat) (lower upper : Real),
      HighProbabilityG2Bounds
        canonicalIIDMassPhaseEnsemble.probability
        (measurableClosedEquilibrationTime
          kappa beta hbeta mu delta)
        sizeCutoff lower upper := by
  exact not_exists_frozen_root_highProbabilityG2Bounds
    hbeta hmu hmuOne hdelta

#print axioms problem_r32_canonical_supervolume_uniform_no_hit

end

end ArchonPhysicsConsumers.Thermalization.R32CanonicalSupervolumeUniformNoHit
