import ArchonPhysics.CanonicalShiftedSixBlockSpectralCountGluing

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalScalarIDSCenterLimit
open ArchonPhysics.CanonicalShiftedSixBlockSpectralCountGluing

noncomputable section

/-- Standalone acceptance theorem for many-block scalar spectral gluing. -/
theorem problem_canonical_shifted_six_block_spectral_count_gluing
    (shift blockCount : Nat) (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    shiftedSixBlockThresholdCountSum shift (blockCount + 1) E omega <=
      shiftedPeriodicThresholdCount shift (6 * (blockCount + 1)) E omega +
        4 * (blockCount : Real) := by
  exact shiftedSixBlockThresholdCountSum_succ_le_coupled
    shift blockCount E omega

end

end ArchonPhysicsConsumers.Thermalization
