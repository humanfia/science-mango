import ArchonPhysics.ActualSixSiteGoodBlockGlobalLowerBridge

/-!
# Iterated six-block scalar spectral-count gluing

This is the many-block iteration of the genuine shifted rank-four comparison.
The conclusion concerns the actual coupled periodic weighted cycle.  The sum
of isolated six-site periodic counts occurs only as a comparison quantity.
-/

namespace ArchonPhysics.CanonicalShiftedSixBlockSpectralCountGluing

open ArchonPhysics
open ArchonPhysics.ActualSixSiteGoodBlockGlobalLowerBridge
open ArchonPhysics.CanonicalScalarIDSCenterLimit
open Filter

noncomputable section

/-- Sum of the scalar threshold counts of `blockCount` adjacent periodic
six-site restrictions. -/
def shiftedSixBlockThresholdCountSum (shift blockCount : Nat)
    (E : Real) (omega : RandomEnsemble.SampleSpace) : Real :=
  ∑ k ∈ Finset.range blockCount,
    shiftedPeriodicThresholdCount (shift + 6 * k) 6 E omega

/-- The sum of `blockCount + 1` adjacent six-site scalar counts is bounded by
the scalar count of the actual coupled `6 * (blockCount + 1)` periodic cycle,
with accumulated boundary defect `4 * blockCount`. -/
theorem shiftedSixBlockThresholdCountSum_succ_le_coupled
    (shift blockCount : Nat) (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    shiftedSixBlockThresholdCountSum shift (blockCount + 1) E omega <=
      shiftedPeriodicThresholdCount shift (6 * (blockCount + 1)) E omega +
        4 * (blockCount : Real) := by
  induction blockCount with
  | zero =>
      simp [shiftedSixBlockThresholdCountSum]
  | succ blockCount ih =>
      have hglue := shiftedPeriodicThresholdCount_gluing_lower
        (shift := shift) (n := 6 * (blockCount + 1)) (m := 6) E omega
      rw [shiftedSixBlockThresholdCountSum, Finset.sum_range_succ]
      change
        shiftedSixBlockThresholdCountSum shift (blockCount + 1) E omega +
            shiftedPeriodicThresholdCount
              (shift + 6 * (blockCount + 1)) 6 E omega <= _
      calc
        shiftedSixBlockThresholdCountSum shift (blockCount + 1) E omega +
              shiftedPeriodicThresholdCount
                (shift + 6 * (blockCount + 1)) 6 E omega <=
            (shiftedPeriodicThresholdCount shift
                (6 * (blockCount + 1)) E omega +
              4 * (blockCount : Real)) +
                shiftedPeriodicThresholdCount
                  (shift + 6 * (blockCount + 1)) 6 E omega :=
          by linarith [ih]
        _ = (shiftedPeriodicThresholdCount shift
                (6 * (blockCount + 1)) E omega +
              shiftedPeriodicThresholdCount
                (shift + 6 * (blockCount + 1)) 6 E omega) +
              4 * (blockCount : Real) := by ring
        _ <= (shiftedPeriodicThresholdCount shift
                (6 * (blockCount + 1) + 6) E omega + 4) +
              4 * (blockCount : Real) := by
          linarith [hglue]
        _ = shiftedPeriodicThresholdCount shift
              (6 * ((blockCount + 1) + 1)) E omega +
                4 * ((blockCount + 1 : Nat) : Real) := by
          have hsize : 6 * (blockCount + 1) + 6 =
              6 * ((blockCount + 1) + 1) := by omega
          cases hsize
          push_cast
          ring

end

end ArchonPhysics.CanonicalShiftedSixBlockSpectralCountGluing
