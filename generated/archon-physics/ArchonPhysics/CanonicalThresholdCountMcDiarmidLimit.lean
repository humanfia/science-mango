import ArchonPhysics.CanonicalThresholdCountMcDiarmidTails

/-!
# Convergence to the finite-volume expectation

The two-sided McDiarmid estimate implies that, for every fixed positive
deviation and fixed threshold, the deviation probability tends to zero as
the volume grows.  The centering is the expectation at the same volume;
this theorem does not assert that those expectations themselves converge.
-/

namespace ArchonPhysics.CanonicalThresholdCountMcDiarmidLimit

open ArchonPhysics
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmidTails
open Filter MeasureTheory Set Topology

noncomputable section

/-- The canonical normalized threshold count converges in probability to
its own finite-volume expectation along the positive volumes `N = n + 1`. -/
theorem canonicalNormalizedHarmonicThresholdCount_deviationProbability_tendsto_zero
    (E : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto
      (fun n : Nat => RandomEnsemble.canonicalLaw.real
        {omega | epsilon <=
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega -
            (∫ eta,
              canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
                ∂(RandomEnsemble.canonicalLaw))|})
      atTop (nhds 0) := by
  let r : Real := Real.exp (-2 * epsilon ^ 2)
  have hr_nonneg : 0 <= r := Real.exp_nonneg _
  have hr_lt_one : r < 1 := by
    change Real.exp (-2 * epsilon ^ 2) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [sq_pos_of_pos hepsilon]
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  have hbound : Tendsto
      (fun n : Nat => 2 * Real.exp
        (-2 * ((n + 1 : Nat) : Real) * epsilon ^ 2))
      atTop (nhds 0) := by
    have hmul := hpow.mul_const (2 * r)
    convert hmul using 1
    · funext n
      rw [show -2 * ((n + 1 : Nat) : Real) * epsilon ^ 2 =
          ((n + 1 : Nat) : Real) * (-2 * epsilon ^ 2) by ring,
        Real.exp_nat_mul, pow_succ]
      ring
    · ring_nf
  apply squeeze_zero
  · intro n
    exact measureReal_nonneg
  · intro n
    exact canonicalNormalizedHarmonicThresholdCount_mcDiarmid_twoSided
      (n + 1) E hepsilon.le
  · exact hbound

end

end ArchonPhysics.CanonicalThresholdCountMcDiarmidLimit
