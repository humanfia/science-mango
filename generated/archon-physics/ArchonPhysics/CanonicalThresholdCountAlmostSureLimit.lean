import ArchonPhysics.CanonicalScalarIDSUniformBlockLimit
import ArchonPhysics.CanonicalThresholdCountMcDiarmidTails
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost-sure convergence of the canonical threshold count

The sharp fixed-volume McDiarmid estimate is exponentially summable at every
fixed positive deviation.  The first Borel--Cantelli lemma therefore upgrades
concentration about the finite-volume expectation to almost-sure convergence.
The uniform `4 / N` deterministic approximation of those expectations then
identifies the almost-sure limit with `canonicalScalarIDSValue` at every fixed
energy threshold.

The null set in the final theorem may depend on the threshold.  A later dense
threshold argument is needed before one may make a simultaneous statement for
all real energies.
-/

namespace ArchonPhysics.CanonicalThresholdCountAlmostSureLimit

open ArchonPhysics
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSUniformBlockLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmidTails
open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

/-- At every fixed positive deviation, the sequence of bad-event
probabilities is summable in the `ENNReal` sense required by the first
Borel--Cantelli lemma. -/
theorem canonicalThresholdCount_deviation_tsum_ne_top
    (E : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    (∑' n : Nat, RandomEnsemble.canonicalLaw
      {omega | epsilon <=
        |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega -
          (∫ eta,
            canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
              ∂(RandomEnsemble.canonicalLaw))|}) ≠ ∞ := by
  let c : Real := -2 * epsilon ^ 2
  have hc : c < 0 := by
    dsimp [c]
    nlinarith [sq_pos_of_pos hepsilon]
  have hbase : Summable (fun n : Nat => Real.exp ((n : Real) * c)) :=
    Real.summable_exp_nat_mul_iff.mpr hc
  have hboundSummable : Summable (fun n : Nat =>
      2 * Real.exp (-2 * ((n + 1 : Nat) : Real) * epsilon ^ 2)) := by
    have hscaled := hbase.mul_left (2 * Real.exp c)
    apply hscaled.congr
    intro n
    rw [show -2 * ((n + 1 : Nat) : Real) * epsilon ^ 2 =
        ((n : Real) + 1) * c by
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp [c]
      ring]
    rw [add_mul, Real.exp_add]
    ring_nf
  have hmeasureBound : forall n : Nat,
      RandomEnsemble.canonicalLaw
          {omega | epsilon <=
            |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega -
              (∫ eta,
                canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
                  ∂(RandomEnsemble.canonicalLaw))|} <=
        ENNReal.ofReal
          (2 * Real.exp
            (-2 * ((n + 1 : Nat) : Real) * epsilon ^ 2)) := by
    intro n
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal
      (canonicalNormalizedHarmonicThresholdCount_mcDiarmid_twoSided
        (n + 1) E hepsilon.le)
  have hsum_le :
      (∑' n : Nat, RandomEnsemble.canonicalLaw
        {omega | epsilon <=
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega -
            (∫ eta,
              canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
                ∂(RandomEnsemble.canonicalLaw))|}) <=
      ∑' n : Nat, ENNReal.ofReal
        (2 * Real.exp
          (-2 * ((n + 1 : Nat) : Real) * epsilon ^ 2)) := by
    exact ENNReal.tsum_le_tsum hmeasureBound
  exact (hsum_le.trans_lt hboundSummable.tsum_ofReal_lt_top).ne

/-- For a fixed positive deviation, almost every sample violates that
deviation bound only finitely often. -/
theorem canonicalThresholdCount_deviation_eventually_lt_ae
    (E : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      ∀ᶠ n : Nat in atTop,
        |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega -
          (∫ eta,
            canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
              ∂(RandomEnsemble.canonicalLaw))| < epsilon := by
  have hbc := ae_eventually_notMem
    (canonicalThresholdCount_deviation_tsum_ne_top E hepsilon)
  filter_upwards [hbc] with omega homega
  filter_upwards [homega] with n hn
  simpa only [Set.mem_ofPred_eq, not_le] using hn

/-- At every fixed threshold, the canonical normalized count converges
almost surely to its own finite-volume expectation. -/
theorem canonicalThresholdCount_deviation_tendsto_zero_ae (E : Real) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat =>
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega -
            (∫ eta,
              canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
                ∂(RandomEnsemble.canonicalLaw))|)
        atTop (nhds 0) := by
  have hgrid : forall k : Nat,
      ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
        ∀ᶠ n : Nat in atTop,
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega -
            (∫ eta,
              canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
                ∂(RandomEnsemble.canonicalLaw))| <
            1 / ((k + 1 : Nat) : Real) := by
    intro k
    apply canonicalThresholdCount_deviation_eventually_lt_ae
    positivity
  filter_upwards [ae_all_iff.mpr hgrid] with omega homega
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hepsilon
  have hk' : 1 / ((k + 1 : Nat) : Real) < epsilon := by
    simpa only [Nat.cast_add, Nat.cast_one] using hk
  have hkEventually := homega k
  rw [eventually_atTop] at hkEventually
  obtain ⟨N, hN⟩ := hkEventually
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_abs] using (hN n hn).trans hk'

/-- Fixed-threshold self-averaging: the canonical normalized harmonic
threshold count converges almost surely to the deterministic scalar IDS. -/
theorem canonicalNormalizedHarmonicThresholdCount_tendsto_scalarIDS_ae
    (E : Real) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat =>
          canonicalNormalizedHarmonicThresholdCount (n + 1) E omega)
        atTop (nhds (canonicalScalarIDSValue E)) := by
  filter_upwards
    [canonicalThresholdCount_deviation_tendsto_zero_ae E] with omega hdeviation
  have hdist : Tendsto
      (fun n : Nat => dist
        (canonicalNormalizedHarmonicThresholdCount (n + 1) E omega)
        (∫ eta,
          canonicalNormalizedHarmonicThresholdCount (n + 1) E eta
            ∂(RandomEnsemble.canonicalLaw)))
      atTop (nhds 0) := by
    simpa only [Real.dist_eq] using hdeviation
  exact (tendsto_iff_of_dist hdist).mpr
    (canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at E)

end

end ArchonPhysics.CanonicalThresholdCountAlmostSureLimit
