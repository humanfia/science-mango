import ArchonPhysics.AlmostAdditiveLimitApproximation
import ArchonPhysics.CanonicalScalarIDSCenterLimit

/-!
# Uniform finite-block approximation of the canonical scalar IDS

The periodic weighted-cycle gluing theorem has a two-sided defect of four.
The original scalar-IDS construction used only its upper half.  Here the
lower half is integrated as well, making the expected unnormalised count
almost additive.  The generic quantitative limit theorem then shows that
every positive finite block approximates the deterministic IDS value with
error at most `4 / N`, uniformly in the energy threshold.
-/

namespace ArchonPhysics.CanonicalScalarIDSBlockApproximation

open ArchonPhysics
open ArchonPhysics.AlmostAdditiveLimitApproximation
open ArchonPhysics.CanonicalScalarIDSCenterLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter MeasureTheory Set Topology

noncomputable section

/-- The lower half of the samplewise four-boundary gluing estimate. -/
theorem canonicalPeriodicThresholdCount_gluing_lower
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (E : Real) (omega : RandomEnsemble.SampleSpace) :
    canonicalPeriodicThresholdCount n E omega +
        shiftedPeriodicThresholdCount n m E omega ≤
      canonicalPeriodicThresholdCount (n + m) E omega + 4 := by
  have h := splitFinWeightedCycle_thresholdCount_defect_le_four
    (canonicalInverseMassVector (n + m) omega) E
  rw [splitFinWeightedCycle_thresholdCount_eq_fin,
    leftWeights_canonicalInverseMassVector,
    rightWeights_canonicalInverseMassVector] at h
  change (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian (canonicalInverseMassVector n omega)) E : Real) +
    (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian (shiftedInverseMassVector n m omega)) E : Real) ≤
    (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian (canonicalInverseMassVector (n + m) omega)) E : Real) + 4
  exact_mod_cast h.2

/-- Translation invariance of the iid law turns the samplewise lower gluing
estimate into the matching lower estimate for expected counts. -/
theorem integral_canonicalPeriodicThresholdCount_gluing_lower
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)] (E : Real) :
    (∫ omega, canonicalPeriodicThresholdCount n E omega
        ∂(RandomEnsemble.canonicalLaw)) +
      (∫ omega, canonicalPeriodicThresholdCount m E omega
        ∂(RandomEnsemble.canonicalLaw)) ≤
      (∫ omega, canonicalPeriodicThresholdCount (n + m) E omega
        ∂(RandomEnsemble.canonicalLaw)) + 4 := by
  have hbig := integrable_canonicalPeriodicThresholdCount (n + m) E
  have hleft := integrable_canonicalPeriodicThresholdCount n E
  have hright := integrable_shiftedPeriodicThresholdCount n m E
  have hsum : Integrable
      (fun omega => canonicalPeriodicThresholdCount n E omega +
        shiftedPeriodicThresholdCount n m E omega)
      RandomEnsemble.canonicalLaw :=
    hleft.add hright
  have hbig4 : Integrable
      (fun omega => canonicalPeriodicThresholdCount (n + m) E omega + 4)
      RandomEnsemble.canonicalLaw :=
    hbig.add (integrable_const 4)
  calc
    (∫ omega, canonicalPeriodicThresholdCount n E omega
        ∂(RandomEnsemble.canonicalLaw)) +
      (∫ omega, canonicalPeriodicThresholdCount m E omega
        ∂(RandomEnsemble.canonicalLaw)) =
      (∫ omega, canonicalPeriodicThresholdCount n E omega
        ∂(RandomEnsemble.canonicalLaw)) +
      (∫ omega, shiftedPeriodicThresholdCount n m E omega
        ∂(RandomEnsemble.canonicalLaw)) := by
          rw [integral_shiftedPeriodicThresholdCount_eq]
    _ = ∫ omega, (canonicalPeriodicThresholdCount n E omega +
          shiftedPeriodicThresholdCount n m E omega)
          ∂(RandomEnsemble.canonicalLaw) := by
        rw [integral_add hleft hright]
    _ ≤ ∫ omega, (canonicalPeriodicThresholdCount (n + m) E omega + 4)
          ∂(RandomEnsemble.canonicalLaw) :=
      integral_mono hsum hbig4
        (fun omega => canonicalPeriodicThresholdCount_gluing_lower E omega)
    _ = (∫ omega, canonicalPeriodicThresholdCount (n + m) E omega
          ∂(RandomEnsemble.canonicalLaw)) + 4 := by
      rw [integral_add hbig (integrable_const 4)]
      simp

/-- Expected unnormalised periodic counts are additive up to the same
two-sided defect four. -/
theorem canonicalThresholdCountCenter_almostAdditive (E : Real) :
    AlmostAdditive (canonicalThresholdCountCenter E) 4 := by
  intro n m
  constructor
  · cases n with
    | zero => simp [canonicalThresholdCountCenter]
    | succ n =>
        cases m with
        | zero => simp [canonicalThresholdCountCenter]
        | succ m =>
            simp only [canonicalThresholdCountCenter]
            have h := integral_canonicalPeriodicThresholdCount_gluing_lower
              (n := n + 1) (m := m + 1) E
            convert h using 1
            congr 1
  · exact canonicalThresholdCountCenter_almostSubadditive E n m

/-- The canonical deterministic scalar IDS, bundled as a function of the
threshold rather than a separate existential witness at every threshold. -/
def canonicalScalarIDSValue (E : Real) : Real :=
  Classical.choose (exists_canonicalThresholdCountCenter_limit E)

theorem canonicalThresholdCountCenter_tendsto_value (E : Real) :
    Tendsto
      (fun N : Nat => canonicalThresholdCountCenter E N / (N : Real))
      atTop (nhds (canonicalScalarIDSValue E)) :=
  Classical.choose_spec (exists_canonicalThresholdCountCenter_limit E)

/-- The IDS value is within `4 / k` of every positive center block. -/
theorem canonicalScalarIDSValue_within_center_block
    (E : Real) (k : Nat) (hk : 0 < k) :
    |canonicalScalarIDSValue E -
        canonicalThresholdCountCenter E k / (k : Real)| ≤
      4 / (k : Real) := by
  exact limit_within_defect_over_block (by norm_num)
    (canonicalThresholdCountCenter_almostAdditive E)
    (canonicalThresholdCountCenter_tendsto_value E) k hk

/-- Uniform-in-threshold finite-volume approximation: the deterministic IDS
and the expected normalized physical harmonic count differ by at most
`4 / N`. -/
theorem canonicalScalarIDSValue_within_expected_block
    (E : Real) (N : Nat) [NeZero N] :
    |canonicalScalarIDSValue E -
        ∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
          ∂(RandomEnsemble.canonicalLaw)| ≤
      4 / (N : Real) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [← canonicalThresholdCountCenter_succ_div_eq_expectation]
      exact canonicalScalarIDSValue_within_center_block E (n + 1) (by omega)

end

end ArchonPhysics.CanonicalScalarIDSBlockApproximation
