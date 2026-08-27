import ArchonPhysics.CanonicalScalarIDSBlockApproximation
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform finite-block convergence to the canonical scalar IDS

The two-sided periodic gluing estimate bounds the expected normalized count
by `4 / N` at every threshold.  Consequently the sequence of expected counts
on volumes `n + 1` converges uniformly on the whole real energy axis to the
bundled canonical scalar IDS.
-/

namespace ArchonPhysics.CanonicalScalarIDSUniformBlockLimit

open ArchonPhysics
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open Filter MeasureTheory Topology

noncomputable section

theorem canonicalExpectedBlocks_tendstoUniformly_scalarIDS :
    TendstoUniformly
      (fun n : Nat => fun E : Real =>
        ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
          ∂(RandomEnsemble.canonicalLaw))
      canonicalScalarIDSValue atTop := by
  have hvanish : Tendsto
      (fun n : Nat => (4 : Real) / ((n + 1 : Nat) : Real))
      atTop (nhds 0) := by
    have hbase :
        Tendsto (fun n : Nat => (4 : Real) / (n : Real))
          atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun n : Nat => (4 : Real) / (n : Real))
            atTop (nhds 0))
    exact hbase.comp (tendsto_add_atTop_nat 1)
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  filter_upwards [hvanish.eventually (Iio_mem_nhds hepsilon)] with n hn E
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (canonicalScalarIDSValue_within_expected_block E (n + 1)) hn

theorem canonicalExpectedBlocks_tendstoUniformlyOn_scalarIDS
    (S : Set Real) :
    TendstoUniformlyOn
      (fun n : Nat => fun E : Real =>
        ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
          ∂(RandomEnsemble.canonicalLaw))
      canonicalScalarIDSValue atTop S :=
  canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendstoUniformlyOn

end

end ArchonPhysics.CanonicalScalarIDSUniformBlockLimit
