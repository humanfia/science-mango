import ArchonPhysics.CanonicalExpectedThresholdCountContinuity
import ArchonPhysics.CanonicalExpectedZeroThresholdCount
import ArchonPhysics.CanonicalScalarIDSUniformBlockLimit
import ArchonPhysics.FixedEnergySpectrumAvoidance

/-!
# Continuity of the canonical scalar IDS

At a positive energy, finite canonical expected threshold counts are
continuous because a fixed energy is almost surely absent from the finite
spectrum.  At zero, their right continuity is enough.  Thus every finite
expected block is continuous on the nonnegative half-line, and uniform block
convergence transfers this continuity to the canonical scalar IDS.

At negative energies every finite block vanishes, while at zero its value is
`1 / N`.  Pointwise uniqueness of the same uniform limit makes the scalar IDS
zero on the nonpositive half-line.  Gluing the two closed half-lines then
gives continuity on all real energies.
-/

namespace ArchonPhysics.CanonicalScalarIDSContinuity

open ArchonPhysics
open ArchonPhysics.CanonicalExpectedThresholdCountContinuity
open ArchonPhysics.CanonicalExpectedZeroThresholdCount
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSUniformBlockLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter MeasureTheory Set Topology

noncomputable section

/-- The bounded canonical normalized count is integrable at every finite
volume and threshold. -/
theorem integrable_canonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real) :
    Integrable (canonicalNormalizedHarmonicThresholdCount N E)
      RandomEnsemble.canonicalLaw := by
  apply Integrable.of_bound
    (measurable_canonicalNormalizedHarmonicThresholdCount N E).aestronglyMeasurable 1
  exact ae_of_all _ fun omega => by
    have hmem :=
      canonicalNormalizedHarmonicThresholdCount_mem_Icc N E omega
    rw [Real.norm_eq_abs, abs_of_nonneg hmem.1]
    exact hmem.2

/-- For each finite volume and mass sample, the normalized spectral CDF is
monotone in its energy threshold. -/
theorem monotone_canonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (omega : RandomEnsemble.SampleSpace) :
    Monotone (fun E => canonicalNormalizedHarmonicThresholdCount N E omega) := by
  intro EA EB hE
  change canonicalNormalizedHarmonicThresholdCount N EA omega ≤
    canonicalNormalizedHarmonicThresholdCount N EB omega
  rw [canonicalNormalizedHarmonicThresholdCount_eq,
    canonicalNormalizedHarmonicThresholdCount_eq]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast orderedEigenvalueThresholdCount_le_of_pointwise
      (A := harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega))
      (B := harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega))
      (EA := EA) (EB := EB) (fun _ hk => hk.trans hE)
  · positivity

/-- Every finite canonical expected spectral CDF is monotone in its energy
threshold. -/
theorem monotone_expectedCanonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] :
    Monotone
      (fun E => ∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
        ∂(RandomEnsemble.canonicalLaw)) := by
  intro EA EB hE
  exact integral_mono
    (integrable_canonicalNormalizedHarmonicThresholdCount N EA)
    (integrable_canonicalNormalizedHarmonicThresholdCount N EB)
    (fun omega =>
      monotone_canonicalNormalizedHarmonicThresholdCount N omega hE)

/-- The canonical scalar IDS is monotone in energy. -/
theorem monotone_canonicalScalarIDSValue :
    Monotone canonicalScalarIDSValue := by
  intro EA EB hE
  exact le_of_tendsto_of_tendsto'
    (canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at EA)
    (canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at EB)
    (fun n =>
      monotone_expectedCanonicalNormalizedHarmonicThresholdCount
        (n + 1) hE)

/-- Every finite canonical expected spectral CDF is continuous on the
nonnegative energy half-line.  The endpoint uses right continuity, while
positive energies use almost-sure fixed-energy spectrum avoidance. -/
theorem continuousOn_expectedCanonicalNormalizedHarmonicThresholdCount_Ici_zero
    (N : Nat) [NeZero N] :
    ContinuousOn
      (fun E => ∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
        ∂(RandomEnsemble.canonicalLaw)) (Ici 0) := by
  intro E hE
  change 0 ≤ E at hE
  rcases hE.eq_or_lt with hzero | hpositive
  · subst E
    exact
      continuousWithinAt_expectedCanonicalNormalizedHarmonicThresholdCount_Ici
        N 0
  · have hnull := probability_harmonic_charpoly_eval_eq_zero
      canonicalIIDMassPhaseEnsemble (N := N) hpositive.ne'
    have havoid : ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
        (Matrix.charpoly
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)).1).eval E ≠ 0 := by
      simpa only [harmonicHermitian, Set.mem_ofPred_eq,
        canonicalIIDMassPhaseEnsemble] using
        (measure_eq_zero_iff_ae_notMem.mp hnull)
    exact
      (continuousAt_expectedCanonicalNormalizedHarmonicThresholdCount
        N E havoid).continuousWithinAt

/-- Uniform finite-block convergence makes the canonical scalar IDS
continuous on the nonnegative energy half-line. -/
theorem continuousOn_canonicalScalarIDSValue_Ici_zero :
    ContinuousOn canonicalScalarIDSValue (Ici 0) := by
  apply
    (canonicalExpectedBlocks_tendstoUniformlyOn_scalarIDS (Ici 0)).continuousOn
  exact (Eventually.of_forall fun n =>
    continuousOn_expectedCanonicalNormalizedHarmonicThresholdCount_Ici_zero
      (n + 1)).frequently

/-- The scalar IDS vanishes at every strictly negative energy. -/
theorem canonicalScalarIDSValue_eq_zero_of_lt_zero
    {E : Real} (hE : E < 0) :
    canonicalScalarIDSValue E = 0 := by
  have hlimit :=
    canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at E
  have hblocks :
      (fun n : Nat =>
          ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
            ∂(RandomEnsemble.canonicalLaw)) = fun _ => 0 := by
    funext n
    exact expected_canonicalNormalizedHarmonicThresholdCount_eq_zero_of_lt_zero
      (n + 1) hE
  have hzero :
      Tendsto
        (fun n : Nat =>
          ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
            ∂(RandomEnsemble.canonicalLaw)) atTop (nhds 0) := by
    rw [hblocks]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlimit hzero

/-- The acoustic zero-mode atom has weight `1 / N` in a finite block, hence
disappears in the thermodynamic scalar IDS. -/
theorem canonicalScalarIDSValue_zero :
    canonicalScalarIDSValue 0 = 0 := by
  have hlimit :=
    canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at 0
  have hrecip :
      Tendsto (fun n : Nat => (1 : Real) / ((n + 1 : Nat) : Real))
        atTop (nhds 0) := by
    have hbase :
        Tendsto (fun n : Nat => (1 : Real) / (n : Real))
          atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun n : Nat => (1 : Real) / (n : Real))
            atTop (nhds 0))
    exact hbase.comp (tendsto_add_atTop_nat 1)
  have hzero :
      Tendsto
        (fun n : Nat =>
          ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) 0 omega
            ∂(RandomEnsemble.canonicalLaw)) atTop (nhds 0) := by
    apply hrecip.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (expected_canonicalNormalizedHarmonicThresholdCount_zero
      (N := n + 1) (by omega)).symm
  exact tendsto_nhds_unique hlimit hzero

/-- The scalar IDS is identically zero on the nonpositive half-line. -/
theorem canonicalScalarIDSValue_eq_zero_of_nonpos
    {E : Real} (hE : E ≤ 0) :
    canonicalScalarIDSValue E = 0 := by
  rcases hE.eq_or_lt with rfl | hE
  · exact canonicalScalarIDSValue_zero
  · exact canonicalScalarIDSValue_eq_zero_of_lt_zero hE

/-- The canonical scalar IDS is continuous at every real energy. -/
theorem continuous_canonicalScalarIDSValue :
    Continuous canonicalScalarIDSValue := by
  rw [← continuousOn_univ]
  rw [← Iic_union_Ici (a := (0 : Real))]
  apply ContinuousOn.union_of_isClosed
  · refine (continuousOn_congr (f := fun _ : Real => 0)
      (g := canonicalScalarIDSValue) (s := Iic 0) (fun E hE => ?_)).mpr
        continuousOn_const
    exact canonicalScalarIDSValue_eq_zero_of_nonpos hE
  · exact continuousOn_canonicalScalarIDSValue_Ici_zero
  · exact isClosed_Iic
  · exact isClosed_Ici

end

end ArchonPhysics.CanonicalScalarIDSContinuity
