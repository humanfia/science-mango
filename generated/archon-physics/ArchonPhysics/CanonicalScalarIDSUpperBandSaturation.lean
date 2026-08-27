import ArchonPhysics.CanonicalThresholdCountCompactUniformAlmostSureLimit
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Upper-band saturation of the canonical scalar IDS

The frozen mass support gives the deterministic squared-frequency band edge
`5`.  Since threshold counts use the non-strict sublevel convention, every
finite canonical normalized CDF is exactly one at every `E ≥ 5`, including
the endpoint.  Its expectation and the scalar IDS inherit the same identity.

Together with the already established zero lower tail, these exact tail
identities extend compact-uniform convergence on `[0,5]` to uniform
convergence on the whole real energy axis.
-/

namespace ArchonPhysics.CanonicalScalarIDSUpperBandSaturation

open ArchonPhysics
open ArchonPhysics.CanonicalExpectedZeroThresholdCount
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSContinuity
open ArchonPhysics.CanonicalScalarIDSUniformBlockLimit
open ArchonPhysics.CanonicalThresholdCountCompactUniformAlmostSureLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter MeasureTheory Set

noncomputable section

/-- For any frozen iid ensemble, every ordered mode lies below every
threshold `E ≥ 5`, so the complete threshold count equals the volume. -/
theorem iid_orderedEigenvalueThresholdCount_eq_volume_of_five_le
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (N : Nat) [NeZero N] (omega : Omega) {E : Real} (hE : 5 ≤ E) :
    orderedEigenvalueThresholdCount
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) E = N := by
  unfold orderedEigenvalueThresholdCount
  have hfull :
      orderedEigenvalueThresholdIndices
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) E = Finset.univ := by
    ext k
    rw [mem_orderedEigenvalueThresholdIndices_iff]
    simp only [Finset.mem_univ, iff_true]
    exact (iid_orderedEigenvalue_harmonic_le_five ensemble omega k).trans hE
  rw [hfull]
  simp [Lattice.Site]

/-- Every frozen canonical finite-volume normalized CDF is exactly one at
and above the deterministic upper band edge. -/
theorem canonicalNormalizedHarmonicThresholdCount_eq_one_of_five_le
    (N : Nat) [NeZero N] (omega : RandomEnsemble.SampleSpace)
    {E : Real} (hE : 5 ≤ E) :
    canonicalNormalizedHarmonicThresholdCount N E omega = 1 := by
  rw [canonicalNormalizedHarmonicThresholdCount_eq]
  rw [iid_orderedEigenvalueThresholdCount_eq_volume_of_five_le
    canonicalIIDMassPhaseEnsemble N omega hE]
  exact div_self (Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- The expected canonical finite-volume normalized CDF is exactly one at
and above the deterministic upper band edge. -/
theorem expected_canonicalNormalizedHarmonicThresholdCount_eq_one_of_five_le
    (N : Nat) [NeZero N] {E : Real} (hE : 5 ≤ E) :
    (∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
      ∂(RandomEnsemble.canonicalLaw)) = 1 := by
  rw [integral_congr_ae (ae_of_all _ fun omega =>
    canonicalNormalizedHarmonicThresholdCount_eq_one_of_five_le
      N omega hE)]
  simp

/-- The canonical scalar IDS is exactly one at and above the deterministic
upper band edge. -/
theorem canonicalScalarIDSValue_eq_one_of_five_le
    {E : Real} (hE : 5 ≤ E) :
    canonicalScalarIDSValue E = 1 := by
  have hlimit :=
    canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at E
  have hblocks :
      (fun n : Nat =>
        ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
          ∂(RandomEnsemble.canonicalLaw)) = fun _ => 1 := by
    funext n
    exact expected_canonicalNormalizedHarmonicThresholdCount_eq_one_of_five_le
      (n + 1) hE
  have hone :
      Tendsto
        (fun n : Nat =>
          ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
            ∂(RandomEnsemble.canonicalLaw)) atTop (nhds 1) := by
    rw [hblocks]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlimit hone

/-- Uniform convergence on a closed interval extends to the whole real line
when every approximant agrees exactly with the limit on both complementary
tails. -/
theorem tendstoUniformly_of_tendstoUniformlyOn_Icc_of_eqOn_tails
    {I : Type*} {l : Filter I} (F : I → Real → Real) (g : Real → Real)
    {a b : Real}
    (hband : TendstoUniformlyOn F g l (Icc a b))
    (hleft : ∀ i x, x < a → F i x = g x)
    (hright : ∀ i x, b ≤ x → F i x = g x) :
    TendstoUniformly F g l := by
  rw [Metric.tendstoUniformly_iff]
  rw [Metric.tendstoUniformlyOn_iff] at hband
  intro epsilon hepsilon
  filter_upwards [hband epsilon hepsilon] with i hi x
  by_cases hxa : x < a
  · rw [hleft i x hxa]
    simpa using hepsilon
  · by_cases hxb : b ≤ x
    · rw [hright i x hxb]
      simpa using hepsilon
    · exact hi x ⟨le_of_not_gt hxa, le_of_not_ge hxb⟩

/-- Almost surely, the complete finite-volume canonical harmonic CDF
converges uniformly to the scalar IDS on the whole real energy axis. -/
theorem canonicalNormalizedHarmonicThresholdCount_tendstoUniformly_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      TendstoUniformly
        (fun n : Nat ↦ fun E : Real ↦
          canonicalNormalizedHarmonicThresholdCount (n + 1) E omega)
        canonicalScalarIDSValue atTop := by
  filter_upwards
    [canonicalNormalizedHarmonicThresholdCount_tendstoUniformlyOn_Icc_ae]
      with omega hband
  apply tendstoUniformly_of_tendstoUniformlyOn_Icc_of_eqOn_tails
    (F := fun n : Nat ↦ fun E : Real ↦
      canonicalNormalizedHarmonicThresholdCount (n + 1) E omega)
    (g := canonicalScalarIDSValue) hband
  · intro n E hE
    rw [canonicalNormalizedHarmonicThresholdCount_eq_zero_of_lt_zero
      (n + 1) hE omega,
      canonicalScalarIDSValue_eq_zero_of_nonpos hE.le]
  · intro n E hE
    rw [canonicalNormalizedHarmonicThresholdCount_eq_one_of_five_le
      (n + 1) omega hE,
      canonicalScalarIDSValue_eq_one_of_five_le hE]

end

end ArchonPhysics.CanonicalScalarIDSUpperBandSaturation
