import ArchonPhysics.AlmostSubadditiveLimit
import ArchonPhysics.CanonicalThresholdCountMcDiarmidLimit
import ArchonPhysics.CenteredConcentrationTransfer
import ArchonPhysics.PeriodicWeightedCycleBlockGluing
import ArchonPhysics.RandomMassResultantBridge
import ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

/-!
# Canonical scalar IDS center limit

The periodic weighted cycle can be split into two smaller periodic cycles at
the cost of four signed rank-one boundary terms.  In the canonical iid mass
ensemble the two restrictions have the corresponding smaller product laws.
Consequently the expected unnormalised threshold counts are subadditive up
to four, and their volume-normalised expectations have a deterministic
limit by the almost-subadditive Fekete lemma.

The characteristic-polynomial bridge below identifies the edge-space cycle
count with the physical mass-weighted harmonic count, including the zero
mode and multiplicities.  Combining the center limit with the sharp
McDiarmid estimate therefore gives convergence in probability, at every
fixed threshold, to a non-random scalar IDS value.
-/

namespace ArchonPhysics.CanonicalScalarIDSCenterLimit

open ArchonPhysics
open ArchonPhysics.AlmostSubadditiveLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmid
open ArchonPhysics.CanonicalThresholdCountMcDiarmidTails
open ArchonPhysics.CanonicalThresholdCountMcDiarmidLimit
open ArchonPhysics.FiniteVolumeSpectralCountGluing
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter Function MeasureTheory ProbabilityTheory Set Topology

noncomputable section

/-- The physical Gram matrix and the reindexed edge-space weighted cycle
have exactly the same threshold count, including algebraic multiplicity. -/
theorem harmonic_thresholdCount_eq_finWeighted_inverseMass
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) (E : Real) :
    orderedEigenvalueThresholdCount (harmonicHermitian m) E =
      orderedEigenvalueThresholdCount
        (finWeightedCycleHermitian (RandomMassResultantBridge.inverseMassCoordinates m)) E := by
  let w := RandomMassResultantBridge.inverseMassCoordinates m
  have hchar :
      (massWeightedHarmonicMatrix m).charpoly =
        (finWeightedCycleLaplacian w).charpoly := by
    calc
      (massWeightedHarmonicMatrix m).charpoly =
          (massWeightedDifferenceMatrix m *
            Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly :=
        Matrix.charpoly_mul_comm
          (Matrix.transpose (massWeightedDifferenceMatrix m))
          (massWeightedDifferenceMatrix m)
      _ = (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)).charpoly := by
        rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
      _ = (weightedCycleLaplacian (weightsOfCoordinates w)).charpoly := by
        rw [RandomMassResultantBridge.weightsOfCoordinates_inverseMassCoordinates]
      _ = (finWeightedCycleLaplacian w).charpoly := by
        symm
        exact Matrix.charpoly_reindex _ _
  calc
    orderedEigenvalueThresholdCount (harmonicHermitian m) E =
        ((massWeightedHarmonicMatrix m).charpoly.roots.filter fun x => x ≤ E).card := by
      simpa [harmonicHermitian] using
        orderedEigenvalueThresholdCount_eq_card_filter_roots
          (massWeightedHarmonicMatrix m)
          (massWeightedHarmonicMatrix_posSemidef m).isHermitian E
    _ = ((finWeightedCycleLaplacian w).charpoly.roots.filter fun x => x ≤ E).card := by
      rw [hchar]
    _ = orderedEigenvalueThresholdCount (finWeightedCycleHermitian w) E := by
      symm
      simpa [finWeightedCycleHermitian] using
        orderedEigenvalueThresholdCount_eq_card_filter_roots
          (finWeightedCycleLaplacian w) (finWeightedCycleHermitian w).2 E

/-- Inverse masses of the first `N` canonical coordinates. -/
def canonicalInverseMassVector (N : Nat)
    (omega : RandomEnsemble.SampleSpace) : Fin N → Real :=
  fun i => (RandomEnsemble.massAt i.val omega)⁻¹

/-- Inverse masses of a length-`N` block beginning at `shift`. -/
def shiftedInverseMassVector (shift N : Nat)
    (omega : RandomEnsemble.SampleSpace) : Fin N → Real :=
  fun i => (RandomEnsemble.massAt (shift + i.val) omega)⁻¹

theorem inverseMassCoordinates_restrictPositiveMass
    (N : Nat) [NeZero N] (omega : RandomEnsemble.SampleSpace) :
    RandomMassResultantBridge.inverseMassCoordinates
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega) =
      canonicalInverseMassVector N omega := by
  funext i
  simp [RandomMassResultantBridge.inverseMassCoordinates,
    canonicalInverseMassVector,
    PeriodicWeightedCycleBlockGluing.val_siteEquivFin_symm,
    canonicalIIDMassPhaseEnsemble]

/-- Unnormalised edge-space threshold count for the first `N` canonical
mass coordinates. -/
def canonicalPeriodicThresholdCount (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) : Real :=
  orderedEigenvalueThresholdCount
    (finWeightedCycleHermitian (canonicalInverseMassVector N omega)) E

/-- The edge-space count is exactly `N` times the established normalized
physical harmonic count. -/
theorem canonicalPeriodicThresholdCount_eq_mul_normalized
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalPeriodicThresholdCount N E omega =
      (N : Real) * canonicalNormalizedHarmonicThresholdCount N E omega := by
  rw [canonicalPeriodicThresholdCount,
    canonicalNormalizedHarmonicThresholdCount_eq]
  rw [← inverseMassCoordinates_restrictPositiveMass N omega,
    ← harmonic_thresholdCount_eq_finWeighted_inverseMass]
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  field_simp

/-- Shifted finite canonical mass vector. -/
def canonicalShiftedFinMassVector (shift N : Nat)
    (omega : RandomEnsemble.SampleSpace) : Fin N → Real :=
  fun i => RandomEnsemble.massAt (shift + i.val) omega

theorem measurable_canonicalShiftedFinMassVector (shift N : Nat) :
    Measurable (canonicalShiftedFinMassVector shift N) := by
  exact measurable_pi_lambda _ fun i =>
    RandomEnsemble.measurable_massAt (shift + i.val)

/-- Every shifted finite block has the same finite iid product law as the
first block of the same length. -/
theorem canonicalShiftedFinMassVector_hasLaw (shift N : Nat) :
    HasLaw (canonicalShiftedFinMassVector shift N)
      (Measure.pi fun _ : Fin N => RandomEnsemble.massCoordinateLaw)
      RandomEnsemble.canonicalLaw := by
  have hinj : Injective (fun i : Fin N => shift + i.val) := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel hij
  exact (RandomEnsemble.massCoordinates_iIndep.precomp hinj).hasLaw_pi
    (fun i => RandomEnsemble.massAt_hasLaw (shift + i.val))

/-- Unnormalised edge-space threshold count for a shifted canonical block. -/
def shiftedPeriodicThresholdCount (shift N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) : Real :=
  orderedEigenvalueThresholdCount
    (finWeightedCycleHermitian (shiftedInverseMassVector shift N omega)) E

theorem shiftedPeriodicThresholdCount_eq_mul_finNormalized
    (shift N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    shiftedPeriodicThresholdCount shift N E omega =
      (N : Real) * finNormalizedHarmonicThresholdCount N E
        (canonicalShiftedFinMassVector shift N omega) := by
  let m : Lattice.PositiveMassConfig N :=
    clippedPositiveMassConfig
      (siteVectorOfFin (canonicalShiftedFinMassVector shift N omega))
  have hm (i : Fin N) :
      RandomMassResultantBridge.inverseMassCoordinates m i =
        shiftedInverseMassVector shift N omega i := by
    simp [m, RandomMassResultantBridge.inverseMassCoordinates,
      clippedPositiveMassConfig, siteVectorOfFin,
      canonicalShiftedFinMassVector, shiftedInverseMassVector,
      PeriodicWeightedCycleBlockGluing.val_siteEquivFin_symm,
      RandomEnsemble.clippedMass_eq_self
        (RandomEnsemble.massAt_mem_support (shift + i.val) omega)]
  rw [shiftedPeriodicThresholdCount,
    finNormalizedHarmonicThresholdCount,
    clippedNormalizedHarmonicThresholdCount]
  change (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian (shiftedInverseMassVector shift N omega)) E : Real) =
    (N : Real) * ((orderedEigenvalueThresholdCount (harmonicHermitian m) E : Real) /
      (N : Real))
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  rw [mul_div_cancel₀ _ hN]
  rw [← funext hm]
  exact_mod_cast (harmonic_thresholdCount_eq_finWeighted_inverseMass m E).symm

theorem measurable_canonicalPeriodicThresholdCount
    (N : Nat) [NeZero N] (E : Real) :
    Measurable (canonicalPeriodicThresholdCount N E) := by
  rw [show canonicalPeriodicThresholdCount N E =
      fun omega => (N : Real) *
        canonicalNormalizedHarmonicThresholdCount N E omega by
    funext omega
    exact canonicalPeriodicThresholdCount_eq_mul_normalized N E omega]
  exact measurable_const.mul (measurable_canonicalNormalizedHarmonicThresholdCount N E)

theorem measurable_shiftedPeriodicThresholdCount
    (shift N : Nat) [NeZero N] (E : Real) :
    Measurable (shiftedPeriodicThresholdCount shift N E) := by
  rw [show shiftedPeriodicThresholdCount shift N E =
      fun omega => (N : Real) * finNormalizedHarmonicThresholdCount N E
        (canonicalShiftedFinMassVector shift N omega) by
    funext omega
    exact shiftedPeriodicThresholdCount_eq_mul_finNormalized shift N E omega]
  exact measurable_const.mul
    ((measurable_finNormalizedHarmonicThresholdCount N E).comp
      (measurable_canonicalShiftedFinMassVector shift N))

theorem integrable_canonicalPeriodicThresholdCount
    (N : Nat) [NeZero N] (E : Real) :
    Integrable (canonicalPeriodicThresholdCount N E)
      RandomEnsemble.canonicalLaw := by
  refine Integrable.mono' (integrable_const (N : Real))
    (measurable_canonicalPeriodicThresholdCount N E).aestronglyMeasurable
    (ae_of_all _ fun omega => ?_)
  rw [canonicalPeriodicThresholdCount_eq_mul_normalized]
  have h := canonicalNormalizedHarmonicThresholdCount_mem_Icc N E omega
  rw [Real.norm_eq_abs]
  have hN : 0 ≤ (N : Real) := Nat.cast_nonneg N
  rw [abs_of_nonneg (mul_nonneg hN h.1)]
  exact (mul_le_mul_of_nonneg_left h.2 hN).trans_eq (mul_one _)


theorem integrable_shiftedPeriodicThresholdCount
    (shift N : Nat) [NeZero N] (E : Real) :
    Integrable (shiftedPeriodicThresholdCount shift N E)
      RandomEnsemble.canonicalLaw := by
  refine Integrable.mono' (integrable_const (N : Real))
    (measurable_shiftedPeriodicThresholdCount shift N E).aestronglyMeasurable
    (ae_of_all _ fun omega => ?_)
  rw [shiftedPeriodicThresholdCount_eq_mul_finNormalized]
  have h := finNormalizedHarmonicThresholdCount_mem_Icc N E
    (canonicalShiftedFinMassVector shift N omega)
  rw [Real.norm_eq_abs]
  have hN : 0 ≤ (N : Real) := Nat.cast_nonneg N
  rw [abs_of_nonneg (mul_nonneg hN h.1)]
  exact (mul_le_mul_of_nonneg_left h.2 hN).trans_eq (mul_one _)

theorem canonicalPeriodicThresholdCount_eq_mul_finNormalized
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalPeriodicThresholdCount N E omega =
      (N : Real) * finNormalizedHarmonicThresholdCount N E
        (canonicalFinMassVector N omega) := by
  rw [canonicalPeriodicThresholdCount_eq_mul_normalized,
    finNormalizedHarmonicThresholdCount_canonicalFinMassVector]

/-- Translation invariance of the iid product law makes every shifted block
have the same expected periodic spectral count as the first block. -/
theorem integral_shiftedPeriodicThresholdCount_eq
    (shift N : Nat) [NeZero N] (E : Real) :
    (∫ omega, shiftedPeriodicThresholdCount shift N E omega
        ∂(RandomEnsemble.canonicalLaw)) =
      ∫ omega, canonicalPeriodicThresholdCount N E omega
        ∂(RandomEnsemble.canonicalLaw) := by
  let productLaw : Measure (Fin N → Real) :=
    Measure.pi fun _ : Fin N => RandomEnsemble.massCoordinateLaw
  let f : (Fin N → Real) → Real := fun x =>
    (N : Real) * finNormalizedHarmonicThresholdCount N E x
  have hf : AEStronglyMeasurable f productLaw := by
    exact (measurable_const.mul
      (measurable_finNormalizedHarmonicThresholdCount N E)).aestronglyMeasurable
  calc
    (∫ omega, shiftedPeriodicThresholdCount shift N E omega
        ∂(RandomEnsemble.canonicalLaw)) =
        ∫ omega, f (canonicalShiftedFinMassVector shift N omega)
          ∂(RandomEnsemble.canonicalLaw) := by
      apply integral_congr_ae
      exact ae_of_all _ fun omega =>
        shiftedPeriodicThresholdCount_eq_mul_finNormalized shift N E omega
    _ = ∫ x, f x ∂productLaw :=
      (canonicalShiftedFinMassVector_hasLaw shift N).integral_comp hf
    _ = ∫ omega, f (canonicalFinMassVector N omega)
          ∂(RandomEnsemble.canonicalLaw) :=
      ((canonicalFinMassVector_hasLaw N).integral_comp hf).symm
    _ = ∫ omega, canonicalPeriodicThresholdCount N E omega
          ∂(RandomEnsemble.canonicalLaw) := by
      apply integral_congr_ae
      exact ae_of_all _ fun omega =>
        (canonicalPeriodicThresholdCount_eq_mul_finNormalized N E omega).symm

/-- Splitting coordinates is only a reindexing and hence preserves the full
threshold count. -/
theorem splitFinWeightedCycle_thresholdCount_eq_fin
    {n m : Nat} [NeZero (n + m)] (w : Fin (n + m) → Real) (E : Real) :
    orderedEigenvalueThresholdCount (splitFinWeightedCycleHermitian w) E =
      orderedEigenvalueThresholdCount (finWeightedCycleHermitian w) E := by
  have hchar : (splitFinWeightedCycleLaplacian w).charpoly =
      (finWeightedCycleLaplacian w).charpoly := by
    exact Matrix.charpoly_reindex _ _
  calc
    orderedEigenvalueThresholdCount (splitFinWeightedCycleHermitian w) E =
        ((splitFinWeightedCycleLaplacian w).charpoly.roots.filter
          fun x => x ≤ E).card := by
      simpa [splitFinWeightedCycleHermitian] using
        orderedEigenvalueThresholdCount_eq_card_filter_roots
          (splitFinWeightedCycleLaplacian w)
          (splitFinWeightedCycleHermitian w).2 E
    _ = ((finWeightedCycleLaplacian w).charpoly.roots.filter
          fun x => x ≤ E).card := by
      rw [hchar]
    _ = orderedEigenvalueThresholdCount (finWeightedCycleHermitian w) E := by
      symm
      simpa [finWeightedCycleHermitian] using
        orderedEigenvalueThresholdCount_eq_card_filter_roots
          (finWeightedCycleLaplacian w) (finWeightedCycleHermitian w).2 E

theorem leftWeights_canonicalInverseMassVector
    {n m : Nat} (omega : RandomEnsemble.SampleSpace) :
    leftWeights (canonicalInverseMassVector (n + m) omega) =
      canonicalInverseMassVector n omega := by
  rfl

theorem rightWeights_canonicalInverseMassVector
    {n m : Nat} (omega : RandomEnsemble.SampleSpace) :
    rightWeights (canonicalInverseMassVector (n + m) omega) =
      shiftedInverseMassVector n m omega := by
  funext i
  rfl

/-- Samplewise periodic count gluing for the canonical iid chain. -/
theorem canonicalPeriodicThresholdCount_gluing_upper
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (E : Real) (omega : RandomEnsemble.SampleSpace) :
    canonicalPeriodicThresholdCount (n + m) E omega ≤
      canonicalPeriodicThresholdCount n E omega +
        shiftedPeriodicThresholdCount n m E omega + 4 := by
  have h := splitFinWeightedCycle_thresholdCount_defect_le_four
    (canonicalInverseMassVector (n + m) omega) E
  rw [splitFinWeightedCycle_thresholdCount_eq_fin,
    leftWeights_canonicalInverseMassVector,
    rightWeights_canonicalInverseMassVector] at h
  change (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian (canonicalInverseMassVector (n + m) omega)) E : Real) ≤
    (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian (canonicalInverseMassVector n omega)) E : Real) +
    (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian (shiftedInverseMassVector n m omega)) E : Real) + 4
  exact_mod_cast h.1


/-- Integrating the samplewise four-boundary estimate and using shifted iid
invariance gives the expected-count gluing inequality. -/
theorem integral_canonicalPeriodicThresholdCount_gluing_upper
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)] (E : Real) :
    (∫ omega, canonicalPeriodicThresholdCount (n + m) E omega
        ∂(RandomEnsemble.canonicalLaw)) ≤
      (∫ omega, canonicalPeriodicThresholdCount n E omega
        ∂(RandomEnsemble.canonicalLaw)) +
      (∫ omega, canonicalPeriodicThresholdCount m E omega
        ∂(RandomEnsemble.canonicalLaw)) + 4 := by
  have hbig := integrable_canonicalPeriodicThresholdCount (n + m) E
  have hleft := integrable_canonicalPeriodicThresholdCount n E
  have hright := integrable_shiftedPeriodicThresholdCount n m E
  have hsum : Integrable
      (fun omega => canonicalPeriodicThresholdCount n E omega +
        shiftedPeriodicThresholdCount n m E omega + 4)
      RandomEnsemble.canonicalLaw :=
    (hleft.add hright).add (integrable_const 4)
  calc
    (∫ omega, canonicalPeriodicThresholdCount (n + m) E omega
        ∂(RandomEnsemble.canonicalLaw)) ≤
        ∫ omega, (canonicalPeriodicThresholdCount n E omega +
          shiftedPeriodicThresholdCount n m E omega + 4)
          ∂(RandomEnsemble.canonicalLaw) :=
      integral_mono hbig hsum
        (fun omega => canonicalPeriodicThresholdCount_gluing_upper E omega)
    _ = (∫ omega, canonicalPeriodicThresholdCount n E omega
          ∂(RandomEnsemble.canonicalLaw)) +
        (∫ omega, shiftedPeriodicThresholdCount n m E omega
          ∂(RandomEnsemble.canonicalLaw)) + 4 := by
      calc
        (∫ omega, canonicalPeriodicThresholdCount n E omega +
            shiftedPeriodicThresholdCount n m E omega + 4
            ∂(RandomEnsemble.canonicalLaw)) =
          (∫ omega, canonicalPeriodicThresholdCount n E omega +
            shiftedPeriodicThresholdCount n m E omega
            ∂(RandomEnsemble.canonicalLaw)) +
          (∫ _omega : RandomEnsemble.SampleSpace, (4 : Real)
            ∂(RandomEnsemble.canonicalLaw)) := by
              simpa only [Pi.add_apply] using
                (integral_add (hleft.add hright) (integrable_const (4 : Real)))
        _ = (∫ omega, canonicalPeriodicThresholdCount n E omega
              ∂(RandomEnsemble.canonicalLaw)) +
            (∫ omega, shiftedPeriodicThresholdCount n m E omega
              ∂(RandomEnsemble.canonicalLaw)) + 4 := by
          rw [integral_add hleft hright]
          simp
    _ = (∫ omega, canonicalPeriodicThresholdCount n E omega
          ∂(RandomEnsemble.canonicalLaw)) +
        (∫ omega, canonicalPeriodicThresholdCount m E omega
          ∂(RandomEnsemble.canonicalLaw)) + 4 := by
      rw [integral_shiftedPeriodicThresholdCount_eq]

/-- Expected unnormalised periodic threshold count, extended by zero at the
empty volume so that Fekete applies on all natural numbers. -/
def canonicalThresholdCountCenter (E : Real) : Nat → Real
  | 0 => 0
  | N + 1 => ∫ omega, canonicalPeriodicThresholdCount (N + 1) E omega
      ∂(RandomEnsemble.canonicalLaw)

theorem canonicalThresholdCountCenter_nonneg (E : Real) :
    ∀ N, 0 ≤ canonicalThresholdCountCenter E N := by
  intro N
  cases N with
  | zero => simp [canonicalThresholdCountCenter]
  | succ N =>
      rw [canonicalThresholdCountCenter]
      exact integral_nonneg fun omega => Nat.cast_nonneg _

/-- The canonical expected count is subadditive up to exactly the four
boundary rank-one terms. -/
theorem canonicalThresholdCountCenter_almostSubadditive (E : Real) :
    AlmostSubadditive (canonicalThresholdCountCenter E) 4 := by
  intro n m
  cases n with
  | zero => simp [canonicalThresholdCountCenter]
  | succ n =>
      cases m with
      | zero => simp [canonicalThresholdCountCenter]
      | succ m =>
          simp only [canonicalThresholdCountCenter]
          have h := integral_canonicalPeriodicThresholdCount_gluing_upper
            (n := n + 1) (m := m + 1) E
          convert h using 1
          congr 1

/-- For every fixed threshold there is a finite deterministic limit of the
expected periodic count per site. -/
theorem exists_canonicalThresholdCountCenter_limit (E : Real) :
    ∃ L : Real, Tendsto
      (fun N : Nat => canonicalThresholdCountCenter E N / (N : Real))
      atTop (nhds L) := by
  exact exists_tendsto_div_natCast (by norm_num)
    (canonicalThresholdCountCenter_nonneg E)
    (canonicalThresholdCountCenter_almostSubadditive E)


/-- On every positive volume, the Fekete-normalized edge-space center is
exactly the expectation of the normalized physical harmonic count. -/
theorem canonicalThresholdCountCenter_succ_div_eq_expectation
    (E : Real) (n : Nat) :
    canonicalThresholdCountCenter E (n + 1) / ((n + 1 : Nat) : Real) =
      ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
        ∂(RandomEnsemble.canonicalLaw) := by
  rw [canonicalThresholdCountCenter]
  have heq :
      (∫ omega, canonicalPeriodicThresholdCount (n + 1) E omega
          ∂(RandomEnsemble.canonicalLaw)) =
        ∫ omega, ((n + 1 : Nat) : Real) *
          canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
          ∂(RandomEnsemble.canonicalLaw) := by
    apply integral_congr_ae
    exact ae_of_all _ fun omega =>
      canonicalPeriodicThresholdCount_eq_mul_normalized (n + 1) E omega
  rw [heq, integral_const_mul]
  have hn : (((n + 1 : Nat) : Real)) ≠ 0 := by positivity
  field_simp

set_option maxHeartbeats 800000 in
-- The dependent positive-volume integral equality exceeds the default elaboration budget.
/-- The finite-volume physical expectations converge to the same scalar
Fekete limit along all positive volumes. -/
theorem exists_canonicalNormalizedExpectation_limit (E : Real) :
    ∃ L : Real, Tendsto
      (fun n : Nat =>
        ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
          ∂(RandomEnsemble.canonicalLaw)) atTop (nhds L) := by
  obtain ⟨L, hL⟩ := exists_canonicalThresholdCountCenter_limit E
  refine ⟨L, ?_⟩
  have hshift : Tendsto (fun n : Nat => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have h := hL.comp hshift
  refine h.congr' (Eventually.of_forall fun n => ?_)
  exact canonicalThresholdCountCenter_succ_div_eq_expectation E n


/-- At every fixed threshold, the canonical normalized physical harmonic
count converges in probability to a non-random scalar IDS value.  The proof
uses no spectral simplicity and retains eigenvalues equal to the threshold. -/
theorem exists_canonicalScalarIDS_probabilityLimit (E : Real) :
    ∃ L : Real,
      Tendsto
        (fun n : Nat =>
          ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
            ∂(RandomEnsemble.canonicalLaw)) atTop (nhds L) ∧
      ∀ epsilon : Real, 0 < epsilon →
        Tendsto
          (fun n : Nat => RandomEnsemble.canonicalLaw.real
            {omega | epsilon ≤
              |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L|})
          atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := exists_canonicalNormalizedExpectation_limit E
  refine ⟨L, hL, ?_⟩
  intro epsilon hepsilon
  let a : Nat → Real := fun n =>
    ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
      ∂(RandomEnsemble.canonicalLaw)
  have ha : Tendsto a atTop (nhds L) := hL
  have hconst : Tendsto (fun _ : Nat => L) atTop (nhds L) :=
    tendsto_const_nhds
  have habs : Tendsto (fun n => |a n - L|) atTop (nhds 0) := by
    simpa using (ha.sub hconst).abs
  have hcenterClose : ∀ᶠ n in atTop, |a n - L| < epsilon / 2 :=
    habs.eventually (Iio_mem_nhds (half_pos hepsilon))
  have hle : ∀ᶠ n in atTop,
      RandomEnsemble.canonicalLaw.real
          {omega | epsilon ≤
            |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L|} ≤
        RandomEnsemble.canonicalLaw.real
          {omega | epsilon / 2 ≤
            |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n|} := by
    filter_upwards [hcenterClose] with n hn
    refine measureReal_mono ?_ (by finiteness)
    intro omega homega
    change epsilon ≤
      |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L| at homega
    change epsilon / 2 ≤
      |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n|
    have htriangle :
        |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L| ≤
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n| +
            |a n - L| := by
      calc
        |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L| =
            |(canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n) +
              (a n - L)| := by ring_nf
        _ ≤ |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n| +
              |a n - L| := abs_add_le _ _
    linarith
  apply squeeze_zero'
    (Eventually.of_forall fun _ => measureReal_nonneg) hle
  simpa [a] using
    canonicalNormalizedHarmonicThresholdCount_deviationProbability_tendsto_zero
      E (half_pos hepsilon)


/-- Quantitative form: after the deterministic center enters the half-error
window, the tail around the scalar IDS limit retains the McDiarmid
exponential rate. -/
theorem exists_canonicalScalarIDS_eventual_exponentialTail (E : Real) :
    ∃ L : Real,
      Tendsto
        (fun n : Nat =>
          ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
            ∂(RandomEnsemble.canonicalLaw)) atTop (nhds L) ∧
      ∀ epsilon : Real, 0 < epsilon → ∀ᶠ n : Nat in atTop,
        RandomEnsemble.canonicalLaw.real
            {omega | epsilon ≤
              |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L|} ≤
          2 * Real.exp
            (-2 * ((n + 1 : Nat) : Real) * (epsilon / 2) ^ 2) := by
  obtain ⟨L, hL⟩ := exists_canonicalNormalizedExpectation_limit E
  refine ⟨L, hL, ?_⟩
  intro epsilon hepsilon
  let a : Nat → Real := fun n =>
    ∫ omega, canonicalNormalizedHarmonicThresholdCount (n + 1) E omega
      ∂(RandomEnsemble.canonicalLaw)
  have ha : Tendsto a atTop (nhds L) := hL
  have hconst : Tendsto (fun _ : Nat => L) atTop (nhds L) :=
    tendsto_const_nhds
  have habs : Tendsto (fun n => |a n - L|) atTop (nhds 0) := by
    simpa using (ha.sub hconst).abs
  have hcenterClose : ∀ᶠ n in atTop, |a n - L| < epsilon / 2 :=
    habs.eventually (Iio_mem_nhds (half_pos hepsilon))
  filter_upwards [hcenterClose] with n hn
  calc
    RandomEnsemble.canonicalLaw.real
        {omega | epsilon ≤
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L|} ≤
      RandomEnsemble.canonicalLaw.real
        {omega | epsilon / 2 ≤
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n|} := by
      refine measureReal_mono ?_ (by finiteness)
      intro omega homega
      change epsilon ≤
        |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L| at homega
      change epsilon / 2 ≤
        |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n|
      have htriangle :
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L| ≤
            |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n| +
              |a n - L| := by
        calc
          |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - L| =
              |(canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n) +
                (a n - L)| := by ring_nf
          _ ≤ |canonicalNormalizedHarmonicThresholdCount (n + 1) E omega - a n| +
                |a n - L| := abs_add_le _ _
      linarith
    _ ≤ 2 * Real.exp
          (-2 * ((n + 1 : Nat) : Real) * (epsilon / 2) ^ 2) := by
      simpa [a] using
        canonicalNormalizedHarmonicThresholdCount_mcDiarmid_twoSided
          (n + 1) E (half_pos hepsilon).le

end

end ArchonPhysics.CanonicalScalarIDSCenterLimit
