import ArchonPhysics.CanonicalThresholdCountConcentrationInterface
import ArchonPhysics.FiniteProductBoundedDifferences

/-!
# McDiarmid concentration for the canonical fixed-volume threshold count

This module applies the finite-product bounded-differences theorem to the
first `N` frozen iid mass coordinates.  The normalized physical harmonic
threshold count has coordinate sensitivity `1 / N`, hence centered
sub-Gaussian parameter `1 / (4N)` and upper tail
`exp (-2 * N * epsilon^2)`.

The result is finite-volume probability concentration only.  It assumes no
simple spectrum and makes no localization, density-of-states, or
thermalization claim.
-/

namespace ArchonPhysics.CanonicalThresholdCountMcDiarmid

open ArchonPhysics
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.FiniteProductBoundedDifferences
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- Per-coordinate Lipschitz constant for the normalized count. -/
def canonicalCoordinateBound (N : Nat) : NNReal :=
  1 / (N : NNReal)

/-- The McDiarmid sub-Gaussian parameter after summing `N` coordinate
contributions. -/
def canonicalMcDiarmidParameter (N : Nat) : NNReal :=
  1 / (4 * (N : NNReal))

/-- Interpret a `Fin N` vector as a periodic-site vector using the canonical
least-residue representative. -/
def siteVectorOfFin {N : Nat} [NeZero N]
    (x : Fin N -> Real) : Lattice.Site N -> Real :=
  fun i => x ⟨i.val, i.val_lt⟩

/-- The clipped normalized count, reindexed by `Fin N`. -/
def finNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real) (x : Fin N -> Real) : Real :=
  clippedNormalizedHarmonicThresholdCount N E (siteVectorOfFin x)

/-- The reindexing from `Fin N` vectors to site vectors is measurable. -/
theorem measurable_siteVectorOfFin (N : Nat) [NeZero N] :
    Measurable (siteVectorOfFin (N := N)) := by
  exact measurable_pi_lambda _ fun i =>
    measurable_pi_apply (⟨i.val, i.val_lt⟩ : Fin N)

/-- The finite-coordinate observable is measurable. -/
theorem measurable_finNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real) :
    Measurable (finNormalizedHarmonicThresholdCount N E) :=
  (measurable_clippedNormalizedHarmonicThresholdCount N E).comp
    (measurable_siteVectorOfFin N)

/-- Every total finite-coordinate count lies in `[0,1]`. -/
theorem finNormalizedHarmonicThresholdCount_mem_Icc
    (N : Nat) [NeZero N] (E : Real) (x : Fin N -> Real) :
    finNormalizedHarmonicThresholdCount N E x ∈ Set.Icc 0 1 := by
  unfold finNormalizedHarmonicThresholdCount
  unfold clippedNormalizedHarmonicThresholdCount
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcount :
      orderedEigenvalueThresholdCount
          (harmonicHermitian
            (clippedPositiveMassConfig (siteVectorOfFin x))) E <= N := by
    unfold orderedEigenvalueThresholdCount orderedEigenvalueThresholdIndices
    simpa [Lattice.Site] using
      (Finset.card_filter_le
        (Finset.univ : Finset
          (Fin (Fintype.card (Lattice.Site N))))
        (fun k => orderedEigenvalue
          (harmonicHermitian
            (clippedPositiveMassConfig (siteVectorOfFin x))) k <= E))
  constructor
  · positivity
  · rw [div_le_iff₀ hN]
    norm_num
    exact_mod_cast hcount

/-- Reindexing preserves the sharp `1 / N` coordinate sensitivity. -/
theorem finNormalizedHarmonicThresholdCount_hasBoundedDifferences
    (N : Nat) [NeZero N] (E : Real) :
    HasFinBoundedDifferences
      (finNormalizedHarmonicThresholdCount N E)
      (fun _ : Fin N => canonicalCoordinateBound N) := by
  intro x y k hoff
  apply clippedNormalizedHarmonicThresholdCount_single_coordinate E
    (siteVectorOfFin x) (siteVectorOfFin y) (k.val : ZMod N)
  intro j hj
  apply hoff ⟨j.val, j.val_lt⟩
  intro heq
  apply hj
  apply ZMod.val_injective N
  rw [ZMod.val_natCast_of_lt k.isLt]
  exact congrArg Fin.val heq

/-- The constant-coordinate variance proxy is exactly `1 / (4N)`. -/
theorem varianceProxy_canonicalCoordinateBound
    (N : Nat) [NeZero N] :
    varianceProxy (fun _ : Fin N => canonicalCoordinateBound N) =
      canonicalMcDiarmidParameter N := by
  apply NNReal.eq
  simp [varianceProxy, canonicalCoordinateBound,
    canonicalMcDiarmidParameter, Finset.sum_const, nsmul_eq_mul]
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  field_simp
  norm_num

/-- The first `N` positive canonical mass representatives, indexed by
`Fin N`. -/
def canonicalFinMassVector (N : Nat)
    (omega : RandomEnsemble.SampleSpace) : Fin N -> Real :=
  fun i => RandomEnsemble.massAt i.val omega

/-- The canonical finite mass vector is measurable. -/
theorem measurable_canonicalFinMassVector (N : Nat) :
    Measurable (canonicalFinMassVector N) := by
  exact measurable_pi_lambda _ fun i =>
    RandomEnsemble.measurable_massAt i.val

/-- Its joint law is the genuine finite iid product law. -/
theorem canonicalFinMassVector_hasLaw (N : Nat) :
    HasLaw (canonicalFinMassVector N)
      (Measure.pi fun _ : Fin N => RandomEnsemble.massCoordinateLaw)
      RandomEnsemble.canonicalLaw := by
  exact (RandomEnsemble.massCoordinates_iIndep.precomp Fin.val_injective).hasLaw_pi
    (fun i => RandomEnsemble.massAt_hasLaw i.val)

/-- On a canonical sample, the `Fin N` observable is exactly the established
fixed-volume site observable. -/
theorem finNormalizedHarmonicThresholdCount_canonicalFinMassVector
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    finNormalizedHarmonicThresholdCount N E
        (canonicalFinMassVector N omega) =
      canonicalNormalizedHarmonicThresholdCount N E omega := by
  rfl

/-- Product-space McDiarmid MGF certificate before transport to the canonical
sample space. -/
theorem finNormalizedHarmonicThresholdCount_hasSubgaussianMGF
    (N : Nat) [NeZero N] (E : Real) :
    HasSubgaussianMGF
      (fun x => finNormalizedHarmonicThresholdCount N E x -
        (∫ y, finNormalizedHarmonicThresholdCount N E y
          ∂(Measure.pi fun _ : Fin N => RandomEnsemble.massCoordinateLaw)))
      (canonicalMcDiarmidParameter N)
      (Measure.pi fun _ : Fin N => RandomEnsemble.massCoordinateLaw) := by
  have h := hasSubgaussianMGF_finitePi_of_boundedDifferences
    RandomEnsemble.massCoordinateLaw N
    (finNormalizedHarmonicThresholdCount N E)
    (fun _ : Fin N => canonicalCoordinateBound N)
    (measurable_finNormalizedHarmonicThresholdCount N E)
    (finNormalizedHarmonicThresholdCount_mem_Icc N E)
    (finNormalizedHarmonicThresholdCount_hasBoundedDifferences N E)
  rw [varianceProxy_canonicalCoordinateBound N] at h
  exact h

/-- Canonical fixed-volume normalized counts have the sharp bounded-
differences parameter `1 / (4N)`. -/
theorem canonicalNormalizedHarmonicThresholdCount_hasMcDiarmidMGF
    (N : Nat) [NeZero N] (E : Real) :
    HasSubgaussianMGF
      (fun omega => canonicalNormalizedHarmonicThresholdCount N E omega -
        (∫ eta, canonicalNormalizedHarmonicThresholdCount N E eta
          ∂(RandomEnsemble.canonicalLaw)))
      (canonicalMcDiarmidParameter N) RandomEnsemble.canonicalLaw := by
  let productLaw : Measure (Fin N -> Real) :=
    Measure.pi fun _ : Fin N => RandomEnsemble.massCoordinateLaw
  have hlaw := canonicalFinMassVector_hasLaw N
  have hmean :
      (∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
          ∂(RandomEnsemble.canonicalLaw)) =
        ∫ x, finNormalizedHarmonicThresholdCount N E x ∂productLaw := by
    rw [show canonicalNormalizedHarmonicThresholdCount N E =
        finNormalizedHarmonicThresholdCount N E ∘ canonicalFinMassVector N by
      funext omega
      exact (finNormalizedHarmonicThresholdCount_canonicalFinMassVector
        N E omega).symm]
    exact hlaw.integral_comp
      (measurable_finNormalizedHarmonicThresholdCount N E).aestronglyMeasurable
  have hproductMap : HasSubgaussianMGF
      (fun x => finNormalizedHarmonicThresholdCount N E x -
        (∫ y, finNormalizedHarmonicThresholdCount N E y ∂productLaw))
      (canonicalMcDiarmidParameter N)
      (RandomEnsemble.canonicalLaw.map (canonicalFinMassVector N)) := by
    rw [hlaw.map_eq]
    exact finNormalizedHarmonicThresholdCount_hasSubgaussianMGF N E
  have htransport := HasSubgaussianMGF.of_map
    (measurable_canonicalFinMassVector N).aemeasurable hproductMap
  simpa [Function.comp_def, hmean,
    finNormalizedHarmonicThresholdCount_canonicalFinMassVector] using htransport

/-- Sharp one-sided McDiarmid concentration for the canonical normalized
threshold count. -/
theorem canonicalNormalizedHarmonicThresholdCount_mcDiarmid_upperTail
    (N : Nat) [NeZero N] (E : Real) {epsilon : Real}
    (hepsilon : 0 <= epsilon) :
    RandomEnsemble.canonicalLaw.real
        {omega | epsilon <=
          canonicalNormalizedHarmonicThresholdCount N E omega -
            (∫ eta, canonicalNormalizedHarmonicThresholdCount N E eta
              ∂(RandomEnsemble.canonicalLaw))} <=
      Real.exp (-2 * (N : Real) * epsilon ^ 2) := by
  have htail :=
    (canonicalNormalizedHarmonicThresholdCount_hasMcDiarmidMGF N E).measure_ge_le
      hepsilon
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  convert htail using 1
  congr 1
  simp only [canonicalMcDiarmidParameter, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
  field_simp
  ring

end

end ArchonPhysics.CanonicalThresholdCountMcDiarmid
