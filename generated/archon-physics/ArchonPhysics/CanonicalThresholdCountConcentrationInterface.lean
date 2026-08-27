import ArchonPhysics.MultiMassThresholdCountSensitivity
import ArchonPhysics.OrderedSpectrumContinuity
import Mathlib.Probability.Moments.SubGaussian

/-!
# Concentration-ready interface for fixed-volume harmonic threshold counts

This module packages the normalized physical harmonic threshold count as a
measurable function of finitely many independent mass coordinates.  The
function changes by at most `1 / N` when one coordinate is replaced, and by
at most `S.card / N` when replacements are confined to a site finset `S`.

Mathlib currently supplies Hoeffding's lemma for one bounded random variable
and Azuma--Hoeffding from conditional sub-Gaussian martingale increments, but
no theorem converting a coordinatewise bounded-differences hypothesis into
those conditional increment bounds.  Accordingly, this module proves the
complete measurable/Hamming--Lipschitz input interface.  It also records the
weaker, volume-independent concentration bound obtained directly from the
fact that the normalized count lies in `[0,1]`.

No spectral simplicity, localization, thermodynamic limit, or thermalization
claim is made.
-/

namespace ArchonPhysics.CanonicalThresholdCountConcentrationInterface

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MultiMassThresholdCountSensitivity
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter Function MeasureTheory ProbabilityTheory Set Topology

noncomputable section

/-- Standard coordinatewise bounded-differences predicate. -/
def HasCoordinateBoundedDifferences
    {index value : Type*} (f : (index -> value) -> Real)
    (c : index -> Real) : Prop :=
  forall x y i, (forall j, j ≠ i -> x j = y j) ->
    |f x - f y| <= c i

/-- Total positive-mass configuration obtained by clipping every coordinate
to the frozen support. -/
def clippedPositiveMassConfig {N : Nat}
    (x : Lattice.Site N -> Real) : Lattice.PositiveMassConfig N where
  mass i := RandomEnsemble.clippedMass (x i)
  mass_pos i := RandomEnsemble.clippedMass_pos (x i)

/-- The normalized physical harmonic sublevel count as a total function of a
finite real coordinate vector. -/
def clippedNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real)
    (x : Lattice.Site N -> Real) : Real :=
  (orderedEigenvalueThresholdCount
      (harmonicHermitian (clippedPositiveMassConfig x)) E : Real) /
    (N : Real)

/-- Indicator-average representation of the normalized threshold count. -/
theorem clippedNormalizedHarmonicThresholdCount_eq_indicatorAverage
    (N : Nat) [NeZero N] (E : Real)
    (x : Lattice.Site N -> Real) :
    clippedNormalizedHarmonicThresholdCount N E x =
      (∑ k : Fin (Fintype.card (Lattice.Site N)),
        if orderedEigenvalue
            (harmonicHermitian (clippedPositiveMassConfig x)) k <= E
          then (1 : Real) else 0) / (N : Real) := by
  unfold clippedNormalizedHarmonicThresholdCount
  unfold orderedEigenvalueThresholdCount orderedEigenvalueThresholdIndices
  rw [Finset.natCast_card_filter]

/-- The finite-coordinate normalized threshold-count function is measurable.
This is the measurability input required by product-measure concentration
theorems. -/
theorem measurable_clippedNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real) :
    Measurable (clippedNormalizedHarmonicThresholdCount N E) := by
  have hmass : forall i : Lattice.Site N,
      Measurable fun x : Lattice.Site N -> Real =>
        (clippedPositiveMassConfig x).mass i := by
    intro i
    exact RandomEnsemble.measurable_clippedMass.comp
      (measurable_pi_apply i)
  have hsample : Measurable fun x : Lattice.Site N -> Real =>
      harmonicHermitian (clippedPositiveMassConfig x) := by
    apply Measurable.subtype_mk
    exact
      ArchonPhysics.MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
        (fun x : Lattice.Site N -> Real => clippedPositiveMassConfig x) hmass
  have heigen (k : Fin (Fintype.card (Lattice.Site N))) :
      Measurable fun x : Lattice.Site N -> Real =>
        orderedEigenvalue
          (harmonicHermitian (clippedPositiveMassConfig x)) k :=
    (continuous_orderedEigenvalue k).measurable.comp hsample
  have hindicator (k : Fin (Fintype.card (Lattice.Site N))) :
      Measurable fun x : Lattice.Site N -> Real =>
        if orderedEigenvalue
            (harmonicHermitian (clippedPositiveMassConfig x)) k <= E
          then (1 : Real) else 0 :=
    Measurable.ite (measurableSet_le (heigen k) measurable_const)
      measurable_const measurable_const
  have hsum : Measurable fun x : Lattice.Site N -> Real =>
      ∑ k : Fin (Fintype.card (Lattice.Site N)),
        if orderedEigenvalue
            (harmonicHermitian (clippedPositiveMassConfig x)) k <= E
          then (1 : Real) else 0 :=
    Finset.measurable_fun_sum Finset.univ fun k _ => hindicator k
  rw [show clippedNormalizedHarmonicThresholdCount N E =
      fun x =>
        (∑ k : Fin (Fintype.card (Lattice.Site N)),
          if orderedEigenvalue
              (harmonicHermitian (clippedPositiveMassConfig x)) k <= E
            then (1 : Real) else 0) / (N : Real) by
    funext x
    exact clippedNormalizedHarmonicThresholdCount_eq_indicatorAverage N E x]
  exact hsum.div_const (N : Real)

/-- Replacements confined to `S` change the normalized count by at most
`S.card / N`. -/
theorem clippedNormalizedHarmonicThresholdCount_finset_sensitivity
    {N : Nat} [NeZero N] (E : Real)
    (x y : Lattice.Site N -> Real)
    (S : Finset (Lattice.Site N))
    (hoff : forall i, i ∉ S -> x i = y i) :
    |clippedNormalizedHarmonicThresholdCount N E x -
        clippedNormalizedHarmonicThresholdCount N E y| <=
      (S.card : Real) / (N : Real) := by
  apply harmonic_normalizedThresholdCount_finset_sensitivity
    (clippedPositiveMassConfig x) (clippedPositiveMassConfig y) S
  intro i hi
  simp only [clippedPositiveMassConfig]
  rw [hoff i hi]

/-- In particular, changing one coordinate changes the normalized count by
at most `1 / N`. -/
theorem clippedNormalizedHarmonicThresholdCount_single_coordinate
    {N : Nat} [NeZero N] (E : Real)
    (x y : Lattice.Site N -> Real) (i : Lattice.Site N)
    (hoff : forall j, j ≠ i -> x j = y j) :
    |clippedNormalizedHarmonicThresholdCount N E x -
        clippedNormalizedHarmonicThresholdCount N E y| <=
      (1 : Real) / (N : Real) := by
  simpa using clippedNormalizedHarmonicThresholdCount_finset_sensitivity
    E x y {i} (fun j hj => hoff j (by simpa using hj))

/-- The clipped finite-coordinate observable has coordinatewise bounded
differences with constant `1 / N` at every site. -/
theorem clippedNormalizedHarmonicThresholdCount_hasBoundedDifferences
    (N : Nat) [NeZero N] (E : Real) :
    HasCoordinateBoundedDifferences
      (clippedNormalizedHarmonicThresholdCount N E)
      (fun _ : Lattice.Site N => (1 : Real) / (N : Real)) := by
  intro x y i hoff
  exact clippedNormalizedHarmonicThresholdCount_single_coordinate E x y i hoff

/-- Fixed finite vector of canonical positive mass coordinates. -/
def canonicalFixedMassVector (N : Nat) [NeZero N]
    (omega : RandomEnsemble.SampleSpace) : Lattice.Site N -> Real :=
  fun i => RandomEnsemble.massAt i.val omega

/-- The canonical finite mass vector is measurable. -/
theorem measurable_canonicalFixedMassVector
    (N : Nat) [NeZero N] :
    Measurable (canonicalFixedMassVector N) := by
  exact measurable_pi_lambda _ fun i =>
    RandomEnsemble.measurable_massAt i.val

/-- Its coordinates are mutually independent under the canonical law. -/
theorem canonicalFixedMassVector_iIndep
    (N : Nat) [NeZero N] :
    iIndepFun (fun (i : Lattice.Site N) omega =>
      canonicalFixedMassVector N omega i)
      RandomEnsemble.canonicalLaw := by
  simpa [canonicalFixedMassVector, IIDMassPhaseEnsemble.restrictMass,
    canonicalIIDMassPhaseEnsemble] using
    (IIDMassPhaseEnsemble.restrictMass_iIndep
      canonicalIIDMassPhaseEnsemble (N := N))

/-- Every coordinate of the canonical finite vector has the frozen one-site
mass law. -/
theorem canonicalFixedMassVector_hasLaw
    (N : Nat) [NeZero N] (i : Lattice.Site N) :
    HasLaw (fun omega => canonicalFixedMassVector N omega i)
      RandomEnsemble.massCoordinateLaw RandomEnsemble.canonicalLaw := by
  simpa [canonicalFixedMassVector, IIDMassPhaseEnsemble.restrictMass,
    canonicalIIDMassPhaseEnsemble] using
    (IIDMassPhaseEnsemble.restrictMass_hasLaw
      canonicalIIDMassPhaseEnsemble i)

/-- Clipping the already-supported canonical vector recovers the existing
finite positive-mass restriction exactly. -/
theorem clippedPositiveMassConfig_canonicalFixedMassVector
    (N : Nat) [NeZero N] (omega : RandomEnsemble.SampleSpace) :
    clippedPositiveMassConfig (canonicalFixedMassVector N omega) =
      canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := N) omega := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext i
  exact RandomEnsemble.clippedMass_eq_self
    (RandomEnsemble.massAt_mem_support i.val omega)

/-- Canonical fixed-volume normalized physical harmonic threshold count. -/
def canonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) : Real :=
  clippedNormalizedHarmonicThresholdCount N E
    (canonicalFixedMassVector N omega)

/-- Formula in terms of the established positive-mass restriction. -/
theorem canonicalNormalizedHarmonicThresholdCount_eq
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalNormalizedHarmonicThresholdCount N E omega =
      (orderedEigenvalueThresholdCount
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)) E : Real) / (N : Real) := by
  rw [canonicalNormalizedHarmonicThresholdCount,
    clippedNormalizedHarmonicThresholdCount,
    clippedPositiveMassConfig_canonicalFixedMassVector]

/-- The canonical normalized threshold count is measurable. -/
theorem measurable_canonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (E : Real) :
    Measurable (canonicalNormalizedHarmonicThresholdCount N E) :=
  (measurable_clippedNormalizedHarmonicThresholdCount N E).comp
    (measurable_canonicalFixedMassVector N)

/-- The normalized count always belongs to `[0,1]`. -/
theorem canonicalNormalizedHarmonicThresholdCount_mem_Icc
    (N : Nat) [NeZero N] (E : Real)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalNormalizedHarmonicThresholdCount N E omega ∈ Set.Icc 0 1 := by
  rw [canonicalNormalizedHarmonicThresholdCount_eq]
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcount :
      orderedEigenvalueThresholdCount
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)) E <= N := by
    unfold orderedEigenvalueThresholdCount orderedEigenvalueThresholdIndices
    simpa [Lattice.Site] using
      (Finset.card_filter_le
        (Finset.univ : Finset
          (Fin (Fintype.card (Lattice.Site N))))
        (fun k => orderedEigenvalue
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)) k <= E))
  constructor
  · positivity
  · rw [div_le_iff₀ hN]
    norm_num
    exact_mod_cast hcount

/-- Volume-independent Hoeffding certificate obtained only from the range
`[0,1]`.  The sharper parameter `1/(4N)` would require the missing
bounded-differences-to-conditional-sub-Gaussian bridge. -/
theorem canonicalNormalizedHarmonicThresholdCount_hasSubgaussianMGF
    (N : Nat) [NeZero N] (E : Real) :
    HasSubgaussianMGF
      (fun omega => canonicalNormalizedHarmonicThresholdCount N E omega -
        (∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
          ∂(RandomEnsemble.canonicalLaw)))
      (1 / 4 : NNReal) RandomEnsemble.canonicalLaw := by
  convert hasSubgaussianMGF_of_mem_Icc
    (X := canonicalNormalizedHarmonicThresholdCount N E)
    (μ := RandomEnsemble.canonicalLaw)
    (measurable_canonicalNormalizedHarmonicThresholdCount N E).aemeasurable
    (ae_of_all _ fun omega =>
      canonicalNormalizedHarmonicThresholdCount_mem_Icc N E omega) using 1
  apply NNReal.eq
  norm_num

/-- Grounded one-sided concentration around the expectation.  This fallback
bound is valid for every fixed `N` but does not improve with volume. -/
theorem canonicalNormalizedHarmonicThresholdCount_upperTail
    (N : Nat) [NeZero N] (E : Real) {epsilon : Real}
    (hepsilon : 0 <= epsilon) :
    RandomEnsemble.canonicalLaw.real
        {omega | epsilon <=
          canonicalNormalizedHarmonicThresholdCount N E omega -
            (∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
              ∂(RandomEnsemble.canonicalLaw))} <=
      Real.exp (-2 * epsilon ^ 2) := by
  have htail :=
    (canonicalNormalizedHarmonicThresholdCount_hasSubgaussianMGF N E).measure_ge_le
      hepsilon
  convert htail using 1
  congr 1
  norm_num
  ring
end

end ArchonPhysics.CanonicalThresholdCountConcentrationInterface
