import ArchonPhysics.ActualEightSiteFullIIDRegularPointLocalSmallBallUpper
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Compact good levels for the actual full-eight iid small-ball estimate

The pointwise inverse-function theorem gives a linear mismatch small-ball
estimate around every point of the actual selected-Jacobian regular locus.
This file turns that pointwise statement into a finite atlas on a compact
quantitative good level.

The good level is cut out by a positive distance from the complement of the
regular locus, inside the physical mass support cube.  Compactness supplies a
finite subcover, and the local constants add to one finite coefficient
`C_n`.  The source mass outside the good level is retained exactly as
`fullEightSelectedJacobianBadMass n`.  In particular, this file does not
assert that the regular locus has full iid measure or that the bad mass tends
to zero.
-/

open scoped ENNReal Matrix Topology ContDiff BigOperators

namespace ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
open ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDRegularPointLocalSmallBallUpper
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- Distance to failure of one of the transparent full-eight regularity
conditions. -/
def fullEightSelectedJacobianRegularMargin (x : EightMassVector) : Real :=
  Metric.infDist x fullEightSelectedJacobianRegularSetᶜ

/-- The positive cutoff used at quantitative level `n`. -/
def fullEightSelectedJacobianGoodThreshold (n : Nat) : Real :=
  (((n + 1 : Nat) : Real))⁻¹

/-- A compact quantitative good level.  The single distance condition keeps
the point away from every failure mode encoded in the transparent regular
set: support boundary, spectral collision, loss of positivity, or vanishing
selected partial Jacobian. -/
def fullEightSelectedJacobianGoodLevel (n : Nat) : Set EightMassVector :=
  fullEightMassSupportCube ∩
    {x | fullEightSelectedJacobianGoodThreshold n ≤
      fullEightSelectedJacobianRegularMargin x}

/-- The same compact good level in the selected-first coordinates used by the
augmented mismatch chart. -/
def selectedFirstFullEightJacobianGoodLevel (n : Nat) :
    Set (MassTriple × EightMassEnvironment) :=
  selectedFirstEightMassEquiv '' fullEightSelectedJacobianGoodLevel n

/-- Exact iid mass discarded at level `n`.  No decay of this quantity is
claimed here. -/
def fullEightSelectedJacobianBadMass (n : Nat) : ENNReal :=
  (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
    (selectedFirstFullEightJacobianGoodLevel n)ᶜ

theorem fullEightSelectedJacobianGoodThreshold_pos (n : Nat) :
    0 < fullEightSelectedJacobianGoodThreshold n := by
  unfold fullEightSelectedJacobianGoodThreshold
  positivity

theorem isCompact_fullEightMassSupportCube :
    IsCompact fullEightMassSupportCube := by
  unfold fullEightMassSupportCube massSupport
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem isCompact_fullEightSelectedJacobianGoodLevel (n : Nat) :
    IsCompact (fullEightSelectedJacobianGoodLevel n) := by
  unfold fullEightSelectedJacobianGoodLevel
  exact isCompact_fullEightMassSupportCube.inter_right
    (isClosed_le continuous_const
      (Metric.continuous_infDist_pt
        fullEightSelectedJacobianRegularSetᶜ))

theorem fullEightSelectedJacobianGoodLevel_subset_regular (n : Nat) :
    fullEightSelectedJacobianGoodLevel n ⊆
      fullEightSelectedJacobianRegularSet := by
  intro x hx
  by_contra hregular
  have hxComplement : x ∈ fullEightSelectedJacobianRegularSetᶜ := hregular
  have hzero : fullEightSelectedJacobianRegularMargin x = 0 := by
    exact Metric.infDist_zero_of_mem hxComplement
  have hpositive := fullEightSelectedJacobianGoodThreshold_pos n
  have hmargin : fullEightSelectedJacobianGoodThreshold n ≤
      fullEightSelectedJacobianRegularMargin x := hx.2
  rw [hzero] at hmargin
  exact (not_le_of_gt hpositive) hmargin

theorem isCompact_selectedFirstFullEightJacobianGoodLevel (n : Nat) :
    IsCompact (selectedFirstFullEightJacobianGoodLevel n) := by
  exact (isCompact_fullEightSelectedJacobianGoodLevel n).image
    selectedFirstEightMassEquiv.continuous

theorem measurableSet_selectedFirstFullEightJacobianGoodLevel (n : Nat) :
    MeasurableSet (selectedFirstFullEightJacobianGoodLevel n) :=
  (isCompact_selectedFirstFullEightJacobianGoodLevel n).isClosed.measurableSet

/-- The product-volume chart bound at a regular point transfers to the actual
selected-first eightfold iid source.  Its local coefficient is finite; this
uses only the already-proved global density domination of `finiteMassLaw 8`.
-/
theorem exists_actualEightSite_local_fullIID_linearSmallBallUpper_of_regular
    {x : EightMassVector} (hx : x ∈ fullEightSelectedJacobianRegularSet) :
    ∃ patch : Set (MassTriple × EightMassEnvironment),
      ∃ coefficient : ENNReal,
        IsOpen patch ∧ selectedFirstEightMassEquiv x ∈ patch ∧
        coefficient ≠ (∞ : ENNReal) ∧
        ∀ delta : Real, 0 ≤ delta →
          (Measure.map selectedFirstEightMassEquiv
              (finiteMassLaw 8)).restrict patch
                {point |
                  |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
            coefficient * ENNReal.ofReal (2 * delta) := by
  obtain ⟨patch, detLower, ceiling, environmentPatch,
      hpatchOpen, hpointPatch, _hpatchSupport, hdetLower, _hceiling,
      _henvironmentMeasurable, henvironmentFinite, hvolume⟩ :=
    exists_actualEightSite_local_productVolume_linearSmallBallUpper_of_regular
      hx
  obtain ⟨densityCeiling, hdensityFinite, hdensity⟩ :=
    exists_selectedFirstFiniteMassLaw_le_smul_productVolume
  let source : Measure (MassTriple × EightMassEnvironment) :=
    Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8)
  let productVolume : Measure (MassTriple × EightMassEnvironment) :=
    (volume : Measure MassTriple).prod
      (volume : Measure EightMassEnvironment)
  have hsourcePatch : source.restrict patch ≤
      densityCeiling • productVolume.restrict patch := by
    calc
      source.restrict patch ≤
          (densityCeiling • productVolume).restrict patch :=
        Measure.restrict_mono_measure hdensity patch
      _ = densityCeiling • productVolume.restrict patch := by
        rw [Measure.restrict_smul]
  have htransferred := localSmallBallUpper_of_restrictedMeasure_le
    source densityCeiling patch hsourcePatch detLower ceiling
      environmentPatch (by simpa [productVolume] using hvolume)
  let coefficient : ENNReal :=
    densityCeiling * (ENNReal.ofReal detLower)⁻¹ *
      (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
      (volume : Measure EightMassEnvironment) environmentPatch
  have hcoefficientFinite : coefficient ≠ (∞ : ENNReal) := by
    have hdetNonzero : ENNReal.ofReal detLower ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hdetLower
    dsimp [coefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hdensityFinite
          (ENNReal.inv_ne_top.mpr hdetNonzero))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
      henvironmentFinite
  refine ⟨patch, coefficient, hpatchOpen, hpointPatch,
    hcoefficientFinite, ?_⟩
  intro delta hdelta
  have hbound := htransferred delta hdelta
  simpa [source, coefficient, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- A compact quantitative good level admits a finite collection of actual
full-iid inverse-function charts.  The theorem exposes both the finite index
set and each finite local coefficient; it is the finite-subcover step used in
the good/bad reduction below. -/
theorem exists_finiteAtlas_actualEightSite_fullIID_goodLevel (n : Nat) :
    ∃ (Index : Type) (_ : Fintype Index)
      (patch : Index → Set (MassTriple × EightMassEnvironment))
      (coefficient : Index → ENNReal),
      selectedFirstFullEightJacobianGoodLevel n ⊆ ⋃ i, patch i ∧
      (∀ i, IsOpen (patch i)) ∧
      (∀ i, coefficient i ≠ (∞ : ENNReal)) ∧
      (∀ i delta, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv
            (finiteMassLaw 8)).restrict (patch i)
              {point |
                |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient i * ENNReal.ofReal (2 * delta)) := by
  classical
  let K := selectedFirstFullEightJacobianGoodLevel n
  have hlocal : ∀ point : K,
      ∃ patch : Set (MassTriple × EightMassEnvironment),
        ∃ coefficient : ENNReal,
          IsOpen patch ∧ point.1 ∈ patch ∧
          coefficient ≠ (∞ : ENNReal) ∧
          ∀ delta : Real, 0 ≤ delta →
            (Measure.map selectedFirstEightMassEquiv
                (finiteMassLaw 8)).restrict patch
                  {sourcePoint |
                    |selectedFirstActualEightSiteMismatch sourcePoint| ≤
                      delta} ≤
              coefficient * ENNReal.ofReal (2 * delta) := by
    intro point
    rcases point.2 with ⟨x, hxGood, hxImage⟩
    have hxRegular :=
      fullEightSelectedJacobianGoodLevel_subset_regular n hxGood
    obtain ⟨patch, coefficient, hopen, hxPatch, hfinite, hbound⟩ :=
      exists_actualEightSite_local_fullIID_linearSmallBallUpper_of_regular
        hxRegular
    refine ⟨patch, coefficient, hopen, ?_, hfinite, hbound⟩
    rw [← hxImage]
    exact hxPatch
  choose patch coefficient hopen hmem hfinite hbound using hlocal
  obtain ⟨atlas, hcover⟩ :=
    (isCompact_selectedFirstFullEightJacobianGoodLevel n).elim_finite_subcover
      patch hopen (by
        intro point hpoint
        rw [mem_iUnion]
        exact ⟨⟨point, hpoint⟩, hmem ⟨point, hpoint⟩⟩)
  let Index := {point : K // point ∈ atlas}
  let atlasPatch : Index → Set (MassTriple × EightMassEnvironment) :=
    fun i => patch i.1
  let atlasCoefficient : Index → ENNReal := fun i => coefficient i.1
  refine ⟨Index, inferInstance, atlasPatch, atlasCoefficient, ?_, ?_, ?_, ?_⟩
  · intro point hpoint
    rcases mem_iUnion₂.mp (hcover hpoint) with
      ⟨center, hcenter, hpointPatch⟩
    rw [mem_iUnion]
    exact ⟨⟨center, hcenter⟩, hpointPatch⟩
  · intro i
    exact hopen i.1
  · intro i
    exact hfinite i.1
  · intro i delta hdelta
    exact hbound i.1 delta hdelta

/-- Finite-atlas `C_n * (2 * delta) + badMass_n` reduction for the actual
full-eight iid mismatch.  The coefficient `C_n` is finite.  The final term is
the exact iid mass of the complement of the compact quantitative good level;
no estimate or limiting assertion about it is hidden in this theorem. -/
theorem exists_finiteCoefficient_actualEightSite_fullIID_goodLevel_smallBallUpper
    (n : Nat) :
    ∃ coefficient : ENNReal, coefficient ≠ (∞ : ENNReal) ∧
      ∀ delta : Real, 0 ≤ delta →
        (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
            {point |
              |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
          coefficient * ENNReal.ofReal (2 * delta) +
            fullEightSelectedJacobianBadMass n := by
  classical
  obtain ⟨Index, instIndex, patch, localCoefficient,
      hcover, _hopen, hlocalFinite, hlocal⟩ :=
    exists_finiteAtlas_actualEightSite_fullIID_goodLevel n
  letI : Fintype Index := instIndex
  let source : Measure (MassTriple × EightMassEnvironment) :=
    Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8)
  let K := selectedFirstFullEightJacobianGoodLevel n
  let coefficient : ENNReal := ∑ i : Index, localCoefficient i
  have hcoefficientFinite : coefficient ≠ (∞ : ENNReal) := by
    dsimp [coefficient]
    simpa only [tsum_fintype] using
      (ENNReal.sum_ne_top.mpr fun i _hi => hlocalFinite i)
  refine ⟨coefficient, hcoefficientFinite, ?_⟩
  intro delta hdelta
  let event : Set (MassTriple × EightMassEnvironment) :=
    {point | |selectedFirstActualEightSiteMismatch point| ≤ delta}
  have hmismatch : Measurable selectedFirstActualEightSiteMismatch := by
    unfold selectedFirstActualEightSiteMismatch
    exact (ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch.continuous_actualEightSiteSelectedMismatch.comp
      (splitEightMass.symm.continuous.comp
        (continuous_snd.prodMk continuous_fst))).measurable
  have hevent : MeasurableSet event := by
    exact (measurableSet_absoluteMismatchSublevel delta).preimage hmismatch
  have hKmeasurable : MeasurableSet K := by
    exact measurableSet_selectedFirstFullEightJacobianGoodLevel n
  have hrestrictGood : source.restrict K ≤
      Measure.sum fun i : Index => source.restrict (patch i) := by
    calc
      source.restrict K ≤ source.restrict (⋃ i, patch i) :=
        source.restrict_mono_set hcover
      _ ≤ Measure.sum fun i : Index => source.restrict (patch i) :=
        Measure.restrict_iUnion_le
  have hgood : source.restrict K event ≤
      coefficient * ENNReal.ofReal (2 * delta) := by
    calc
      source.restrict K event ≤
          (Measure.sum fun i : Index => source.restrict (patch i)) event :=
        hrestrictGood event
      _ = ∑' i : Index, source.restrict (patch i) event := by
        rw [Measure.sum_apply _ hevent]
      _ ≤ ∑' i : Index,
          localCoefficient i * ENNReal.ofReal (2 * delta) :=
        ENNReal.tsum_le_tsum fun i => hlocal i delta hdelta
      _ = coefficient * ENNReal.ofReal (2 * delta) := by
        rw [ENNReal.tsum_mul_right, tsum_fintype]
  have hbad : source.restrict Kᶜ event ≤ source Kᶜ := by
    rw [Measure.restrict_apply hevent]
    exact measure_mono inter_subset_right
  have hsplit : source = source.restrict K + source.restrict Kᶜ := by
    exact (source.restrict_add_restrict_compl hKmeasurable).symm
  change source event ≤ coefficient * ENNReal.ofReal (2 * delta) +
    fullEightSelectedJacobianBadMass n
  rw [hsplit, Measure.add_apply]
  calc
    source.restrict K event + source.restrict Kᶜ event ≤
        coefficient * ENNReal.ofReal (2 * delta) + source Kᶜ := by
      gcongr
    _ = coefficient * ENNReal.ofReal (2 * delta) +
        fullEightSelectedJacobianBadMass n := by
      rfl

end

end ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
