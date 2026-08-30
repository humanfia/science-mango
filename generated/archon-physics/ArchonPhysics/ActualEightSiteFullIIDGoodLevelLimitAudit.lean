import ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Limit audit for the actual full-eight compact good levels

The compact good levels from the preceding module use a reciprocal distance
cutoff from the complement of the transparent regular locus.  Here we prove
that the regular locus is genuinely open, so those levels increase to the
entire physical regular locus, not merely to an unspecified subset.

Continuity from above for the finite iid source then identifies the exact
limit and infimum of the exceptional masses with the iid mass of the
irregular locus.  No nullity theorem for that locus is asserted: convergence
of the bad masses to zero is proved equivalent to regularity almost
everywhere.
-/

open scoped ENNReal Matrix Topology ContDiff BigOperators

namespace ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
open ArchonPhysics.ActualEightSiteFullIIDCompactGoodLevelSmallBallReduction
open ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set

noncomputable section

/-- The true selected partial derivative field obtained from the joint
full-eight lifted family. -/
def fullEightSelectedPartialDerivativeField
    (x : EightMassVector) : MassTriple →L[Real] MassTriple :=
  fderiv Real fullEightLiftedFamily (splitEightMass x) ∘L
    ContinuousLinearMap.inr Real EightMassEnvironment MassTriple

/-- The full lifted family is `C¹` at every physical interior point with
simple spectrum. -/
theorem contDiffAt_one_fullEightLiftedFamily
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    ContDiffAt Real 1 fullEightLiftedFamily (splitEightMass x) := by
  have hactual :=
    contDiffAt_one_actualEightSiteFullLiftedFrequencyChart hx hsimple
  have hinverse : ContDiffAt Real 1
      (fun point => splitEightMass.symm point) (splitEightMass x) := by
    fun_prop
  have hback : splitEightMass.symm (splitEightMass x) = x :=
    splitEightMass.symm_apply_apply x
  have hactualAt : ContDiffAt Real 1
      actualEightSiteFullLiftedFrequencyChart
        (splitEightMass.symm (splitEightMass x)) := by
    rw [hback]
    exact hactual
  change ContDiffAt Real 1
    (fun point => actualEightSiteFullLiftedFrequencyChart
      (splitEightMass.symm point)) (splitEightMass x)
  exact hactualAt.comp (splitEightMass x) hinverse

/-- On the physical simple locus, the `fderiv` used in the original
three-mass definition is exactly the selected partial derivative of the
joint full-eight family. -/
theorem actualEightSiteSelectedPartialJacobian_eq_field
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    actualEightSiteSelectedPartialJacobian x =
      fullEightSelectedPartialDerivativeField x := by
  have hfamily := contDiffAt_one_fullEightLiftedFamily hx hsimple
  let partialDerivative : MassTriple →L[Real] MassTriple :=
    fderiv Real fullEightLiftedFamily (splitEightMass x) ∘L
      ContinuousLinearMap.inr Real EightMassEnvironment MassTriple
  have hsliceRaw := hfamily.differentiableAt_one.hasFDerivAt.comp
    (splitEightMass x).2
      (hasFDerivAt_prodMk_right (splitEightMass x).1
        (splitEightMass x).2)
  have hslice : HasFDerivAt
      (fun triple : MassTriple =>
        fullEightLiftedFamily ((splitEightMass x).1, triple))
      partialDerivative (splitEightMass x).2 := by
    change HasFDerivAt
      (fun triple : MassTriple =>
        fullEightLiftedFamily ((splitEightMass x).1, triple))
      partialDerivative (splitEightMass x).2 at hsliceRaw
    simpa [partialDerivative] using hsliceRaw
  have hsliceThree : HasFDerivAt
      (actualThreeMassLiftedFrequencyChart (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecaySign actualEightSiteDecayModes)
      partialDerivative (splitEightMass x).2 := by
    simpa only [fullEightLiftedFamily_fixed_environment hx] using hslice
  simpa [actualEightSiteSelectedPartialJacobian,
    actualThreeMassLiftedFrequencyJacobian,
    fullEightSelectedPartialDerivativeField, partialDerivative] using
      hsliceThree.fderiv

/-- The selected partial derivative field is continuous at every physical
simple-spectrum point. -/
theorem continuousAt_fullEightSelectedPartialDerivativeField
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    ContinuousAt fullEightSelectedPartialDerivativeField x := by
  have hfamily := contDiffAt_one_fullEightLiftedFamily hx hsimple
  have hfderiv : ContinuousAt (fderiv Real fullEightLiftedFamily)
      (splitEightMass x) :=
    hfamily.continuousAt_fderiv (by norm_num)
  have hcompose : Continuous
      (fun D : (EightMassEnvironment × MassTriple) →L[Real] MassTriple =>
        D ∘L ContinuousLinearMap.inr Real
          EightMassEnvironment MassTriple) := by
    exact continuous_id.clm_comp_const
      (ContinuousLinearMap.inr Real EightMassEnvironment MassTriple)
  have hatSplit : ContinuousAt
      (fun point : EightMassEnvironment × MassTriple =>
        fderiv Real fullEightLiftedFamily point ∘L
          ContinuousLinearMap.inr Real EightMassEnvironment MassTriple)
      (splitEightMass x) :=
    hcompose.continuousAt.comp hfderiv
  exact hatSplit.comp splitEightMass.continuous.continuousAt

/-- The complement of the physical regular locus is nonempty; the zero mass
vector already lies outside the support interior. -/
theorem fullEightSelectedJacobianRegularSet_compl_nonempty :
    fullEightSelectedJacobianRegularSetᶜ.Nonempty := by
  refine ⟨(0 : EightMassVector), ?_⟩
  intro hregular
  have hlower : massLower < 0 := (hregular.1 (0 : Fin 8)).1
  exact (not_lt_of_ge massLower_pos.le) hlower

/-- The transparent actual full-eight regular locus is open.  The only
nontrivial clause is stability of the true selected `fderiv` determinant;
it follows from the local `C¹` derivative field above. -/
theorem isOpen_fullEightSelectedJacobianRegularSet :
    IsOpen fullEightSelectedJacobianRegularSet := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨hxSupport, hsimple, _hpositive, hdet⟩
  have hfieldContinuous :=
    continuousAt_fullEightSelectedPartialDerivativeField hxSupport hsimple
  have hfieldEq :=
    actualEightSiteSelectedPartialJacobian_eq_field hxSupport hsimple
  have hfieldDet : (fullEightSelectedPartialDerivativeField x).det ≠ 0 := by
    rw [← hfieldEq]
    exact hdet
  have hdetEventually : ∀ᶠ y in nhds x,
      (fullEightSelectedPartialDerivativeField y).det ≠ 0 :=
    ((ContinuousLinearMap.continuous_det.continuousAt.comp
      hfieldContinuous).ne_iff_eventually_ne continuousAt_const).1 hfieldDet
  filter_upwards [isOpen_fullEightMassSupportInterior.mem_nhds hxSupport,
    eventually_simple_fullEightHarmonic hsimple,
    hdetEventually] with y hySupport hySimple hyFieldDet
  have hyEq :=
    actualEightSiteSelectedPartialJacobian_eq_field hySupport hySimple
  refine ⟨hySupport, hySimple, ?_, ?_⟩
  · intro r
    exact Real.sqrt_pos.mp (actualEightSiteSelectedFrequency_pos y r)
  · rw [hyEq]
    exact hyFieldDet

/-- Every regular point lies in the closed physical support cube. -/
theorem fullEightSelectedJacobianRegularSet_subset_supportCube :
    fullEightSelectedJacobianRegularSet ⊆ fullEightMassSupportCube := by
  intro x hx i _hi
  exact ⟨(hx.1 i).1.le, (hx.1 i).2.le⟩

/-- The reciprocal-distance good levels are monotone. -/
theorem monotone_fullEightSelectedJacobianGoodLevel :
    Monotone fullEightSelectedJacobianGoodLevel := by
  intro n m hnm x hx
  refine ⟨hx.1, ?_⟩
  have hthreshold : fullEightSelectedJacobianGoodThreshold m ≤
      fullEightSelectedJacobianGoodThreshold n := by
    unfold fullEightSelectedJacobianGoodThreshold
    apply (inv_le_inv₀
      (show (0 : Real) < ((m + 1 : Nat) : Real) by positivity)
      (show (0 : Real) < ((n + 1 : Nat) : Real) by positivity)).2
    exact_mod_cast Nat.add_le_add_right hnm 1
  exact hthreshold.trans hx.2

/-- The countable union of compact good levels is exactly the whole regular
locus. -/
theorem iUnion_fullEightSelectedJacobianGoodLevel_eq_regular :
    (⋃ n, fullEightSelectedJacobianGoodLevel n) =
      fullEightSelectedJacobianRegularSet := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact fullEightSelectedJacobianGoodLevel_subset_regular n hn
  · intro x hx
    have hxCube :=
      fullEightSelectedJacobianRegularSet_subset_supportCube hx
    have hmarginPos : 0 < fullEightSelectedJacobianRegularMargin x := by
      unfold fullEightSelectedJacobianRegularMargin
      have hclosed :=
        isOpen_fullEightSelectedJacobianRegularSet.isClosed_compl
      exact (hclosed.notMem_iff_infDist_pos
        fullEightSelectedJacobianRegularSet_compl_nonempty).1 (by simpa)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmarginPos
    rw [mem_iUnion]
    refine ⟨n, hxCube, ?_⟩
    simpa [fullEightSelectedJacobianGoodThreshold, Nat.cast_add,
      Nat.cast_one, one_div] using hn.le

/-- Requested support-explicit form of the exhaustion identity. -/
theorem iUnion_fullEightSelectedJacobianGoodLevel_eq_support_inter_regular :
    (⋃ n, fullEightSelectedJacobianGoodLevel n) =
      fullEightMassSupportCube ∩ fullEightSelectedJacobianRegularSet := by
  rw [iUnion_fullEightSelectedJacobianGoodLevel_eq_regular]
  exact (inter_eq_right.mpr
    fullEightSelectedJacobianRegularSet_subset_supportCube).symm

/-- The regular locus in the selected-first coordinates. -/
def selectedFirstFullEightJacobianRegularSet :
    Set (MassTriple × EightMassEnvironment) :=
  selectedFirstEightMassEquiv '' fullEightSelectedJacobianRegularSet

theorem isOpen_selectedFirstFullEightJacobianRegularSet :
    IsOpen selectedFirstFullEightJacobianRegularSet := by
  exact selectedFirstEightMassEquiv.toHomeomorph.isOpen_image.2
    isOpen_fullEightSelectedJacobianRegularSet

theorem measurableSet_selectedFirstFullEightJacobianRegularSet :
    MeasurableSet selectedFirstFullEightJacobianRegularSet :=
  isOpen_selectedFirstFullEightJacobianRegularSet.measurableSet

theorem monotone_selectedFirstFullEightJacobianGoodLevel :
    Monotone selectedFirstFullEightJacobianGoodLevel := by
  intro n m hnm
  exact image_mono (monotone_fullEightSelectedJacobianGoodLevel hnm)

theorem iUnion_selectedFirstFullEightJacobianGoodLevel_eq_regular :
    (⋃ n, selectedFirstFullEightJacobianGoodLevel n) =
      selectedFirstFullEightJacobianRegularSet := by
  apply Subset.antisymm
  · intro point hpoint
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.mp hpoint
    exact ⟨x, fullEightSelectedJacobianGoodLevel_subset_regular n hx, rfl⟩
  · rintro point ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp
      (iUnion_fullEightSelectedJacobianGoodLevel_eq_regular.symm ▸ hx)
    rw [mem_iUnion]
    exact ⟨n, x, hn, rfl⟩

/-- Exact physical iid mass of the failure of the transparent regularity
conditions.  No assertion that this number vanishes is made. -/
def fullEightSelectedJacobianIrregularMass : ENNReal :=
  finiteMassLaw 8 fullEightSelectedJacobianRegularSetᶜ

theorem selectedFirst_regular_compl_mass_eq_irregularMass :
    (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
        selectedFirstFullEightJacobianRegularSetᶜ =
      fullEightSelectedJacobianIrregularMass := by
  rw [Measure.map_apply selectedFirstEightMassEquiv.continuous.measurable
    measurableSet_selectedFirstFullEightJacobianRegularSet.compl]
  unfold fullEightSelectedJacobianIrregularMass
  congr 1
  ext x
  simp [selectedFirstFullEightJacobianRegularSet]

/-- The exact bad-mass limit is the iid mass of the irregular locus. -/
theorem tendsto_fullEightSelectedJacobianBadMass_irregularMass :
    Tendsto fullEightSelectedJacobianBadMass atTop
      (nhds fullEightSelectedJacobianIrregularMass) := by
  let source : Measure (MassTriple × EightMassEnvironment) :=
    Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8)
  letI : IsProbabilityMeasure source :=
    Measure.isProbabilityMeasure_map
      selectedFirstEightMassEquiv.continuous.measurable.aemeasurable
  have hanti : Antitone
      (fun n => (selectedFirstFullEightJacobianGoodLevel n)ᶜ) := by
    intro n m hnm
    exact compl_subset_compl.mpr
      (monotone_selectedFirstFullEightJacobianGoodLevel hnm)
  have hinter :
      (⋂ n, (selectedFirstFullEightJacobianGoodLevel n)ᶜ) =
        selectedFirstFullEightJacobianRegularSetᶜ := by
    rw [← compl_iUnion,
      iUnion_selectedFirstFullEightJacobianGoodLevel_eq_regular]
  have hlimit := tendsto_measure_iInter_atTop
    (μ := source)
    (s := fun n => (selectedFirstFullEightJacobianGoodLevel n)ᶜ)
    (fun n =>
      (measurableSet_selectedFirstFullEightJacobianGoodLevel n).compl.nullMeasurableSet)
    hanti ⟨0, measure_ne_top source _⟩
  rw [hinter] at hlimit
  rw [show source selectedFirstFullEightJacobianRegularSetᶜ =
      fullEightSelectedJacobianIrregularMass by
    exact selectedFirst_regular_compl_mass_eq_irregularMass] at hlimit
  change Tendsto
    (fun n => (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
      (selectedFirstFullEightJacobianGoodLevel n)ᶜ) atTop
        (nhds fullEightSelectedJacobianIrregularMass)
  exact hlimit

/-- The infimum of all finite-level bad masses is the same exact irregular
mass. -/
theorem iInf_fullEightSelectedJacobianBadMass_eq_irregularMass :
    (⨅ n, fullEightSelectedJacobianBadMass n) =
      fullEightSelectedJacobianIrregularMass := by
  let source : Measure (MassTriple × EightMassEnvironment) :=
    Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8)
  letI : IsProbabilityMeasure source :=
    Measure.isProbabilityMeasure_map
      selectedFirstEightMassEquiv.continuous.measurable.aemeasurable
  have hanti : Antitone
      (fun n => (selectedFirstFullEightJacobianGoodLevel n)ᶜ) := by
    intro n m hnm
    exact compl_subset_compl.mpr
      (monotone_selectedFirstFullEightJacobianGoodLevel hnm)
  have hinter :
      (⋂ n, (selectedFirstFullEightJacobianGoodLevel n)ᶜ) =
        selectedFirstFullEightJacobianRegularSetᶜ := by
    rw [← compl_iUnion,
      iUnion_selectedFirstFullEightJacobianGoodLevel_eq_regular]
  have hmeasure := hanti.measure_iInter
    (fun n =>
      (measurableSet_selectedFirstFullEightJacobianGoodLevel n).compl.nullMeasurableSet)
    ⟨0, measure_ne_top source _⟩
  rw [hinter] at hmeasure
  rw [show source selectedFirstFullEightJacobianRegularSetᶜ =
      fullEightSelectedJacobianIrregularMass by
    exact selectedFirst_regular_compl_mass_eq_irregularMass] at hmeasure
  simpa [source, fullEightSelectedJacobianBadMass] using hmeasure.symm

/-- Zero irregular mass is exactly almost-everywhere regularity for the
original eightfold iid law. -/
theorem fullEightSelectedJacobianIrregularMass_eq_zero_iff_regular_ae :
    fullEightSelectedJacobianIrregularMass = 0 ↔
      ∀ᵐ x ∂(finiteMassLaw 8),
        x ∈ fullEightSelectedJacobianRegularSet := by
  unfold fullEightSelectedJacobianIrregularMass
  rw [measure_eq_zero_iff_ae_notMem]
  simp only [mem_compl_iff, not_not]

/-- Therefore bad-mass convergence to zero is neither assumed nor obtained
for free: it is equivalent to proving actual regularity almost everywhere. -/
theorem tendsto_fullEightSelectedJacobianBadMass_zero_iff_regular_ae :
    Tendsto fullEightSelectedJacobianBadMass atTop (nhds 0) ↔
      ∀ᵐ x ∂(finiteMassLaw 8),
        x ∈ fullEightSelectedJacobianRegularSet := by
  constructor
  · intro hzero
    have hirregularZero : fullEightSelectedJacobianIrregularMass = 0 :=
      tendsto_nhds_unique
        tendsto_fullEightSelectedJacobianBadMass_irregularMass hzero
    exact
      fullEightSelectedJacobianIrregularMass_eq_zero_iff_regular_ae.mp
        hirregularZero
  · intro hae
    have hirregularZero : fullEightSelectedJacobianIrregularMass = 0 :=
      fullEightSelectedJacobianIrregularMass_eq_zero_iff_regular_ae.mpr hae
    simpa [hirregularZero] using
      tendsto_fullEightSelectedJacobianBadMass_irregularMass

/-- Equivalent infimum formulation of the same remaining scientific
obligation. -/
theorem iInf_fullEightSelectedJacobianBadMass_eq_zero_iff_regular_ae :
    (⨅ n, fullEightSelectedJacobianBadMass n) = 0 ↔
      ∀ᵐ x ∂(finiteMassLaw 8),
        x ∈ fullEightSelectedJacobianRegularSet := by
  rw [iInf_fullEightSelectedJacobianBadMass_eq_irregularMass]
  exact fullEightSelectedJacobianIrregularMass_eq_zero_iff_regular_ae

end

end ArchonPhysics.ActualEightSiteFullIIDGoodLevelLimitAudit
