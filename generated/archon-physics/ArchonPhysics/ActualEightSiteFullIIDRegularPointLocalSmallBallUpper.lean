import ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper

/-!
# Pointwise full-eight small-ball upper bounds on the regular locus

The certified resonance is not used here.  Every point in the transparent
selected-Jacobian regular set produces an actual open chart, a uniform local
Jacobian lower bound, and a linear product-volume mismatch estimate.
-/

open scoped ENNReal Matrix Topology ContDiff

namespace ArchonPhysics.ActualEightSiteFullIIDRegularPointLocalSmallBallUpper

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.LocalParametricJacobianSmallBallPipeline
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.SelectedFirstPartialJacobianChart
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set

noncomputable section

/-- Every actual regular point has an open selected-first chart on which
product volume obeys a true linear mismatch small-ball upper bound. -/
theorem exists_actualEightSite_local_productVolume_linearSmallBallUpper_of_regular
    {x : EightMassVector} (hx : x ∈ fullEightSelectedJacobianRegularSet) :
    ∃ patch : Set (MassTriple × EightMassEnvironment),
      ∃ detLower ceiling : Real,
        ∃ environmentPatch : Set EightMassEnvironment,
          IsOpen patch ∧ selectedFirstEightMassEquiv x ∈ patch ∧
          patch ⊆ selectedFirstEightMassEquiv ''
            fullEightMassSupportInterior ∧
          0 < detLower ∧ 0 < ceiling ∧
          MeasurableSet environmentPatch ∧
          (volume : Measure EightMassEnvironment) environmentPatch ≠
            (∞ : ENNReal) ∧
          ∀ delta : Real, 0 ≤ delta →
            (((volume : Measure MassTriple).prod
                (volume : Measure EightMassEnvironment)).restrict patch)
              {point |
                |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
              (ENNReal.ofReal detLower)⁻¹ *
                  (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
                ENNReal.ofReal (2 * delta) *
                  (volume : Measure EightMassEnvironment)
                    environmentPatch := by
  have hxSupport := hx.1
  have hsimple := hx.2.1
  obtain ⟨derivative, hderivative, hpartial⟩ :=
    exists_fullEightLiftedFamily_strictDerivative_partial_isInvertible_of_regular
      hx
  let point : MassTriple × EightMassEnvironment :=
    selectedFirstEightMassEquiv x
  have hpoint : point = ((splitEightMass x).2, (splitEightMass x).1) := by
    rfl
  have hcont : ContDiffAt Real 1
      fullEightSelectedFirstAugmentedChart point := by
    rw [hpoint]
    exact contDiffAt_one_fullEightSelectedFirstAugmentedChart
      hxSupport hsimple
  obtain ⟨baseDerivative, hstrictRaw, hinvertible⟩ :=
    exists_strictDerivative_isInvertible_selectedFirstAugmentedMap
      hderivative hpartial
  have hstrict : HasStrictFDerivAt fullEightSelectedFirstAugmentedChart
      baseDerivative point := by
    rw [hpoint]
    exact hstrictRaw
  let derivativeField :=
    fderiv Real fullEightSelectedFirstAugmentedChart
  have hfieldAt : derivativeField point = baseDerivative := by
    exact hstrict.hasFDerivAt.fderiv
  have hfieldContinuous : ContinuousAt derivativeField point := by
    exact hcont.continuousAt_fderiv (by norm_num)
  let supportPatch :=
    selectedFirstEightMassEquiv '' fullEightMassSupportInterior
  have hsupportOpen : IsOpen supportPatch :=
    selectedFirstEightMassEquiv.toHomeomorph.isOpen_image.2
      isOpen_fullEightMassSupportInterior
  have hpointSupport : point ∈ supportPatch := ⟨x, hxSupport, rfl⟩
  let regularity : Set (MassTriple × EightMassEnvironment) :=
    {nearby | ContDiffAt Real 1
      fullEightSelectedFirstAugmentedChart nearby} ∩ supportPatch
  have hregularity : regularity ∈ nhds point := by
    apply inter_mem
    · exact hcont.eventually (by norm_num)
    · exact hsupportOpen.mem_nhds hpointSupport
  have htrueDerivative : ∀ nearby ∈ regularity,
      HasFDerivAt fullEightSelectedFirstAugmentedChart
        (derivativeField nearby) nearby := by
    intro nearby hnearby
    exact hnearby.1.differentiableAt_one.hasFDerivAt
  let ceiling : Real := max
      (fullEightSelectedFirstAugmentedChart point).1.1.1
      (fullEightSelectedFirstAugmentedChart point).1.1.2 + 1
  have hchildOne :
      (fullEightSelectedFirstAugmentedChart point).1.1.1 < ceiling := by
    dsimp [ceiling]
    linarith [le_max_left
      (fullEightSelectedFirstAugmentedChart point).1.1.1
      (fullEightSelectedFirstAugmentedChart point).1.1.2]
  have hchildTwo :
      (fullEightSelectedFirstAugmentedChart point).1.1.2 < ceiling := by
    dsimp [ceiling]
    linarith [le_max_right
      (fullEightSelectedFirstAugmentedChart point).1.1.1
      (fullEightSelectedFirstAugmentedChart point).1.1.2]
  have hceiling : 0 < ceiling := by
    have hnonneg : 0 ≤
        (fullEightSelectedFirstAugmentedChart point).1.1.1 := by
      rw [hpoint]
      exact Real.sqrt_nonneg _
    exact lt_of_le_of_lt hnonneg hchildOne
  let environmentPatch : Set EightMassEnvironment :=
    Metric.ball point.2 1
  have henvironmentMeasurable : MeasurableSet environmentPatch :=
    Metric.isOpen_ball.measurableSet
  have henvironmentFinite :
      (volume : Measure EightMassEnvironment) environmentPatch ≠
        (∞ : ENNReal) := by
    exact ne_of_lt measure_ball_lt_top
  let neighborhood : Set (MassTriple × EightMassEnvironment) :=
    {nearby |
      (fullEightSelectedFirstAugmentedChart nearby).1.1.1 < ceiling} ∩
    {nearby |
      (fullEightSelectedFirstAugmentedChart nearby).1.1.2 < ceiling} ∩
    Prod.snd ⁻¹' environmentPatch
  have hneighborhood : neighborhood ∈ nhds point := by
    have hopenOne : IsOpen {nearby |
        (fullEightSelectedFirstAugmentedChart nearby).1.1.1 < ceiling} :=
      isOpen_lt continuous_fullEightSelectedFirstAugmentedChart.fst.fst.fst
        continuous_const
    have hopenTwo : IsOpen {nearby |
        (fullEightSelectedFirstAugmentedChart nearby).1.1.2 < ceiling} :=
      isOpen_lt continuous_fullEightSelectedFirstAugmentedChart.fst.fst.snd
        continuous_const
    have hopenEnvironment : IsOpen (Prod.snd ⁻¹' environmentPatch) :=
      Metric.isOpen_ball.preimage
        (continuous_snd : Continuous
          (fun nearby : MassTriple × EightMassEnvironment => nearby.2))
    exact ((hopenOne.inter hopenTwo).inter hopenEnvironment).mem_nhds
      ⟨⟨hchildOne, hchildTwo⟩, by
        change dist point.2 point.2 < 1
        simpa⟩
  have himageNeighborhood :
      fullEightSelectedFirstAugmentedChart '' neighborhood ⊆
        parametricLiftedCylinder ceiling environmentPatch := by
    rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
    rcases hsourcePoint with ⟨⟨hupperOne, hupperTwo⟩, henvironment⟩
    change
      ((((0 ≤ (fullEightSelectedFirstAugmentedChart sourcePoint).1.1.1) ∧
          (fullEightSelectedFirstAugmentedChart sourcePoint).1.1.1 ≤
            ceiling) ∧
        ((0 ≤ (fullEightSelectedFirstAugmentedChart sourcePoint).1.1.2) ∧
          (fullEightSelectedFirstAugmentedChart sourcePoint).1.1.2 ≤
            ceiling)) ∧ True) ∧
        sourcePoint.2 ∈ environmentPatch
    refine ⟨⟨⟨⟨?_, hupperOne.le⟩, ⟨?_, hupperTwo.le⟩⟩,
      trivial⟩, henvironment⟩
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
  obtain ⟨patch, detLower, hpatchOpen, hpointPatch, hpatchRegular,
      _hpatchNeighborhood, hdetLower, hsmallBall⟩ :=
    exists_localPatch_parametricMismatch_smallBall
      (volume : Measure EightMassEnvironment)
      continuous_fullEightSelectedFirstAugmentedChart.measurable
      hstrict hinvertible derivativeField hfieldAt hfieldContinuous
      hregularity hneighborhood htrueDerivative ceiling
      henvironmentMeasurable himageNeighborhood
  refine ⟨patch, detLower, ceiling, environmentPatch,
    hpatchOpen, ?_, ?_, hdetLower, hceiling, henvironmentMeasurable,
    henvironmentFinite, ?_⟩
  · change point ∈ patch
    exact hpointPatch
  · intro nearby hnearby
    exact (hpatchRegular hnearby).2
  · intro delta hdelta
    have hbound := hsmallBall delta hdelta
    rw [Measure.map_apply measurable_parametricMismatch
      (measurableSet_absoluteMismatchSublevel delta)] at hbound
    rw [Measure.map_apply
      continuous_fullEightSelectedFirstAugmentedChart.measurable
      ((measurableSet_absoluteMismatchSublevel delta).preimage
        measurable_parametricMismatch)] at hbound
    simpa [absoluteMismatchSublevel] using hbound

end

end ArchonPhysics.ActualEightSiteFullIIDRegularPointLocalSmallBallUpper
