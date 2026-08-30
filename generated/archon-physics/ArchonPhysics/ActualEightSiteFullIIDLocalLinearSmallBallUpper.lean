import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall
import ArchonPhysics.LocalParametricJacobianSmallBallPipeline

/-!
# A local full-eight-IID linear small-ball upper bound

The companion full-eight module proves a local `c * delta` lower bound near
one certified exact resonance.  RPA estimates require the opposite direction.
Here the actual eight-mass lifted spectral chart is shown to be `C¹` at the
same certified simple-spectrum point.  The selected three masses are put
first, the remaining five masses are retained as environment coordinates,
and the quantitative local Jacobian pipeline gives a genuine local
`C * delta` upper bound.

This is deliberately a local statement.  It does not claim that one chart
covers the full eight-fold mass cube.  A global full-IID estimate still needs
a finite/countable regular atlas plus control of its Jacobian-degenerate
complement.
-/

open scoped ENNReal Matrix Topology ContDiff

namespace ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
open ArchonPhysics.ActualEightSiteFullIIDLinearSmallBall
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.LocalParametricJacobianSmallBallPipeline
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.SelectedFirstPartialJacobianChart
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set

noncomputable section

/-- The implicit simple eigenvalue branch is jointly `C¹` in all eight raw
mass coordinates. -/
theorem contDiffAt_one_fullEightOrderedEigenvalue
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x))
    (k : Fin (Fintype.card (Lattice.Site 8))) :
    ContDiffAt Real 1
      (fun y => orderedEigenvalue (fullEightHarmonic y) k) x := by
  let A := fullEightHarmonic x
  let lambda := orderedEigenvalue A k
  let characteristic := actualFullEightCharacteristicEquation
  let Dcharacteristic := fderiv Real characteristic (x, lambda)
  have hcharacteristicC1 :
      ContDiffAt Real 1 characteristic (x, lambda) :=
    contDiffAt_one_actualFullEightCharacteristicEquation hx lambda
  have hcharacteristicDeriv :
      HasFDerivAt characteristic Dcharacteristic (x, lambda) :=
    hcharacteristicC1.differentiableAt_one.hasFDerivAt
  have hinclusion : HasFDerivAt (fun energy : Real => (x, energy))
      (ContinuousLinearMap.inr Real EightMassVector Real) lambda :=
    hasFDerivAt_prodMk_right x lambda
  have hslice : HasFDerivAt
      (fun energy : Real => characteristic (x, energy))
      (Dcharacteristic ∘L ContinuousLinearMap.inr Real EightMassVector Real)
      lambda := by
    simpa [Function.comp_def] using
      hcharacteristicDeriv.comp lambda hinclusion
  have hpolynomial : HasFDerivAt
      (fun energy : Real => characteristic (x, energy))
      (ContinuousLinearMap.toSpanSingleton Real
        ((Matrix.charpoly A.1).derivative.eval lambda)) lambda := by
    simpa [characteristic, actualFullEightCharacteristicEquation, A, lambda]
      using ((Matrix.charpoly A.1).hasDerivAt lambda).hasFDerivAt
  have hpartial :
      Dcharacteristic ∘L ContinuousLinearMap.inr Real EightMassVector Real =
        ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda) :=
    hslice.unique hpolynomial
  have hrootDerivative :
      (Matrix.charpoly A.1).derivative.eval lambda ≠ 0 :=
    charpoly_derivative_eval_orderedEigenvalue_ne_zero A hsimple k
  let scalarEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 ((Matrix.charpoly A.1).derivative.eval lambda)
        hrootDerivative)
  have hscalarEquiv : (scalarEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real
        ((Matrix.charpoly A.1).derivative.eval lambda) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [scalarEquiv, mul_comm]
  have hpartialInvertible :
      (Dcharacteristic ∘L
        ContinuousLinearMap.inr Real EightMassVector Real).IsInvertible := by
    rw [hpartial]
    exact ⟨scalarEquiv, hscalarEquiv⟩
  let branch := hcharacteristicC1.implicitFunction
    (by norm_num) hpartialInvertible
  have hbranchC1 : ContDiffAt Real 1 branch x :=
    hcharacteristicC1.contDiffAt_implicitFunction
      (by norm_num) hpartialInvertible
  let orderedBranch : EightMassVector → Real := fun y =>
    orderedEigenvalue (fullEightHarmonic y) k
  have horderedContinuous : Continuous orderedBranch :=
    (continuous_orderedEigenvalue k).comp continuous_fullEightHarmonic
  have horderedTendsto : Tendsto (fun y => (y, orderedBranch y))
      (nhds x) (nhds (x, lambda)) :=
    tendsto_id.prodMk_nhds horderedContinuous.continuousAt
  have hrootBase : characteristic (x, lambda) = 0 :=
    charpoly_eval_orderedEigenvalue_eq_zero A k
  have hbranchEq : branch =ᶠ[nhds x] orderedBranch := by
    have hiff := hcharacteristicC1.eventually_apply_eq_iff_implicitFunction
      (by norm_num) hpartialInvertible
    filter_upwards [horderedTendsto.eventually hiff] with y hnear
    have hrootNearby : characteristic (y, orderedBranch y) = 0 :=
      charpoly_eval_orderedEigenvalue_eq_zero (fullEightHarmonic y) k
    exact hnear.mp (hrootNearby.trans hrootBase.symm)
  exact hbranchC1.congr_of_eventuallyEq hbranchEq.symm

theorem contDiffAt_one_fullEightOrderedModeFrequency
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x))
    (k : Fin (Fintype.card (Lattice.Site 8)))
    (hpositive : 0 < orderedEigenvalue (fullEightHarmonic x) k) :
    ContDiffAt Real 1
      (fun y => orderedModeFrequency (fullEightHarmonic y) k) x := by
  simpa [orderedModeFrequency] using
    (contDiffAt_one_fullEightOrderedEigenvalue hx hsimple k).sqrt
      (ne_of_gt hpositive)

/-- The three-output actual lifted chart is `C¹` jointly in all eight
masses at every interior simple-spectrum point. -/
theorem contDiffAt_one_actualEightSiteFullLiftedFrequencyChart
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    ContDiffAt Real 1 actualEightSiteFullLiftedFrequencyChart x := by
  have hpositive : ∀ r, 0 < orderedEigenvalue
      (fullEightHarmonic x) (actualEightSiteDecayModes r) := by
    intro r
    exact Real.sqrt_pos.1 (actualEightSiteSelectedFrequency_pos x r)
  have hfrequency : ∀ r, ContDiffAt Real 1
      (fun y => orderedModeFrequency (fullEightHarmonic y)
        (actualEightSiteDecayModes r)) x := fun r =>
    contDiffAt_one_fullEightOrderedModeFrequency hx hsimple
      (actualEightSiteDecayModes r) (hpositive r)
  have hmismatch : ContDiffAt Real 1
      (fun y => ∑ r, (actualEightSiteDecaySign r).coefficient *
        orderedModeFrequency (fullEightHarmonic y)
          (actualEightSiteDecayModes r)) x := by
    apply ContDiffAt.sum
    intro r _hr
    exact (contDiffAt_const : ContDiffAt Real 1
      (fun _ : EightMassVector =>
        (actualEightSiteDecaySign r).coefficient) x).mul (hfrequency r)
  unfold actualEightSiteFullLiftedFrequencyChart
  exact ((hfrequency 1).prodMk (hfrequency 2)).prodMk hmismatch

/-- Actual full-eight mismatch expressed in selected-first coordinates. -/
def selectedFirstActualEightSiteMismatch
    (point : MassTriple × EightMassEnvironment) : Real :=
  actualEightSiteSelectedMismatch
    (splitEightMass.symm (point.2, point.1))

def fullEightSelectedFirstAugmentedChart :
    MassTriple × EightMassEnvironment →
      MassTriple × EightMassEnvironment :=
  selectedFirstAugmentedMap fullEightLiftedFamily

/-- The coordinate permutation used by the selected-first chart. -/
def selectedFirstEightMassEquiv : EightMassVector ≃L[Real]
    (MassTriple × EightMassEnvironment) :=
  splitEightMass.trans
    (ContinuousLinearEquiv.prodComm Real EightMassEnvironment MassTriple)

/-- The actual eightfold iid law in selected-first coordinates is bounded by
a finite multiple of product volume.  Thus local density domination is not a
new probabilistic hypothesis for `finiteMassLaw 8`; it follows from its exact
constant density on the support cube and Haar uniqueness under the linear
coordinate permutation. -/
theorem exists_selectedFirstFiniteMassLaw_le_smul_productVolume :
    ∃ densityCeiling : ENNReal, densityCeiling ≠ (∞ : ENNReal) ∧
      Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8) ≤
        densityCeiling •
          ((volume : Measure MassTriple).prod
            (volume : Measure EightMassEnvironment)) := by
  let normalization : ENNReal :=
    ((volume : Measure Real) massSupport)⁻¹ ^ 8
  have hfiniteMass : finiteMassLaw 8 ≤
      normalization • (volume : Measure EightMassVector) := by
    rw [finiteMassLaw_eight_eq_smul_restrict_volume]
    exact smul_mono_right normalization Measure.restrict_le_self
  let e := selectedFirstEightMassEquiv
  let sourceVolume : Measure EightMassVector := volume
  let targetVolume : Measure (MassTriple × EightMassEnvironment) := volume
  letI : MeasureTheory.Measure.IsAddHaarMeasure
      (volume : Measure Real) := by
    rw [← MeasureTheory.addHaarMeasure_eq_volume]
    infer_instance
  letI : MeasureTheory.Measure.IsAddHaarMeasure
      (volume : Measure (Real × Real)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  letI : MeasureTheory.Measure.IsAddHaarMeasure
      (volume : Measure MassTriple) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  letI : MeasureTheory.Measure.IsAddHaarMeasure
      (volume : Measure EightMassEnvironment) :=
    MeasureTheory.isAddHaarMeasure_volume_pi _
  letI : MeasureTheory.Measure.IsAddHaarMeasure targetVolume := by
    dsimp [targetVolume]
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  letI : MeasureTheory.Measure.IsAddHaarMeasure
      (Measure.map e sourceVolume) :=
    e.isAddHaarMeasure_map sourceVolume
  let coordinateFactor : NNReal :=
    MeasureTheory.Measure.addHaarScalarFactor
      (Measure.map e sourceVolume) targetVolume
  have hmapVolume : Measure.map e sourceVolume =
      (coordinateFactor : ENNReal) • targetVolume := by
    exact MeasureTheory.Measure.isAddLeftInvariant_eq_smul _ _
  have hmapped := Measure.map_mono hfiniteMass e.continuous.measurable
  have hmapped' : Measure.map e (finiteMassLaw 8) ≤
      (normalization * (coordinateFactor : ENNReal)) • targetVolume := by
    rw [Measure.map_smul, hmapVolume, smul_smul] at hmapped
    exact hmapped
  refine ⟨normalization * (coordinateFactor : ENNReal), ?_, ?_⟩
  · have hnormalization : normalization ≠ (∞ : ENNReal) := by
      dsimp [normalization]
      simp [massSupport, massLower, massUpper, Real.volume_Icc]
      norm_num
    exact ENNReal.mul_ne_top hnormalization ENNReal.coe_ne_top
  · simpa [e, sourceVolume, targetVolume, Measure.volume_eq_prod] using hmapped'

@[simp] theorem parametricMismatch_fullEightSelectedFirstAugmentedChart
    (point : MassTriple × EightMassEnvironment) :
    parametricMismatch (fullEightSelectedFirstAugmentedChart point) =
      selectedFirstActualEightSiteMismatch point := by
  rfl


theorem continuous_actualEightSiteFullLiftedFrequencyChart :
    Continuous actualEightSiteFullLiftedFrequencyChart := by
  unfold actualEightSiteFullLiftedFrequencyChart
  exact (((continuous_orderedModeFrequency (actualEightSiteDecayModes 1)).comp
    continuous_fullEightHarmonic).prodMk
      ((continuous_orderedModeFrequency (actualEightSiteDecayModes 2)).comp
        continuous_fullEightHarmonic)).prodMk
          continuous_actualEightSiteSelectedMismatch

theorem continuous_fullEightSelectedFirstAugmentedChart :
    Continuous fullEightSelectedFirstAugmentedChart := by
  have hfamily : Continuous fullEightLiftedFamily := by
    unfold fullEightLiftedFamily
    exact continuous_actualEightSiteFullLiftedFrequencyChart.comp
      splitEightMass.symm.continuous
  unfold fullEightSelectedFirstAugmentedChart selectedFirstAugmentedMap
  exact (hfamily.comp (continuous_snd.prodMk continuous_fst)).prodMk
    continuous_snd

theorem contDiffAt_one_fullEightSelectedFirstAugmentedChart
    {x : EightMassVector} (hx : x ∈ fullEightMassSupportInterior)
    (hsimple : SimpleOrderedSpectrum (fullEightHarmonic x)) :
    ContDiffAt Real 1 fullEightSelectedFirstAugmentedChart
      ((splitEightMass x).2, (splitEightMass x).1) := by
  have hactual :=
    contDiffAt_one_actualEightSiteFullLiftedFrequencyChart hx hsimple
  have hfamily : ContDiffAt Real 1 fullEightLiftedFamily
      (splitEightMass x) := by
    have hinverse : ContDiffAt Real 1 (fun point => splitEightMass.symm point)
        (splitEightMass x) := by fun_prop
    have hback : splitEightMass.symm (splitEightMass x) = x :=
      splitEightMass.symm_apply_apply x
    have hactualAt : ContDiffAt Real 1 actualEightSiteFullLiftedFrequencyChart
        (splitEightMass.symm (splitEightMass x)) := by
      rw [hback]
      exact hactual
    change ContDiffAt Real 1
      (fun point => actualEightSiteFullLiftedFrequencyChart
        (splitEightMass.symm point)) (splitEightMass x)
    exact hactualAt.comp (splitEightMass x) hinverse
  have hswap : ContDiffAt Real 1
      (fun point : MassTriple × EightMassEnvironment => (point.2, point.1))
      ((splitEightMass x).2, (splitEightMass x).1) := by
    fun_prop
  have hfirst := hfamily.comp
    ((splitEightMass x).2, (splitEightMass x).1) hswap
  change ContDiffAt Real 1
    (fun point : MassTriple × EightMassEnvironment =>
      (fullEightLiftedFamily (point.2, point.1), point.2))
    ((splitEightMass x).2, (splitEightMass x).1)
  exact hfirst.prodMk
    (contDiffAt_snd : ContDiffAt Real 1
      (fun point : MassTriple × EightMassEnvironment => point.2)
      ((splitEightMass x).2, (splitEightMass x).1))


/-- A local product-volume small-ball estimate transfers to any source whose
restriction to the same patch has an explicit bounded density.  This is the
precise measure-theoretic input needed to apply the geometric chart estimate
to a pushed-forward iid mass law; no decay or small-ball assumption is hidden
in this lemma. -/
theorem localSmallBallUpper_of_restrictedMeasure_le
    (source : Measure (MassTriple × EightMassEnvironment))
    (densityCeiling : ENNReal)
    (patch : Set (MassTriple × EightMassEnvironment))
    (hsource : source.restrict patch ≤ densityCeiling •
      (((volume : Measure MassTriple).prod
        (volume : Measure EightMassEnvironment)).restrict patch))
    (detLower ceiling : Real)
    (environmentPatch : Set EightMassEnvironment)
    (hvolume : ∀ delta : Real, 0 ≤ delta →
      (((volume : Measure MassTriple).prod
          (volume : Measure EightMassEnvironment)).restrict patch)
        {point | |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
      (ENNReal.ofReal detLower)⁻¹ *
          (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
        ENNReal.ofReal (2 * delta) *
          (volume : Measure EightMassEnvironment) environmentPatch) :
    ∀ delta : Real, 0 ≤ delta →
      source.restrict patch
          {point | |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
        densityCeiling *
          ((ENNReal.ofReal detLower)⁻¹ *
              (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
            ENNReal.ofReal (2 * delta) *
              (volume : Measure EightMassEnvironment) environmentPatch) := by
  intro delta hdelta
  let event : Set (MassTriple × EightMassEnvironment) :=
    {point | |selectedFirstActualEightSiteMismatch point| ≤ delta}
  calc
    source.restrict patch event ≤
        densityCeiling *
          (((volume : Measure MassTriple).prod
            (volume : Measure EightMassEnvironment)).restrict patch) event := by
      simpa only [Measure.smul_apply, smul_eq_mul] using
        Measure.le_iff'.1 hsource event
    _ ≤ densityCeiling *
        ((ENNReal.ofReal detLower)⁻¹ *
            (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          ENNReal.ofReal (2 * delta) *
            (volume : Measure EightMassEnvironment) environmentPatch) := by
      gcongr
      exact hvolume delta hdelta


/-- Local RPA-direction estimate at the certified actual resonance.  The
source measure is Lebesgue measure in selected-first coordinates, restricted
to an open patch lying inside the eight-mass support interior. -/
theorem exists_actualEightSite_fullIID_local_linearSmallBallUpper :
    ∃ t ∈ Ioo
        ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowLower
        ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowUpper,
      let x := actualEightSiteRationalMassPath t
      let sourceEquiv : EightMassVector ≃L[Real]
          (MassTriple × EightMassEnvironment) :=
        splitEightMass.trans
          (ContinuousLinearEquiv.prodComm Real EightMassEnvironment MassTriple)
      ∃ patch : Set (MassTriple × EightMassEnvironment),
        ∃ detLower ceiling : Real,
          ∃ environmentPatch : Set EightMassEnvironment,
            IsOpen patch ∧ sourceEquiv x ∈ patch ∧
            patch ⊆ sourceEquiv '' fullEightMassSupportInterior ∧
            0 < detLower ∧ 0 < ceiling ∧
            MeasurableSet environmentPatch ∧
            (volume : Measure EightMassEnvironment) environmentPatch ≠ (∞ : ENNReal) ∧
            ∀ delta : Real, 0 ≤ delta →
              (((volume : Measure MassTriple).prod
                    (volume : Measure EightMassEnvironment)).restrict patch)
                  {point |
                    |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
                (ENNReal.ofReal detLower)⁻¹ *
                    (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
                  ENNReal.ofReal (2 * delta) *
                    (volume : Measure EightMassEnvironment) environmentPatch := by
  obtain ⟨t, ht, derivative, hx, _hxresonance, hderivative, hpartial⟩ :=
    exists_fullEightLiftedFamily_strictDerivative_partial_isInvertible
  let x := actualEightSiteRationalMassPath t
  let sourceEquiv : EightMassVector ≃L[Real]
      (MassTriple × EightMassEnvironment) :=
    splitEightMass.trans
      (ContinuousLinearEquiv.prodComm Real EightMassEnvironment MassTriple)
  let point : MassTriple × EightMassEnvironment := sourceEquiv x
  have hpoint : point = ((splitEightMass x).2, (splitEightMass x).1) := by
    rfl
  have htcc : t ∈ Icc
      ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowLower
      ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge.actualEightSiteNarrowUpper :=
    ⟨ht.1.le, ht.2.le⟩
  have hsimple : SimpleOrderedSpectrum (fullEightHarmonic x) := by
    exact ArchonPhysics.ActualEightSiteNarrowUniformSimpleSpectrum.fullEightHarmonic_narrow_simpleOrderedSpectrum
      htcc
  have hcont : ContDiffAt Real 1
      fullEightSelectedFirstAugmentedChart point := by
    rw [hpoint]
    exact contDiffAt_one_fullEightSelectedFirstAugmentedChart hx hsimple
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
  let supportPatch := sourceEquiv '' fullEightMassSupportInterior
  have hsupportOpen : IsOpen supportPatch :=
    sourceEquiv.toHomeomorph.isOpen_image.2
      isOpen_fullEightMassSupportInterior
  have hpointSupport : point ∈ supportPatch := ⟨x, hx, rfl⟩
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
      (volume : Measure EightMassEnvironment) environmentPatch ≠ (∞ : ENNReal) := by
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
          (fullEightSelectedFirstAugmentedChart sourcePoint).1.1.1 ≤ ceiling) ∧
        ((0 ≤ (fullEightSelectedFirstAugmentedChart sourcePoint).1.1.2) ∧
          (fullEightSelectedFirstAugmentedChart sourcePoint).1.1.2 ≤ ceiling)) ∧
        True) ∧ sourcePoint.2 ∈ environmentPatch
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
  refine ⟨t, ht, patch, detLower, ceiling, environmentPatch,
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


/-- End-to-end local `C * delta` upper bound for the actual pushed-forward
eightfold iid mass law.  All source-density and support conditions are now
discharged; locality of `patch` is the only remaining qualification. -/
theorem exists_actualEightSite_fullIID_restricted_local_linearSmallBallUpper :
    ∃ patch : Set (MassTriple × EightMassEnvironment),
      ∃ detLower ceiling : Real,
        ∃ environmentPatch : Set EightMassEnvironment,
          ∃ densityCeiling : ENNReal,
            IsOpen patch ∧ patch.Nonempty ∧
            patch ⊆ selectedFirstEightMassEquiv '' fullEightMassSupportInterior ∧
            0 < detLower ∧ 0 < ceiling ∧
            densityCeiling ≠ (∞ : ENNReal) ∧
            MeasurableSet environmentPatch ∧
            (volume : Measure EightMassEnvironment) environmentPatch ≠
              (∞ : ENNReal) ∧
            ∀ delta : Real, 0 ≤ delta →
              (Measure.map selectedFirstEightMassEquiv
                  (finiteMassLaw 8)).restrict patch
                    {point |
                      |selectedFirstActualEightSiteMismatch point| ≤ delta} ≤
                densityCeiling *
                  ((ENNReal.ofReal detLower)⁻¹ *
                      (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
                    ENNReal.ofReal (2 * delta) *
                      (volume : Measure EightMassEnvironment)
                        environmentPatch) := by
  obtain ⟨t, ht, hlocal⟩ :=
    exists_actualEightSite_fullIID_local_linearSmallBallUpper
  dsimp only at hlocal
  obtain ⟨patch, detLower, ceiling, environmentPatch,
      hpatchOpen, hpointPatch, hpatchSupport, hdetLower, hceiling,
      henvironmentMeasurable, henvironmentFinite, hvolume⟩ := hlocal
  obtain ⟨densityCeiling, hdensityFinite, hdensity⟩ :=
    exists_selectedFirstFiniteMassLaw_le_smul_productVolume
  let productVolume : Measure (MassTriple × EightMassEnvironment) :=
    (volume : Measure MassTriple).prod
      (volume : Measure EightMassEnvironment)
  have hsourcePatch :
      (Measure.map selectedFirstEightMassEquiv
        (finiteMassLaw 8)).restrict patch ≤
          densityCeiling • productVolume.restrict patch := by
    calc
      (Measure.map selectedFirstEightMassEquiv
          (finiteMassLaw 8)).restrict patch ≤
          (densityCeiling • productVolume).restrict patch :=
        Measure.restrict_mono_measure hdensity patch
      _ = densityCeiling • productVolume.restrict patch := by
        rw [Measure.restrict_smul]
  have htransferred := localSmallBallUpper_of_restrictedMeasure_le
    (Measure.map selectedFirstEightMassEquiv (finiteMassLaw 8))
    densityCeiling patch hsourcePatch detLower ceiling environmentPatch
    (by simpa [productVolume] using hvolume)
  refine ⟨patch, detLower, ceiling, environmentPatch, densityCeiling,
    hpatchOpen, ⟨_, hpointPatch⟩, ?_, hdetLower, hceiling,
    hdensityFinite, henvironmentMeasurable, henvironmentFinite, htransferred⟩
  simpa [selectedFirstEightMassEquiv] using hpatchSupport

end

end ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
