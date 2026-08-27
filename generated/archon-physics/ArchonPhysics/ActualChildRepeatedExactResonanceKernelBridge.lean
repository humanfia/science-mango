import ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
import ArchonPhysics.ActualTwoMassRegularSpectralPatch
import ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
import ArchonPhysics.FiniteMassLawOpenPatch

/-!
# Exact ChildRepeated resonance to quantitative kernel input

This module isolates the shortest honest bridge from an exact
ChildRepeated resonance to the analytic small-ball input used by the
finite-time resonance kernel.

There are three deliberately separate layers.

* A continuous exact, positive-weight point in the interior of the six-fold
  mass cube gives a nonempty open event of positive genuine iid probability.
* An interior simple positive two-mass exact resonance with nonzero true
  frequency Jacobian gives an open inverse-function patch whose image
  contains a child-frequency interval times a symmetric mismatch window.
  A finite upper bound for the true Jacobian on that patch then gives a
  linear small-ball lower bound by reverse coarea.
* A volume-uniform family of such linear bounds gives a volume-uniform
  inverse-time lower bound for the normalized sinc-squared kernel.

The second layer does not turn the four frozen background masses into iid
variables.  The first layer does not produce a linear small-ball slope.
Likewise, the final layer assumes rather than proves the global coupled-chain
localization/additivity statement needed to make the slope uniform in
volume.  Keeping these interfaces separate prevents qualitative open-patch
positivity from being mistaken for the quantitative thermodynamic input.
-/

namespace ArchonPhysics.ActualChildRepeatedExactResonanceKernelBridge

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
open ArchonPhysics.ActualTwoMassRegularSpectralPatch
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
open ArchonPhysics.FiniteMassLawOpenPatch
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ## Qualitative genuine six-IID thickening -/

/-- Exact full-six data sufficient to thicken one resonant point to a
positive-probability iid event.  This structure intentionally asks for the
physical interaction weight at the full-six point; exact mismatch and a
Jacobian alone do not imply that the collision is physically weighted. -/
structure SixIIDExactWeightedResonanceData
    (mismatch weight : (Fin 6 -> Real) -> Real) where
  base : Fin 6 -> Real
  base_interior : forall i, base i ∈ Ioo massLower massUpper
  mismatch_continuous : Continuous mismatch
  weight_continuous : Continuous weight
  exact : mismatch base = 0
  weight_pos : 0 < weight base


/-- Distribution-facing property actually used to thicken one interior
six-mass point: every open neighborhood of such a point has positive law.
This is satisfied both by the frozen uniform product law and by a product of
truncated-Gaussian laws whose one-site density is positive on the support
interior. -/
def SixMassInteriorOpenPatchPositive
    (law : Measure (Fin 6 -> Real)) : Prop :=
  forall patch : Set (Fin 6 -> Real), forall x : Fin 6 -> Real,
    IsOpen patch -> x ∈ patch ->
    (forall i, x i ∈ Ioo massLower massUpper) -> 0 < law patch

/-- Distribution-generic form of qualitative iid thickening. -/
theorem SixIIDExactWeightedResonanceData.exists_positive_openPatch_of_law
    {mismatch weight : (Fin 6 -> Real) -> Real}
    (data : SixIIDExactWeightedResonanceData mismatch weight)
    (law : Measure (Fin 6 -> Real))
    (hlaw : SixMassInteriorOpenPatchPositive law)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set (Fin 6 -> Real),
      IsOpen patch ∧
      0 < law patch ∧
      patch ⊆ {x | |mismatch x| < epsilon ∧ 0 < weight x} := by
  let patch : Set (Fin 6 -> Real) :=
    mismatch ⁻¹' Ioo (-epsilon) epsilon ∩ weight ⁻¹' Ioi 0
  have hopen : IsOpen patch :=
    (isOpen_Ioo.preimage data.mismatch_continuous).inter
      (isOpen_Ioi.preimage data.weight_continuous)
  have hbase : data.base ∈ patch := by
    constructor
    · change mismatch data.base ∈ Ioo (-epsilon) epsilon
      rw [data.exact]
      exact ⟨by linarith, hepsilon⟩
    · exact data.weight_pos
  exact ⟨patch, hopen, hlaw patch data.base hopen hbase data.base_interior,
    fun _ hx => ⟨abs_lt.2 hx.1, hx.2⟩⟩
/-- A continuous exact positive-weight full-six point has, at every positive
mismatch width, an open genuinely-six-IID event of positive probability.
No quantitative dependence of that probability on `epsilon` is claimed. -/
theorem SixIIDExactWeightedResonanceData.exists_positive_iid_openPatch
    {mismatch weight : (Fin 6 -> Real) -> Real}
    (data : SixIIDExactWeightedResonanceData mismatch weight)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set (Fin 6 -> Real),
      IsOpen patch ∧
      0 < finiteMassLaw 6 patch ∧
      patch ⊆ {x | |mismatch x| < epsilon ∧ 0 < weight x} := by
  let patch : Set (Fin 6 -> Real) :=
    mismatch ⁻¹' Ioo (-epsilon) epsilon ∩ weight ⁻¹' Ioi 0
  have hopen : IsOpen patch :=
    (isOpen_Ioo.preimage data.mismatch_continuous).inter
      (isOpen_Ioi.preimage data.weight_continuous)
  have hbase : data.base ∈ patch := by
    constructor
    · change mismatch data.base ∈ Ioo (-epsilon) epsilon
      rw [data.exact]
      exact ⟨by linarith, hepsilon⟩
    · exact data.weight_pos
  refine ⟨patch, hopen,
    finiteMassLaw_pos_of_isOpen_of_mem_interior
      hopen data.base hbase data.base_interior, ?_⟩
  intro x hx
  exact ⟨(abs_lt.2 hx.1), hx.2⟩

/-! ## A resonance-centred actual two-mass inverse-function patch -/

/-- The linear child-frequency/mismatch coordinates as a homeomorphism. -/
def childFrequencyMismatchHomeomorph :
    (Real × Real) ≃ₜ (Real × Real) where
  toEquiv := childFrequencyMismatchLinearEquiv
  continuous_toFun := continuous_childFrequencyMismatchLinearEquiv
  continuous_invFun := by
    change Continuous fun joint : Real × Real =>
      (joint.2 + 2 * joint.1, joint.1)
    fun_prop

/-- Every open neighborhood of `(childCenter, 0)` contains a positive-length
child interval times one closed symmetric mismatch window. -/
theorem exists_positive_childInterval_absoluteMismatchSublevel
    {image : Set (Real × Real)} (himage : IsOpen image)
    (childCenter : Real) (hcenter : (childCenter, 0) ∈ image) :
    ∃ childSet : Set Real, ∃ radius : Real,
      MeasurableSet childSet ∧
      0 < (volume : Measure Real) childSet ∧
      (volume : Measure Real) childSet ≠ ∞ ∧
      0 < radius ∧
      childSet ×ˢ absoluteMismatchSublevel radius ⊆ image := by
  obtain ⟨childNeighborhood, hchildNeighborhood,
      mismatchNeighborhood, hmismatchNeighborhood, hproduct⟩ :=
    mem_nhds_prod_iff.mp (himage.mem_nhds hcenter)
  obtain ⟨a, b, hab, habSubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hchildNeighborhood
  obtain ⟨outerRadius, houterRadius, hballSubset⟩ :=
    Metric.mem_nhds_iff.mp hmismatchNeighborhood
  let radius : Real := outerRadius / 2
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  refine ⟨Ioo a b, radius, measurableSet_Ioo, ?_, ?_, hradius, ?_⟩
  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (hab.1.trans hab.2))
  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  · rintro ⟨child, mismatch⟩ ⟨hchild, hmismatch⟩
    apply hproduct
    constructor
    · exact habSubset hchild
    · apply hballSubset
      rw [Metric.mem_ball, Real.dist_eq]
      change |mismatch - 0| < outerRadius
      have hmismatchRadius : |mismatch| ≤ radius := hmismatch
      dsimp [radius] at hmismatchRadius
      simpa using (lt_of_le_of_lt hmismatchRadius (by linarith))

/-- The two-mass strict inverse function theorem with the openness of the
selected chart image retained.  The older regular-patch theorem deliberately
drops this field because upper coarea does not need it; reverse coarea does. -/
theorem exists_actualTwoMassChildFrequency_openImageRegularPatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (hparent : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) parent)
    (hchild : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child)
    (hJacobian :
      (actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child pair).det ≠ 0) :
    ∃ patch : Set (Real × Real),
      pair ∈ patch ∧
      IsOpen patch ∧
      MeasurableSet patch ∧
      patch ⊆ iidMassPairSupport ∧
      DifferentiableOn Real
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child) patch ∧
      InjOn
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child) patch ∧
      IsOpen
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child '' patch) := by
  let chart :=
    actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
      fixed hsite hpair hsimple parent child hparent hchild
  have hactualDerivative :
      actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child pair = derivative := by
    simpa [chart, actualTwoMassChildFrequencyJacobian] using
      hderivative.hasFDerivAt.fderiv
  have hderivativeDet : derivative.det ≠ 0 := by
    rwa [hactualDerivative] at hJacobian
  have hdetLinear : LinearMap.det derivative.toLinearMap ≠ 0 := by
    simpa [ContinuousLinearMap.det] using hderivativeDet
  have hker : derivative.ker = ⊥ := by
    by_contra hne
    exact hdetLinear (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hinjective : Function.Injective derivative :=
    LinearMap.ker_eq_bot.mp hker
  have hsurjective : Function.Surjective derivative :=
    LinearMap.injective_iff_surjective.mp hinjective
  have hrange : derivative.range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  let derivativeEquiv : (Real × Real) ≃L[Real] (Real × Real) :=
    ContinuousLinearEquiv.ofBijective derivative hker hrange
  have hderivativeEquiv :
      (derivativeEquiv : (Real × Real) →L[Real] (Real × Real)) =
        derivative :=
    ContinuousLinearEquiv.coe_ofBijective derivative hker hrange
  have hstrictEquiv : HasStrictFDerivAt chart
      (derivativeEquiv : (Real × Real) →L[Real] (Real × Real)) pair := by
    rw [hderivativeEquiv]
    exact hderivative
  let localChart : OpenPartialHomeomorph (Real × Real) (Real × Real) :=
    hstrictEquiv.toOpenPartialHomeomorph chart
  have hpairSource : pair ∈ localChart.source :=
    hstrictEquiv.mem_toOpenPartialHomeomorph_source
  have hparentContinuous : Continuous fun nearby =>
      orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) parent :=
    (continuous_orderedEigenvalue parent).comp
      (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)
  have hchildContinuous : Continuous fun nearby =>
      orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child :=
    (continuous_orderedEigenvalue child).comp
      (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)
  let regularitySet : Set (Real × Real) :=
    {nearby |
      nearby ∈ interior iidMassPairSupport ∧
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) ∧
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) parent ∧
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child}
  have hregularityNhds : regularitySet ∈ nhds pair := by
    have hparentEventually : ∀ᶠ nearby in nhds pair,
        0 < orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) parent :=
      hparentContinuous.continuousAt.eventually
        (isOpen_Ioi.mem_nhds hparent)
    have hchildEventually : ∀ᶠ nearby in nhds pair,
        0 < orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child :=
      hchildContinuous.continuousAt.eventually
        (isOpen_Ioi.mem_nhds hchild)
    filter_upwards [isOpen_interior.mem_nhds hpair,
      eventually_simple_twoSiteHarmonicHermitian
        fixed site₁ site₂ pair hsimple,
      hparentEventually, hchildEventually] with
        nearby hsupport hsimpleNearby hparentNearby hchildNearby
    exact ⟨hsupport, hsimpleNearby, hparentNearby, hchildNearby⟩
  obtain ⟨regularityOpen, hopenSubset, hopen, hpairOpen⟩ :=
    mem_nhds_iff.mp hregularityNhds
  let patch : Set (Real × Real) := localChart.source ∩ regularityOpen
  refine ⟨patch, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hpairSource, hpairOpen⟩
  · exact localChart.open_source.inter hopen
  · exact (localChart.open_source.inter hopen).measurableSet
  · intro nearby hnearby
    exact interior_subset (hopenSubset hnearby.2).1
  · intro nearby hnearby
    have hregular := hopenSubset hnearby.2
    obtain ⟨nearbyDerivative, hnearbyDerivative⟩ :=
      exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
        fixed hsite hregular.1 hregular.2.1 parent child
          hregular.2.2.1 hregular.2.2.2
    exact hnearbyDerivative.differentiableAt.differentiableWithinAt
  · apply localChart.injOn.mono
    intro nearby hnearby
    exact hnearby.1
  · exact localChart.isOpen_image_of_subset_source
      (localChart.open_source.inter hopen) inter_subset_left

/-- Complete geometry generated by an exact two-mass ChildRepeated point.
The determinant upper bound is not stored because it is a quantitative
property of the selected patch and is supplied to the reverse-coarea method
below. -/
structure ActualTwoMassChildRepeatedExactPatchData
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) where
  patch : Set (Real × Real)
  childSet : Set Real
  radius : Real
  base_mem : pair ∈ patch
  patch_open : IsOpen patch
  patch_measurable : MeasurableSet patch
  patch_support : patch ⊆ iidMassPairSupport
  differentiable : DifferentiableOn Real
    (actualTwoMassChildFrequencyChart
      fixed site₁ site₂ parent child) patch
  injective : InjOn
    (actualTwoMassChildFrequencyChart
      fixed site₁ site₂ parent child) patch
  childSet_measurable : MeasurableSet childSet
  childSet_volume_pos : 0 < (volume : Measure Real) childSet
  childSet_volume_ne_top : (volume : Measure Real) childSet ≠ ∞
  radius_pos : 0 < radius
  rectangle_subset_image :
    childSet ×ˢ absoluteMismatchSublevel radius ⊆
      childFrequencyMismatchLinearEquiv ''
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child '' patch)

/-- Differentiability on the generated open patch is the true Frechet
derivative required by reverse coarea. -/
theorem ActualTwoMassChildRepeatedExactPatchData.hasFDerivWithinAt
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N}
    {parent child : Fin (Fintype.card (Lattice.Site N))}
    {pair : Real × Real}
    (data : ActualTwoMassChildRepeatedExactPatchData
      fixed site₁ site₂ parent child pair)
    (point : Real × Real) (hpoint : point ∈ data.patch) :
    HasFDerivWithinAt
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child)
      (actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point) data.patch point := by
  have hdiffAt : DifferentiableAt Real
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child) point :=
    (data.differentiable point hpoint).differentiableAt
      (data.patch_open.mem_nhds hpoint)
  simpa [actualTwoMassChildFrequencyJacobian] using
    hdiffAt.hasFDerivAt.hasFDerivWithinAt

/-- Interior exact resonance, simple spectrum, positive participating
frequencies and a nonzero true two-mass Jacobian generate the complete
resonance-centred rectangle geometry. -/
theorem exists_actualTwoMassChildRepeatedExactPatchData
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (hparent : 0 < orderedModeFrequency
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) parent)
    (hchild : 0 < orderedModeFrequency
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child)
    (hJacobian :
      (actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child pair).det ≠ 0)
    (hresonance : childRepeatedDecayMismatch
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child pair) = 0) :
    Nonempty (ActualTwoMassChildRepeatedExactPatchData
      fixed site₁ site₂ parent child pair) := by
  have hparentEnergy : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) parent := by
    exact Real.sqrt_pos.1 hparent
  have hchildEnergy : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child := by
    exact Real.sqrt_pos.1 hchild
  obtain ⟨patch, hbase, hopen, hmeasurable, hsupport,
      hdifferentiable, hinjective, himageOpen⟩ :=
    exists_actualTwoMassChildFrequency_openImageRegularPatch
      fixed hsite parent child pair hpair hsimple hparentEnergy
        hchildEnergy hJacobian
  let chart :=
    actualTwoMassChildFrequencyChart fixed site₁ site₂ parent child
  let transformedImage : Set (Real × Real) :=
    childFrequencyMismatchLinearEquiv '' (chart '' patch)
  have htransformedOpen : IsOpen transformedImage := by
    change IsOpen (childFrequencyMismatchHomeomorph '' (chart '' patch))
    exact childFrequencyMismatchHomeomorph.isOpen_image.2 himageOpen
  have hcenter : ((chart pair).2, 0) ∈ transformedImage := by
    refine ⟨chart pair, ⟨pair, hbase, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · simpa [childFrequencyMismatchLinearEquiv,
        childRepeatedDecayMismatch] using hresonance
  obtain ⟨childSet, radius, hchildMeasurable, hchildPos,
      hchildFinite, hradius, hrectangle⟩ :=
    exists_positive_childInterval_absoluteMismatchSublevel
      htransformedOpen (chart pair).2 hcenter
  exact ⟨{
    patch := patch
    childSet := childSet
    radius := radius
    base_mem := hbase
    patch_open := hopen
    patch_measurable := hmeasurable
    patch_support := hsupport
    differentiable := hdifferentiable
    injective := hinjective
    childSet_measurable := hchildMeasurable
    childSet_volume_pos := hchildPos
    childSet_volume_ne_top := hchildFinite
    radius_pos := hradius
    rectangle_subset_image := hrectangle
  }⟩


/-- The exact-patch geometry plus any positive finite upper bound for the
true Jacobian yields the desired actual iid two-mass linear small-ball lower
bound. -/
theorem ActualTwoMassChildRepeatedExactPatchData.exists_linearSmallBallLower
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N}
    {parent child : Fin (Fintype.card (Lattice.Site N))}
    {pair : Real × Real}
    (data : ActualTwoMassChildRepeatedExactPatchData
      fixed site₁ site₂ parent child pair)
    {detUpper : Real} (hdetUpper : 0 < detUpper)
    (hdet : ∀ point ∈ data.patch,
      |(actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point).det| ≤ detUpper) :
    ∃ constant : Real, 0 < constant ∧
      ∀ delta : Real, 0 < delta → delta ≤ data.radius →
        constant * delta ≤
          (Measure.map childRepeatedDecayMismatch
            (Measure.map
              (actualTwoMassChildFrequencyChart
                fixed site₁ site₂ parent child) iidMassPairLaw)
            (absoluteMismatchSublevel delta)).toReal := by
  exact exists_positive_actualTwoMass_childRepeated_linearSmallBallLower
    fixed site₁ site₂ parent child data.patch_measurable
      data.patch_support data.hasFDerivWithinAt data.injective
      hdetUpper hdet data.childSet_measurable data.childSet_volume_pos
      data.childSet_volume_ne_top data.radius_pos
      data.rectangle_subset_image


/-- Distribution adapter for the quantitative local theorem.  If another
finite two-mass law dominates a positive scalar multiple of the frozen
uniform iid pair law, the exact-patch linear lower bound transfers with the
same scalar loss.  A truncated Gaussian on the same compact support supplies
this premise from a positive lower bound for its normalized density. -/
theorem ActualTwoMassChildRepeatedExactPatchData.exists_linearSmallBallLower_of_law
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N}
    {parent child : Fin (Fintype.card (Lattice.Site N))}
    {pair : Real × Real}
    (data : ActualTwoMassChildRepeatedExactPatchData
      fixed site₁ site₂ parent child pair)
    {detUpper : Real} (hdetUpper : 0 < detUpper)
    (hdet : ∀ point ∈ data.patch,
      |(actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point).det| ≤ detUpper)
    (law : FiniteMeasure (Real × Real))
    (density : NNReal) (hdensity : 0 < density)
    (hdomination : (density : ENNReal) • iidMassPairLaw ≤
      (law : Measure (Real × Real))) :
    ∃ constant : Real, 0 < constant ∧
      ∀ delta : Real, 0 < delta → delta ≤ data.radius →
        constant * delta ≤
          (Measure.map childRepeatedDecayMismatch
            (Measure.map
              (actualTwoMassChildFrequencyChart
                fixed site₁ site₂ parent child) law)
            (absoluteMismatchSublevel delta)).toReal := by
  obtain ⟨baseConstant, hbaseConstant, hbaseBound⟩ :=
    data.exists_linearSmallBallLower hdetUpper hdet
  let constant : Real := (density : Real) * baseConstant
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, hconstant, ?_⟩
  intro delta hdelta hdeltaRadius
  let chart := actualTwoMassChildFrequencyChart
    fixed site₁ site₂ parent child
  let uniformMismatch := Measure.map childRepeatedDecayMismatch
    (Measure.map chart iidMassPairLaw)
  let lawMismatch := Measure.map childRepeatedDecayMismatch
    (Measure.map chart (law : Measure (Real × Real)))
  have hchart : Measurable chart :=
    (continuous_actualTwoMassChildFrequencyChart
      fixed site₁ site₂ parent child).measurable
  have hchartDomination :
      (density : ENNReal) • Measure.map chart iidMassPairLaw ≤
        Measure.map chart (law : Measure (Real × Real)) := by
    rw [← Measure.map_smul]
    exact Measure.map_mono hdomination hchart
  have hmismatchDomination :
      (density : ENNReal) • uniformMismatch ≤ lawMismatch := by
    dsimp [uniformMismatch, lawMismatch]
    rw [← Measure.map_smul]
    exact Measure.map_mono hchartDomination
      measurable_childRepeatedDecayMismatch
  have hmeasure := hmismatchDomination
    (absoluteMismatchSublevel delta)
  rw [Measure.smul_apply] at hmeasure
  have hlawFinite : lawMismatch (absoluteMismatchSublevel delta) ≠ ∞ := by
    exact measure_ne_top _ _
  have hreal := ENNReal.toReal_mono hlawFinite hmeasure
  have hbase := hbaseBound delta hdelta hdeltaRadius
  change constant * delta ≤
    (lawMismatch (absoluteMismatchSublevel delta)).toReal
  calc
    constant * delta =
        (density : Real) * (baseConstant * delta) := by
      dsimp [constant]
      ring
    _ ≤ (density : Real) *
        (uniformMismatch (absoluteMismatchSublevel delta)).toReal :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ (lawMismatch (absoluteMismatchSublevel delta)).toReal := by
      simpa using hreal
/-! ## Uniform small balls imply a uniform inverse-time kernel lower bound -/

/-- The exact analytic contract needed after the model-specific global
localization step: one slope and one radius work for every member of a
finite-measure family. -/
structure VolumeUniformLinearSmallBallLower
    (mismatchMeasure : Nat -> FiniteMeasure Real) where
  constant : Real
  radius : Real
  constant_pos : 0 < constant
  radius_pos : 0 < radius
  bound : forall volumeIndex delta,
    0 < delta -> delta <= radius ->
    constant * delta <=
      ((mismatchMeasure volumeIndex : Measure Real)
        (absoluteMismatchSublevel delta)).toReal

/-- A volume-uniform `constant * delta` small-ball lower bound gives the
same positive sinc-kernel lower bound at every volume whenever the inverse
time window lies inside the certified radius. -/
theorem VolumeUniformLinearSmallBallLower.inverseTimeKernelLower
    {mismatchMeasure : Nat -> FiniteMeasure Real}
    (data : VolumeUniformLinearSmallBallLower mismatchMeasure)
    (volumeIndex : Nat) {T : Real} (hT : 0 < T)
    (hwindow : 1 / (4 * T) <= data.radius) :
    (data.constant / 4) / (4 * Real.pi) <=
      ((ArchonPhysics.BroadenedResonanceMeasure.broadenedResonanceMeasure
        (mismatchMeasure volumeIndex) id measurable_id T hT).mass : Real) := by
  have hdelta : 0 < 1 / (4 * T) := by positivity
  have hlinear := data.bound volumeIndex (1 / (4 * T)) hdelta hwindow
  have hsmallBall :
      (data.constant / 4) / T <=
        ((mismatchMeasure volumeIndex : Measure Real).real
          (absoluteMismatchSublevel (1 / (4 * T)))) := by
    calc
      (data.constant / 4) / T =
          data.constant * (1 / (4 * T)) := by field_simp
      _ <= _ := by simpa [Measure.real] using hlinear
  exact slope_div_four_pi_le_broadenedResonanceMeasure_mass
    (mismatchMeasure volumeIndex) hT hsmallBall

end

end ArchonPhysics.ActualChildRepeatedExactResonanceKernelBridge
