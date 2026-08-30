import ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
import ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound
import ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound

/-!
# Exact-resonance linear small balls for the actual three-mass chart

An interior simple-positive exact three-wave resonance with nonzero genuine
three-mass Jacobian supplies more than qualitative positivity.  The inverse
function theorem gives a local chart whose image contains a fixed positive
area child rectangle times every sufficiently small symmetric mismatch
window.  Local continuity of the true determinant supplies a finite upper
Jacobian bound on the same source patch.  Reverse coarea then yields an
explicit positive `constant * delta` lower bound for the iid mismatch law.

This is a fixed frozen-environment theorem.  It does not identify the local
modes with modes of a larger coupled chain and makes no volume-uniform claim.
-/

namespace ArchonPhysics.ActualThreeMassLiftedExactResonanceLinearSmallBall

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
open ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-! ## Product geometry in the open chart image -/

/-- Every open neighborhood of `(childCenter, 0)` contains a positive finite
area child rectangle times one closed symmetric mismatch window. -/
theorem exists_positiveArea_childRectangle_absoluteMismatchSublevel
    {image : Set MassTriple} (himage : IsOpen image)
    (childCenter : Real × Real) (hcenter : (childCenter, 0) ∈ image) :
    ∃ child : Set (Real × Real), ∃ radius : Real,
      MeasurableSet child ∧
      0 < (volume : Measure (Real × Real)) child ∧
      (volume : Measure (Real × Real)) child ≠ ∞ ∧
      0 < radius ∧
      child ×ˢ absoluteMismatchSublevel radius ⊆ image := by
  obtain ⟨childNeighborhood, hchildNeighborhood,
      mismatchNeighborhood, hmismatchNeighborhood, hproduct⟩ :=
    mem_nhds_prod_iff.mp (himage.mem_nhds hcenter)
  obtain ⟨firstNeighborhood, hfirstNeighborhood,
      secondNeighborhood, hsecondNeighborhood, hchildProduct⟩ :=
    mem_nhds_prod_iff.mp hchildNeighborhood
  obtain ⟨a, b, hab, habSubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hfirstNeighborhood
  obtain ⟨c, d, hcd, hcdSubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hsecondNeighborhood
  obtain ⟨outerRadius, houterRadius, hballSubset⟩ :=
    Metric.mem_nhds_iff.mp hmismatchNeighborhood
  let radius : Real := outerRadius / 2
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  refine ⟨Ioo a b ×ˢ Ioo c d, radius,
    measurableSet_Ioo.prod measurableSet_Ioo, ?_, ?_, hradius, ?_⟩
  · change ((volume : Measure Real).prod (volume : Measure Real))
      (Ioo a b ×ˢ Ioo c d) > 0
    rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hab.1.trans hab.2))).ne'
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hcd.1.trans hcd.2))).ne'
  · change ((volume : Measure Real).prod (volume : Measure Real))
      (Ioo a b ×ˢ Ioo c d) ≠ ∞
    rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · rintro ⟨⟨x, y⟩, mismatch⟩ ⟨⟨hx, hy⟩, hmismatch⟩
    apply hproduct
    constructor
    · exact hchildProduct ⟨habSubset hx, hcdSubset hy⟩
    · apply hballSubset
      rw [Metric.mem_ball, Real.dist_eq]
      change |mismatch - 0| < outerRadius
      have hmismatchRadius : |mismatch| ≤ radius := hmismatch
      dsimp [radius] at hmismatchRadius
      simpa using (lt_of_le_of_lt hmismatchRadius (by linarith))

/-! ## A determinant-bounded exact-resonance patch -/

/-- Complete local data needed by the reverse-coarea linear lower bound. -/
structure ActualThreeMassExactResonancePatchData
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) where
  patch : Set MassTriple
  child : Set (Real × Real)
  radius : Real
  base_mem : triple ∈ patch
  patch_open : IsOpen patch
  patch_measurable : MeasurableSet patch
  patch_support : patch ⊆ iidMassTripleSupport
  differentiable : DifferentiableOn Real
    (actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes) patch
  injective : InjOn
    (actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes) patch
  child_measurable : MeasurableSet child
  child_volume_pos : 0 < (volume : Measure (Real × Real)) child
  child_volume_ne_top : (volume : Measure (Real × Real)) child ≠ ∞
  radius_pos : 0 < radius
  product_subset_image :
    child ×ˢ absoluteMismatchSublevel radius ⊆
      actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes '' patch

/-- On the open source patch, the derivative stored by `fderiv` is the true
actual lifted Jacobian used by the reverse area formula. -/
theorem ActualThreeMassExactResonancePatchData.hasFDerivWithinAt
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₀ site₁ site₂ : Lattice.Site N}
    {sign : Fin 3 → InteractionSign}
    {modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))}
    {triple : MassTriple}
    (data : ActualThreeMassExactResonancePatchData
      fixed site₀ site₁ site₂ sign modes triple)
    (point : MassTriple) (hpoint : point ∈ data.patch) :
    HasFDerivWithinAt
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes)
      (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes point) data.patch point := by
  have hdiffAt : DifferentiableAt Real
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) point :=
    (data.differentiable point hpoint).differentiableAt
      (data.patch_open.mem_nhds hpoint)
  simpa [actualThreeMassLiftedFrequencyJacobian] using
    hdiffAt.hasFDerivAt.hasFDerivWithinAt

/-- An exact regular resonant point generates a single open inverse-function
patch on which the true determinant also has a positive finite ceiling. -/
theorem exists_actualThreeMassExactResonancePatchData_with_detUpper
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r))
    (hJacobian :
      (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det ≠ 0)
    (hresonance :
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes triple).2 = 0) :
    ∃ data : ActualThreeMassExactResonancePatchData
        fixed site₀ site₁ site₂ sign modes triple,
      ∃ detUpper : Real, 0 < detUpper ∧
        ∀ point ∈ data.patch,
          |(actualThreeMassLiftedFrequencyJacobian
            fixed site₀ site₁ site₂ sign modes point).det| ≤ detUpper := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  let J := actualThreeMassLiftedFrequencyJacobian
    fixed site₀ site₁ site₂ sign modes triple
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualThreeMassLiftedFrequencyChart
      fixed h₁₀ h₂₀ h₂₁ sign modes htriple hsimple hpositive
  have hactualDerivative : J = derivative := by
    simpa [J, chart, actualThreeMassLiftedFrequencyJacobian] using
      hderivative.hasFDerivAt.fderiv
  have hderivativeDet : derivative.det ≠ 0 := by
    have hJ : J.det ≠ 0 := by
      simpa [J] using hJacobian
    simpa [hactualDerivative] using hJ
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
  let derivativeEquiv : MassTriple ≃L[Real] MassTriple :=
    ContinuousLinearEquiv.ofBijective derivative hker hrange
  have hderivativeEquiv :
      (derivativeEquiv : MassTriple →L[Real] MassTriple) = derivative :=
    ContinuousLinearEquiv.coe_ofBijective derivative hker hrange
  have hstrictEquiv : HasStrictFDerivAt chart
      (derivativeEquiv : MassTriple →L[Real] MassTriple) triple := by
    rw [hderivativeEquiv]
    exact hderivative
  let localChart : OpenPartialHomeomorph MassTriple MassTriple :=
    hstrictEquiv.toOpenPartialHomeomorph chart
  have htripleSource : triple ∈ localChart.source :=
    hstrictEquiv.mem_toOpenPartialHomeomorph_source
  have hfrequencyContinuous (r : Fin 3) : Continuous fun nearby =>
      orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
        (modes r) :=
    (continuous_orderedEigenvalue (modes r)).comp
      (continuous_threeMassHarmonicHermitian fixed site₀ site₁ site₂)
  let regularitySet : Set MassTriple :=
    {nearby |
      nearby ∈ interior iidMassTripleSupport ∧
      SimpleOrderedSpectrum
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) ∧
      ∀ r, 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
        (modes r)}
  have hpositiveEventually : ∀ᶠ nearby in nhds triple,
      ∀ r, 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
        (modes r) := by
    rw [eventually_all]
    intro r
    exact (hfrequencyContinuous r).continuousAt.eventually
      (isOpen_Ioi.mem_nhds (hpositive r))
  have hregularityNhds : regularitySet ∈ nhds triple := by
    filter_upwards [isOpen_interior.mem_nhds htriple,
      eventually_simple_threeMassHarmonicHermitian
        fixed site₀ site₁ site₂ triple hsimple,
      hpositiveEventually] with nearby hsupport hsimpleNearby hpositiveNearby
    exact ⟨hsupport, hsimpleNearby, hpositiveNearby⟩
  obtain ⟨regularityOpen, hopenSubset, hopenRegularity, htripleRegularity⟩ :=
    mem_nhds_iff.mp hregularityNhds
  let detUpper : Real := |J.det| + 1
  have hdetUpper : 0 < detUpper := by
    dsimp [detUpper]
    positivity
  have hdetContinuous : ContinuousAt
      (fun nearby => (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes nearby).det) triple :=
    continuousAt_actualThreeMassLiftedFrequencyJacobian_det
      fixed h₁₀ h₂₀ h₂₁ sign modes htriple hsimple hpositive
  have hdetEventually : ∀ᶠ nearby in nhds triple,
      |(actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes nearby).det| < detUpper := by
    have htarget : ∀ᶠ value in nhds |J.det|, value < detUpper :=
      Iio_mem_nhds (by simp [detUpper])
    exact (continuous_abs.continuousAt.comp hdetContinuous).eventually htarget
  obtain ⟨detOpen, hdetOpenSubset, hopenDet, htripleDet⟩ :=
    mem_nhds_iff.mp hdetEventually
  let patch : Set MassTriple :=
    localChart.source ∩ regularityOpen ∩ detOpen ∩
      interior iidMassTripleSupport
  have htriplePatch : triple ∈ patch :=
    ⟨⟨⟨htripleSource, htripleRegularity⟩, htripleDet⟩, htriple⟩
  have hopenPatch : IsOpen patch :=
    ((localChart.open_source.inter hopenRegularity).inter hopenDet).inter
      isOpen_interior
  have hpatchSupport : patch ⊆ iidMassTripleSupport := fun _ hnearby =>
    interior_subset hnearby.2
  have hpatchDifferentiable : DifferentiableOn Real chart patch := by
    intro nearby hnearby
    have hregular := hopenSubset hnearby.1.1.2
    obtain ⟨nearbyDerivative, hnearbyDerivative⟩ :=
      exists_hasStrictFDerivAt_actualThreeMassLiftedFrequencyChart
        fixed h₁₀ h₂₀ h₂₁ sign modes hregular.1 hregular.2.1
          hregular.2.2
    exact hnearbyDerivative.differentiableAt.differentiableWithinAt
  have hpatchInjective : InjOn chart patch := by
    apply localChart.injOn.mono
    intro nearby hnearby
    exact hnearby.1.1.1
  have himageOpen : IsOpen (chart '' patch) :=
    localChart.isOpen_image_of_subset_source hopenPatch
      (fun _ hnearby => hnearby.1.1.1)
  have hcenter : ((chart triple).1, 0) ∈ chart '' patch := by
    refine ⟨triple, htriplePatch, ?_⟩
    exact Prod.ext rfl hresonance
  obtain ⟨child, radius, hchildMeasurable, hchildPos,
      hchildFinite, hradius, hproduct⟩ :=
    exists_positiveArea_childRectangle_absoluteMismatchSublevel
      himageOpen (chart triple).1 hcenter
  let data : ActualThreeMassExactResonancePatchData
      fixed site₀ site₁ site₂ sign modes triple := {
    patch := patch
    child := child
    radius := radius
    base_mem := htriplePatch
    patch_open := hopenPatch
    patch_measurable := hopenPatch.measurableSet
    patch_support := hpatchSupport
    differentiable := hpatchDifferentiable
    injective := hpatchInjective
    child_measurable := hchildMeasurable
    child_volume_pos := hchildPos
    child_volume_ne_top := hchildFinite
    radius_pos := hradius
    product_subset_image := hproduct
  }
  refine ⟨data, detUpper, hdetUpper, ?_⟩
  intro point hpoint
  exact (hdetOpenSubset hpoint.1.2).le

/-! ## Reverse coarea gives the linear slope -/

/-- A determinant-bounded exact patch gives a positive linear small-ball
lower bound for the actual conditional iid three-mass mismatch law. -/
theorem ActualThreeMassExactResonancePatchData.exists_linearSmallBallLower
    {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₀ site₁ site₂ : Lattice.Site N}
    {sign : Fin 3 → InteractionSign}
    {modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))}
    {triple : MassTriple}
    (data : ActualThreeMassExactResonancePatchData
      fixed site₀ site₁ site₂ sign modes triple)
    {detUpper : Real} (hdetUpper : 0 < detUpper)
    (hdet : ∀ point ∈ data.patch,
      |(actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes point).det| ≤ detUpper) :
    ∃ constant : Real, 0 < constant ∧
      ∀ delta : Real, 0 < delta → delta ≤ data.radius →
        constant * delta ≤
          (Measure.map Prod.snd
            (Measure.map
              (actualThreeMassLiftedFrequencyChart
                fixed site₀ site₁ site₂ sign modes) iidMassTripleLaw)
            (absoluteMismatchSublevel delta)).toReal := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  let childVolume : Real :=
    (volume : Measure (Real × Real)).real data.child
  let constant : Real := 2 * childVolume / detUpper
  have hchildVolumePos : 0 < childVolume := by
    dsimp [childVolume, Measure.real]
    exact ENNReal.toReal_pos data.child_volume_pos.ne'
      data.child_volume_ne_top
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, hconstant, ?_⟩
  intro delta hdelta hdeltaRadius
  have hwindowSubset :
      absoluteMismatchSublevel delta ⊆
        absoluteMismatchSublevel data.radius := by
    intro mismatch hmismatch
    exact le_trans hmismatch hdeltaRadius
  have hproduct :
      data.child ×ˢ absoluteMismatchSublevel delta ⊆
        chart '' data.patch := by
    intro point hpoint
    exact data.product_subset_image ⟨hpoint.1, hwindowSubset hpoint.2⟩
  have hENN := childVolume_mul_targetVolume_le_actualIidMismatch
    fixed site₀ site₁ site₂ sign modes data.patch_measurable
    data.patch_support data.hasFDerivWithinAt data.injective detUpper hdet
    data.child_measurable (measurableSet_absoluteMismatchSublevel delta)
    hproduct
  rw [volume_absoluteMismatchSublevel] at hENN
  let mismatchLaw : Measure Real :=
    Measure.map Prod.snd (Measure.map chart iidMassTripleLaw)
  have hmismatchFinite :
      mismatchLaw (absoluteMismatchSublevel delta) ≠ ∞ := by
    dsimp [mismatchLaw]
    rw [Measure.map_apply measurable_snd
      (measurableSet_absoluteMismatchSublevel delta)]
    rw [Measure.map_apply
      (continuous_actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes).measurable
      ((measurableSet_absoluteMismatchSublevel delta).preimage
        measurable_snd)]
    have huniv : iidMassTripleLaw Set.univ = 1 := by
      simp [iidMassTripleLaw,
        ArchonPhysics.TwoParameterSpectralAveragingAtlas.iidMassPairLaw]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((measure_mono (subset_univ _)).trans_eq huniv)
  have hupperFinite :
      ENNReal.ofReal detUpper *
          mismatchLaw (absoluteMismatchSublevel delta) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmismatchFinite
  have hreal := ENNReal.toReal_mono hupperFinite hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hdetUpper.le,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hdelta.le)] at hreal
  rw [show (2 * childVolume / detUpper) * delta =
    (childVolume * (2 * delta)) / detUpper by ring]
  apply (div_le_iff₀ hdetUpper).2
  simpa [mismatchLaw, chart, childVolume, constant, Measure.real,
    mul_comm] using hreal

/-- Consumer-facing endpoint: every exact interior simple-positive point with
nonzero true Jacobian supplies a positive slope and a positive radius. -/
theorem exists_actualThreeMass_exactResonance_linearSmallBallLower
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r))
    (hJacobian :
      (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det ≠ 0)
    (hresonance :
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes triple).2 = 0) :
    ∃ constant radius : Real, 0 < constant ∧ 0 < radius ∧
      ∀ delta : Real, 0 < delta → delta ≤ radius →
        constant * delta ≤
          (Measure.map Prod.snd
            (Measure.map
              (actualThreeMassLiftedFrequencyChart
                fixed site₀ site₁ site₂ sign modes) iidMassTripleLaw)
            (absoluteMismatchSublevel delta)).toReal := by
  obtain ⟨data, detUpper, hdetUpper, hdet⟩ :=
    exists_actualThreeMassExactResonancePatchData_with_detUpper
      fixed h₁₀ h₂₀ h₂₁ sign modes triple htriple hsimple hpositive
        hJacobian hresonance
  obtain ⟨constant, hconstant, hbound⟩ :=
    data.exists_linearSmallBallLower hdetUpper hdet
  exact ⟨constant, data.radius, hconstant, data.radius_pos, hbound⟩

end

end ArchonPhysics.ActualThreeMassLiftedExactResonanceLinearSmallBall
