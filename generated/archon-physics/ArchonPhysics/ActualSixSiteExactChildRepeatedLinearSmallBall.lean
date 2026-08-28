import Mathlib.Analysis.Calculus.ImplicitContDiff
import ArchonPhysics.ActualChildRepeatedExactResonanceKernelBridge
import ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian

/-!
# An unconditional exact six-site child-repeated small-ball slope

The exact opposite-site six-cycle resonance already has simple spectrum,
positive parent and child frequencies, and a nonzero true two-mass frequency
Jacobian.  The reverse-coarea bridge formerly retained one local input: a
finite upper bound for that Jacobian on the inverse-function patch.

Here the missing bound is derived from the actual model.  The characteristic
equation implicit-function construction gives a `C¹` ordered-frequency branch
at every interior simple positive point.  Hence the true Jacobian determinant
is continuous at the exact resonance.  Shrinking the inverse-function patch
inside a determinant sublevel set supplies a positive finite upper bound while
retaining an open image and a product neighborhood of zero mismatch.

The endpoint is an unconditional linear small-ball lower bound for the exact
six-site iid two-mass mismatch law.  It is deliberately not a collision-weight
or thermodynamic-volume statement: positivity of the physical cubic weight at
this exact child-repeated point and transport to the full iid chain remain
separate model obligations.
-/

namespace ArchonPhysics.ActualSixSiteExactChildRepeatedLinearSmallBall

open ArchonPhysics
open ArchonPhysics.ActualChildRepeatedExactResonanceKernelBridge
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum
open ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function MeasureTheory Set

noncomputable section

/-! ## Local `C¹` regularity of the physical ordered spectral branches -/

/-- A simple ordered eigenvalue of the actual two-mass harmonic matrix is a
`C¹` function of the two raw masses at every interior point. -/
theorem contDiffAt_one_actualTwoMassOrderedEigenvalue
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (k : Fin (Fintype.card (Lattice.Site N))) :
    ContDiffAt Real 1
      (fun nearby => orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k) pair := by
  let A := twoSiteHarmonicHermitian fixed site₁ site₂ pair
  let lambda := orderedEigenvalue A k
  let characteristic :=
    actualTwoMassCharacteristicEquation fixed site₁ site₂
  let Dcharacteristic := fderiv Real characteristic (pair, lambda)
  have hcharacteristicC1 :
      ContDiffAt Real 1 characteristic (pair, lambda) :=
    contDiffAt_one_actualTwoMassCharacteristicEquation
      fixed hsite hpair lambda
  have hcharacteristicDeriv :
      HasFDerivAt characteristic Dcharacteristic (pair, lambda) :=
    hcharacteristicC1.differentiableAt_one.hasFDerivAt
  have hinclusion :
      HasFDerivAt (fun energy : Real => (pair, energy))
        (ContinuousLinearMap.inr Real (Real × Real) Real) lambda :=
    hasFDerivAt_prodMk_right pair lambda
  have hslice :
      HasFDerivAt (fun energy : Real => characteristic (pair, energy))
        (Dcharacteristic ∘L
          ContinuousLinearMap.inr Real (Real × Real) Real) lambda := by
    simpa [Function.comp_def] using
      hcharacteristicDeriv.comp lambda hinclusion
  have hpolynomial :
      HasFDerivAt (fun energy : Real => characteristic (pair, energy))
        (ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda)) lambda := by
    simpa [characteristic, actualTwoMassCharacteristicEquation, A, lambda]
      using ((Matrix.charpoly A.1).hasDerivAt lambda).hasFDerivAt
  have hpartial :
      Dcharacteristic ∘L
          ContinuousLinearMap.inr Real (Real × Real) Real =
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
  have hscalarEquiv :
      (scalarEquiv : Real →L[Real] Real) =
        ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda) := by
    apply ContinuousLinearMap.ext
    intro x
    simp [scalarEquiv, mul_comm]
  have hpartialInvertible :
      (Dcharacteristic ∘L
        ContinuousLinearMap.inr Real (Real × Real) Real).IsInvertible := by
    rw [hpartial]
    exact ⟨scalarEquiv, hscalarEquiv⟩
  let branch := hcharacteristicC1.implicitFunction
    (by norm_num) hpartialInvertible
  have hbranchC1 : ContDiffAt Real 1 branch pair := by
    exact hcharacteristicC1.contDiffAt_implicitFunction
      (by norm_num) hpartialInvertible
  let orderedBranch : Real × Real → Real := fun nearby =>
    orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k
  have horderedContinuous : Continuous orderedBranch :=
    (continuous_orderedEigenvalue k).comp
      (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)
  have horderedTendsto :
      Tendsto (fun nearby => (nearby, orderedBranch nearby))
        (nhds pair) (nhds (pair, lambda)) :=
    tendsto_id.prodMk_nhds horderedContinuous.continuousAt
  have hrootBase : characteristic (pair, lambda) = 0 :=
    charpoly_eval_orderedEigenvalue_eq_zero A k
  have hbranchEq : branch =ᶠ[nhds pair] orderedBranch := by
    have hiff := hcharacteristicC1.eventually_apply_eq_iff_implicitFunction
      (by norm_num) hpartialInvertible
    filter_upwards [horderedTendsto.eventually hiff] with nearby hnearby
    have hrootNearby :
        characteristic (nearby, orderedBranch nearby) = 0 :=
      charpoly_eval_orderedEigenvalue_eq_zero
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k
    exact hnearby.mp (hrootNearby.trans hrootBase.symm)
  exact hbranchC1.congr_of_eventuallyEq hbranchEq.symm

/-- A positive simple ordered frequency is `C¹` in the two raw masses. -/
theorem contDiffAt_one_actualTwoMassOrderedModeFrequency
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (k : Fin (Fintype.card (Lattice.Site N)))
    (hpositive : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) k) :
    ContDiffAt Real 1
      (fun nearby => orderedModeFrequency
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k) pair := by
  simpa [orderedModeFrequency] using
    (contDiffAt_one_actualTwoMassOrderedEigenvalue
      fixed hsite hpair hsimple k).sqrt (ne_of_gt hpositive)

/-- The selected actual two-frequency chart is locally `C¹`. -/
theorem contDiffAt_one_actualTwoMassChildFrequencyChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (hparent : 0 < orderedModeFrequency
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) parent)
    (hchild : 0 < orderedModeFrequency
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child) :
    ContDiffAt Real 1
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child) pair := by
  apply ContDiffAt.prodMk
  · exact contDiffAt_one_actualTwoMassOrderedModeFrequency
      fixed hsite hpair hsimple parent (Real.sqrt_pos.1 hparent)
  · exact contDiffAt_one_actualTwoMassOrderedModeFrequency
      fixed hsite hpair hsimple child (Real.sqrt_pos.1 hchild)

/-! ## Automatic local determinant ceiling and reverse coarea -/

/-- At an exact regular child-repeated point, the actual inverse-function
patch can be chosen together with a positive finite Jacobian ceiling. -/
theorem exists_actualTwoMassChildRepeatedExactPatchData_with_detUpper
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
    ∃ data : ActualTwoMassChildRepeatedExactPatchData
        fixed site₁ site₂ parent child pair,
      ∃ detUpper : Real, 0 < detUpper ∧
        ∀ point ∈ data.patch,
          |(actualTwoMassChildFrequencyJacobian
            fixed site₁ site₂ parent child point).det| ≤ detUpper := by
  let chart := actualTwoMassChildFrequencyChart
    fixed site₁ site₂ parent child
  let J := actualTwoMassChildFrequencyJacobian
    fixed site₁ site₂ parent child pair
  have hC1 : ContDiffAt Real 1 chart pair :=
    contDiffAt_one_actualTwoMassChildFrequencyChart
      fixed hsite parent child hpair hsimple hparent hchild
  have hdetLinear : LinearMap.det J.toLinearMap ≠ 0 := by
    simpa [ContinuousLinearMap.det] using hJacobian
  have hker : J.ker = ⊥ := by
    by_contra hne
    exact hdetLinear (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hinjectiveJ : Function.Injective J := LinearMap.ker_eq_bot.mp hker
  have hsurjectiveJ : Function.Surjective J :=
    LinearMap.injective_iff_surjective.mp hinjectiveJ
  have hrange : J.range = ⊤ := LinearMap.range_eq_top.mpr hsurjectiveJ
  let Jequiv : (Real × Real) ≃L[Real] (Real × Real) :=
    ContinuousLinearEquiv.ofBijective J hker hrange
  have hJequiv : (Jequiv : (Real × Real) →L[Real] (Real × Real)) = J :=
    ContinuousLinearEquiv.coe_ofBijective J hker hrange
  have hderiv : HasFDerivAt chart
      (Jequiv : (Real × Real) →L[Real] (Real × Real)) pair := by
    rw [hJequiv]
    simpa [J, chart, actualTwoMassChildFrequencyJacobian] using
      hC1.differentiableAt_one.hasFDerivAt
  let localChart : OpenPartialHomeomorph (Real × Real) (Real × Real) :=
    hC1.toOpenPartialHomeomorph chart hderiv (by norm_num)
  have hpairSource : pair ∈ localChart.source :=
    hC1.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  obtain ⟨regularitySet, hregularityNhds, hregularity⟩ :=
    hC1.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨regularityOpen, hopenSubset, hopenRegularity, hpairRegularity⟩ :=
    mem_nhds_iff.mp hregularityNhds
  let detUpper : Real := |J.det| + 1
  have hdetUpper : 0 < detUpper := by
    dsimp [detUpper]
    positivity
  have hdetContinuous : ContinuousAt
      (fun nearby =>
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child nearby).det) pair := by
    change ContinuousAt
      (fun nearby => (fderiv Real chart nearby).det) pair
    exact ContinuousLinearMap.continuous_det.continuousAt.comp
      (hC1.continuousAt_fderiv (by norm_num))
  have hdetEventually : ∀ᶠ nearby in nhds pair,
      |(actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child nearby).det| < detUpper := by
    have htarget :
        ∀ᶠ value in nhds
          |(actualTwoMassChildFrequencyJacobian
            fixed site₁ site₂ parent child pair).det|,
          value < detUpper :=
      Iio_mem_nhds (show
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child pair).det| < detUpper by
          simp [detUpper, J])
    exact (continuous_abs.continuousAt.comp hdetContinuous).eventually htarget
  obtain ⟨detOpen, hdetOpenSubset, hopenDet, hpairDet⟩ :=
    mem_nhds_iff.mp hdetEventually
  let patch : Set (Real × Real) :=
    localChart.source ∩ regularityOpen ∩ detOpen ∩
      interior iidMassPairSupport
  have hpairPatch : pair ∈ patch :=
    ⟨⟨⟨hpairSource, hpairRegularity⟩, hpairDet⟩, hpair⟩
  have hopenPatch : IsOpen patch :=
    ((localChart.open_source.inter hopenRegularity).inter hopenDet).inter
      isOpen_interior
  have hpatchMeasurable : MeasurableSet patch := hopenPatch.measurableSet
  have hpatchSupport : patch ⊆ iidMassPairSupport := fun _ hnearby =>
    interior_subset hnearby.2
  have hpatchDifferentiable : DifferentiableOn Real chart patch := by
    apply (hregularity.mono ?_).differentiableOn (by norm_num)
    intro nearby hnearby
    exact hopenSubset hnearby.1.1.2
  have hpatchInjective : InjOn chart patch := by
    apply localChart.injOn.mono
    intro nearby hnearby
    exact hnearby.1.1.1
  have himageOpen : IsOpen (chart '' patch) :=
    localChart.isOpen_image_of_subset_source hopenPatch
      (fun _ hnearby => hnearby.1.1.1)
  let transformedImage : Set (Real × Real) :=
    childFrequencyMismatchLinearEquiv '' (chart '' patch)
  have htransformedOpen : IsOpen transformedImage := by
    change IsOpen (childFrequencyMismatchHomeomorph '' (chart '' patch))
    exact childFrequencyMismatchHomeomorph.isOpen_image.2 himageOpen
  have hcenter : ((chart pair).2, 0) ∈ transformedImage := by
    refine ⟨chart pair, ⟨pair, hpairPatch, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · simpa [childFrequencyMismatchLinearEquiv,
        childRepeatedDecayMismatch] using hresonance
  obtain ⟨childSet, radius, hchildMeasurable, hchildPos,
      hchildFinite, hradius, hrectangle⟩ :=
    exists_positive_childInterval_absoluteMismatchSublevel
      htransformedOpen (chart pair).2 hcenter
  let data : ActualTwoMassChildRepeatedExactPatchData
      fixed site₁ site₂ parent child pair := {
    patch := patch
    childSet := childSet
    radius := radius
    base_mem := hpairPatch
    patch_open := hopenPatch
    patch_measurable := hpatchMeasurable
    patch_support := hpatchSupport
    differentiable := hpatchDifferentiable
    injective := hpatchInjective
    childSet_measurable := hchildMeasurable
    childSet_volume_pos := hchildPos
    childSet_volume_ne_top := hchildFinite
    radius_pos := hradius
    rectangle_subset_image := hrectangle
  }
  refine ⟨data, detUpper, hdetUpper, ?_⟩
  intro point hpoint
  exact (hdetOpenSubset hpoint.1.2).le

/-- Any exact regular child-repeated point therefore supplies a linear
small-ball slope with no auxiliary determinant-bound premise. -/
theorem exists_actualTwoMassChildRepeated_linearSmallBallLower
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
    ∃ constant radius : Real, 0 < constant ∧ 0 < radius ∧
      ∀ delta : Real, 0 < delta → delta ≤ radius →
        constant * delta ≤
          (Measure.map childRepeatedDecayMismatch
            (Measure.map
              (actualTwoMassChildFrequencyChart
                fixed site₁ site₂ parent child) iidMassPairLaw)
            (absoluteMismatchSublevel delta)).toReal := by
  obtain ⟨data, detUpper, hdetUpper, hdet⟩ :=
    exists_actualTwoMassChildRepeatedExactPatchData_with_detUpper
      fixed hsite parent child pair hpair hsimple hparent hchild
        hJacobian hresonance
  obtain ⟨constant, hconstant, hbound⟩ :=
    data.exists_linearSmallBallLower hdetUpper hdet
  exact ⟨constant, data.radius, hconstant, data.radius_pos, hbound⟩

/-! ## Exact six-site specialization -/

/-- The actual opposite-site six-cycle has an unconditional positive linear
small-ball slope for its exact child-repeated iid two-mass mismatch law. -/
theorem exists_oppositeSixSite_exactChildRepeated_linearSmallBallLower :
    ∃ constant radius : Real, 0 < constant ∧ 0 < radius ∧
      ∀ delta : Real, 0 < delta → delta ≤ radius →
        constant * delta ≤
          (Measure.map childRepeatedDecayMismatch
            (Measure.map
              (actualTwoMassChildFrequencyChart frozenUnitMassSix
                (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3)
              iidMassPairLaw)
            (absoluteMismatchSublevel delta)).toReal := by
  obtain ⟨s, hs, hresonance, hsimple, hparent, hchild, hJacobian⟩ :=
    exists_interior_simple_positive_jacobian_oppositeChildRepeated_exactResonance
  exact exists_actualTwoMassChildRepeated_linearSmallBallLower
    frozenUnitMassSix (by decide : (0 : Lattice.Site 6) ≠ 3)
    0 3 (oppositeMassPair s) (oppositeMassPair_mem_interior hs)
    (by simpa [oppositeSixSiteHarmonic] using hsimple)
    (by simpa [oppositeSixSiteHarmonic] using hparent)
    (by simpa [oppositeSixSiteHarmonic] using hchild)
    hJacobian hresonance

end

end ArchonPhysics.ActualSixSiteExactChildRepeatedLinearSmallBall
