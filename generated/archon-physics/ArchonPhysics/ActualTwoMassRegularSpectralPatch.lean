import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.NormDet
import ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability

/-!
# Regular patches for the actual two-mass frequency chart

For the genuine periodic random-mass harmonic matrix, this module combines
the two simple positive frequency derivatives and applies the strict inverse
function theorem.  Hence no abstract chart-smoothness or separate C1
hypothesis is needed: simple positive physical modes and a nonzero determinant
of the actual two-mass Jacobian produce an open injective atlas patch.
-/

namespace ArchonPhysics.ActualTwoMassRegularSpectralPatch

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function Set

noncomputable section

/-- At an interior simple-spectrum point, two positive actual ordered
frequencies form a strictly differentiable two-dimensional chart. -/
theorem exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple :
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N)))
    (hpositive₁ : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child₁)
    (hpositive₂ : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child₂) :
    ∃ derivative : (Real × Real) →L[Real] (Real × Real),
      HasStrictFDerivAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂)
        derivative pair := by
  obtain ⟨derivative₁, hderivative₁⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
      fixed hsite hpair hsimple child₁ hpositive₁
  obtain ⟨derivative₂, hderivative₂⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
      fixed hsite hpair hsimple child₂ hpositive₂
  refine ⟨derivative₁.prod derivative₂, ?_⟩
  convert hderivative₁.prodMk hderivative₂ using 1 <;>
    rfl

/-- For the real random-mass harmonic matrix, a nondegenerate actual
two-frequency Jacobian yields an open measurable injective patch contained
in the iid mass square.  Differentiability on the whole patch follows point
by point from persistence of the simple spectrum and positivity. -/
theorem exists_actualTwoMassChildFrequency_regularPatch_of_simpleSpectrum
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple :
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (hpositive₁ : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child₁)
    (hpositive₂ : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child₂)
    (hJacobian :
      (actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ child₁ child₂ pair).det ≠ 0) :
    ∃ patch : Set (Real × Real),
      pair ∈ patch ∧
      IsOpen patch ∧
      MeasurableSet patch ∧
      patch ⊆ iidMassPairSupport ∧
      DifferentiableOn Real
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂) patch ∧
      InjOn
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂) patch := by
  let chart :=
    actualTwoMassChildFrequencyChart fixed site₁ site₂ child₁ child₂
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
      fixed hsite hpair hsimple child₁ child₂ hpositive₁ hpositive₂
  have hactualDerivative :
      actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ child₁ child₂ pair = derivative := by
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
  have hchild₁Continuous : Continuous fun nearby =>
      orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child₁ :=
    (continuous_orderedEigenvalue child₁).comp
      (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)
  have hchild₂Continuous : Continuous fun nearby =>
      orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child₂ :=
    (continuous_orderedEigenvalue child₂).comp
      (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)
  let regularitySet : Set (Real × Real) :=
    {nearby |
      nearby ∈ interior iidMassPairSupport ∧
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) ∧
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child₁ ∧
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child₂}
  have hregularityNhds : regularitySet ∈ nhds pair := by
    have hpositive₁Eventually : ∀ᶠ nearby in nhds pair,
        0 < orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child₁ :=
      hchild₁Continuous.continuousAt.eventually
        (isOpen_Ioi.mem_nhds hpositive₁)
    have hpositive₂Eventually : ∀ᶠ nearby in nhds pair,
        0 < orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) child₂ :=
      hchild₂Continuous.continuousAt.eventually
        (isOpen_Ioi.mem_nhds hpositive₂)
    filter_upwards [isOpen_interior.mem_nhds hpair,
      eventually_simple_twoSiteHarmonicHermitian
        fixed site₁ site₂ pair hsimple,
      hpositive₁Eventually, hpositive₂Eventually] with
        nearby hsupport hsimpleNearby hpositive₁Nearby hpositive₂Nearby
    exact ⟨hsupport, hsimpleNearby, hpositive₁Nearby, hpositive₂Nearby⟩
  obtain ⟨regularityOpen, hopenSubset, hopen, hpairOpen⟩ :=
    mem_nhds_iff.mp hregularityNhds
  let patch : Set (Real × Real) := localChart.source ∩ regularityOpen
  refine ⟨patch, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hpairSource, hpairOpen⟩
  · exact localChart.open_source.inter hopen
  · exact (localChart.open_source.inter hopen).measurableSet
  · intro nearby hnearby
    exact interior_subset (hopenSubset hnearby.2).1
  · intro nearby hnearby
    have hregular := hopenSubset hnearby.2
    obtain ⟨nearbyDerivative, hnearbyDerivative⟩ :=
      exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
        fixed hsite hregular.1 hregular.2.1 child₁ child₂
          hregular.2.2.1 hregular.2.2.2
    exact hnearbyDerivative.differentiableAt.differentiableWithinAt
  · apply localChart.injOn.mono
    intro nearby hnearby
    exact hnearby.1

end

end ArchonPhysics.ActualTwoMassRegularSpectralPatch
