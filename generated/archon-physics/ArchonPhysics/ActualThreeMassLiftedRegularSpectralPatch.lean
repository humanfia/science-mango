import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.NormDet
import ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability

/-!
# Regular patches for the actual three-mass lifted spectral chart

At an interior point with simple spectrum and three positive selected modes,
the genuine child-child-mismatch chart is strictly differentiable.  A
nonzero determinant therefore gives an open measurable injective patch,
without an abstract chart-smoothness premise.
-/

namespace ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function Set

noncomputable section

/-- For the real random-mass harmonic matrix, a nondegenerate lifted
Jacobian yields an open injective patch inside the iid mass cube. -/
theorem exists_actualThreeMassLiftedFrequency_regularPatch_of_simpleSpectrum
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
        fixed site₀ site₁ site₂ sign modes triple).det ≠ 0) :
    ∃ patch : Set MassTriple,
      triple ∈ patch ∧
      IsOpen patch ∧
      MeasurableSet patch ∧
      patch ⊆ iidMassTripleSupport ∧
      DifferentiableOn Real
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes) patch ∧
      InjOn
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes) patch := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualThreeMassLiftedFrequencyChart
      fixed h₁₀ h₂₀ h₂₁ sign modes htriple hsimple hpositive
  have hactualDerivative :
      actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes triple = derivative := by
    simpa [chart, actualThreeMassLiftedFrequencyJacobian] using
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
  obtain ⟨regularityOpen, hopenSubset, hopen, htripleOpen⟩ :=
    mem_nhds_iff.mp hregularityNhds
  let patch : Set MassTriple := localChart.source ∩ regularityOpen
  refine ⟨patch, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨htripleSource, htripleOpen⟩
  · exact localChart.open_source.inter hopen
  · exact (localChart.open_source.inter hopen).measurableSet
  · intro nearby hnearby
    exact interior_subset (hopenSubset hnearby.2).1
  · intro nearby hnearby
    have hregular := hopenSubset hnearby.2
    obtain ⟨nearbyDerivative, hnearbyDerivative⟩ :=
      exists_hasStrictFDerivAt_actualThreeMassLiftedFrequencyChart
        fixed h₁₀ h₂₀ h₂₁ sign modes hregular.1 hregular.2.1
          hregular.2.2
    exact hnearbyDerivative.differentiableAt.differentiableWithinAt
  · apply localChart.injOn.mono
    intro nearby hnearby
    exact hnearby.1

end

end ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
