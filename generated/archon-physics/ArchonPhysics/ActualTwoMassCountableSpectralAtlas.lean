import ArchonPhysics.ActualTwoMassRegularSpectralPatch
import ArchonPhysics.CountableLocalTwoParameterSpectralAveragingAtlas

/-!
# Countable atlas of actual two-mass random-lattice charts

This module specializes local-to-countable spectral averaging to the genuine
mass-weighted harmonic matrices.  A chart source contains exactly the
interior mass pairs where the actual spectrum is simple, the two selected
frequencies are positive, and the true Fréchet Jacobian determinant is
nonzero.  The inverse-function patch and all its regularity properties are
then theorems, rather than atlas inputs.

What remains model-facing is explicit: the images of these regular sources
must cover the additive triangle almost everywhere, and the actual weighted
child trace must dominate every local iid-mass pushforward.
-/

namespace ArchonPhysics.ActualTwoMassCountableSpectralAtlas

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.ActualTwoMassRegularSpectralPatch
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CountableLocalTwoParameterSpectralAveragingAtlas
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas

noncomputable section

/-- The regular parameter source of one genuine two-mass child-frequency
chart. -/
def actualTwoMassRegularSource
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N))) :
    Set (Real × Real) :=
  {pair |
    pair ∈ interior iidMassPairSupport ∧
    SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) ∧
    0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child₁ ∧
    0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) child₂ ∧
    (actualTwoMassChildFrequencyJacobian
      fixed site₁ site₂ child₁ child₂ pair).det ≠ 0}

/-- For countably many actual chart choices, pointwise nondegeneracy supplies
all local inverse-function data and Lindelöf extraction supplies the
enumerated atlas.

Only `hlocalLower` is the weighted local spectral estimate; it is stated on
the concrete actual chart and cannot be confused with an abstract smoothness
or injectivity assumption. -/
theorem volume_restrict_additiveTriangle_absolutelyContinuous_of_actualTwoMass_regularSources
    {N : Nat} [NeZero N]
    (fixed : Nat → Lattice.PositiveMassConfig N)
    (site₁ site₂ : Nat → Lattice.Site N)
    (hsite : ∀ chartIndex, site₁ chartIndex ≠ site₂ chartIndex)
    (child₁ child₂ : Nat → Fin (Fintype.card (Lattice.Site N)))
    (W : Real) (target : Measure (Real × Real))
    (hlocalLower : ∀ chartIndex point,
      point ∈ actualTwoMassRegularSource
        (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
          (child₁ chartIndex) (child₂ chartIndex) →
      ∀ patch : Set (Real × Real),
        point ∈ patch →
        IsOpen patch →
        patch ⊆ iidMassPairSupport →
        DifferentiableOn Real
          (actualTwoMassChildFrequencyChart
            (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
              (child₁ chartIndex) (child₂ chartIndex)) patch →
        InjOn
          (actualTwoMassChildFrequencyChart
            (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
              (child₁ chartIndex) (child₂ chartIndex)) patch →
        Measure.map
            (actualTwoMassChildFrequencyChart
              (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
                (child₁ chartIndex) (child₂ chartIndex))
            (iidMassPairLaw.restrict patch) ≪
          target.restrict (additiveFrequencyTriangle W))
    (hcover : volume
      (additiveFrequencyTriangle W \
        ⋃ chartIndex,
          actualTwoMassChildFrequencyChart
              (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
                (child₁ chartIndex) (child₂ chartIndex) ''
            actualTwoMassRegularSource
              (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
                (child₁ chartIndex) (child₂ chartIndex)) = 0) :
    volume.restrict (additiveFrequencyTriangle W) ≪
      target.restrict (additiveFrequencyTriangle W) := by
  let source : Nat → Set (Real × Real) := fun chartIndex =>
    actualTwoMassRegularSource
      (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
        (child₁ chartIndex) (child₂ chartIndex)
  let chart : Nat → Real × Real → Real × Real := fun chartIndex =>
    actualTwoMassChildFrequencyChart
      (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
        (child₁ chartIndex) (child₂ chartIndex)
  apply
    volume_restrict_additiveTriangle_absolutelyContinuous_of_countable_local_iidMassPair_patches
      W source chart target
  · intro chartIndex point hpoint
    change point ∈ actualTwoMassRegularSource
      (fixed chartIndex) (site₁ chartIndex) (site₂ chartIndex)
        (child₁ chartIndex) (child₂ chartIndex) at hpoint
    rcases hpoint with
      ⟨hinterior, hsimple, hpositive₁, hpositive₂, hdet⟩
    obtain ⟨patch, hpointPatch, hopen, _hmeasurable, hsupport,
        hdifferentiable, hinjective⟩ :=
      exists_actualTwoMassChildFrequency_regularPatch_of_simpleSpectrum
        (fixed chartIndex) (hsite chartIndex)
        (child₁ chartIndex) (child₂ chartIndex) point hinterior hsimple
          hpositive₁ hpositive₂ hdet
    refine ⟨patch, hpointPatch, hopen, hsupport,
      hdifferentiable, hinjective, ?_⟩
    exact hlocalLower chartIndex point
      ⟨hinterior, hsimple, hpositive₁, hpositive₂, hdet⟩ patch
        hpointPatch hopen hsupport hdifferentiable hinjective
  · simpa [source, chart] using hcover

end

end ArchonPhysics.ActualTwoMassCountableSpectralAtlas
