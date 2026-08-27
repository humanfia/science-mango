import ArchonPhysics.ActualTwoMassCountableSpectralAtlas

/-!
# Cross-volume actual two-mass spectral atlas

Thermodynamic spectral coverage cannot be represented by charts from one
fixed finite lattice.  This module packages one actual chart together with
its own positive volume, frozen mass environment, varied sites, and selected
ordered child modes.  A `Nat`-indexed family may therefore use increasing
volumes and genuinely cover a continuum limit.

For every chart specification, the regular source still refers to the true
finite-volume random-mass harmonic matrix and its true Fréchet Jacobian.  The
cross-volume theorem delegates all inverse-function and countable-subcover
work to the already proved actual atlas.
-/

namespace ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.ActualTwoMassCountableSpectralAtlas
open ArchonPhysics.ActualTwoMassRegularSpectralPatch
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CountableLocalTwoParameterSpectralAveragingAtlas
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas

noncomputable section

/-- One genuine two-mass chart, including its own finite lattice volume. -/
structure ActualTwoMassChartSpec where
  volume : Nat
  volume_pos : 0 < volume
  fixed : Lattice.PositiveMassConfig volume
  site₁ : Lattice.Site volume
  site₂ : Lattice.Site volume
  site_ne : site₁ ≠ site₂
  child₁ : Fin volume
  child₂ : Fin volume

namespace ActualTwoMassChartSpec

/-- The actual ordered child-frequency chart of a cross-volume spec. -/
def chart (spec : ActualTwoMassChartSpec) :
    Real × Real → Real × Real := by
  letI : NeZero spec.volume := ⟨Nat.ne_of_gt spec.volume_pos⟩
  let child₁ : Fin (Fintype.card (Lattice.Site spec.volume)) :=
    Fin.cast (ZMod.card spec.volume).symm spec.child₁
  let child₂ : Fin (Fintype.card (Lattice.Site spec.volume)) :=
    Fin.cast (ZMod.card spec.volume).symm spec.child₂
  exact actualTwoMassChildFrequencyChart spec.fixed spec.site₁ spec.site₂
    child₁ child₂

/-- The interior simple-positive, true-Jacobian-regular source of a spec. -/
def regularSource (spec : ActualTwoMassChartSpec) : Set (Real × Real) := by
  letI : NeZero spec.volume := ⟨Nat.ne_of_gt spec.volume_pos⟩
  let child₁ : Fin (Fintype.card (Lattice.Site spec.volume)) :=
    Fin.cast (ZMod.card spec.volume).symm spec.child₁
  let child₂ : Fin (Fintype.card (Lattice.Site spec.volume)) :=
    Fin.cast (ZMod.card spec.volume).symm spec.child₂
  exact actualTwoMassRegularSource spec.fixed spec.site₁ spec.site₂
    child₁ child₂

end ActualTwoMassChartSpec

/-- Cross-volume actual regular sources produce the lower child-trace
comparison once their images cover the physical triangle and the weighted
local lower-averaging estimate is established on each inverse-function
patch. -/
theorem volume_additiveTriangle_ac_of_crossVolume_actualTwoMass_regularSources
    (spec : Nat → ActualTwoMassChartSpec)
    (W : Real) (target : Measure (Real × Real))
    (hlocalLower : ∀ chartIndex point,
      point ∈ (spec chartIndex).regularSource →
      ∀ patch : Set (Real × Real),
        point ∈ patch →
        IsOpen patch →
        patch ⊆ iidMassPairSupport →
        DifferentiableOn Real (spec chartIndex).chart patch →
        InjOn (spec chartIndex).chart patch →
        Measure.map (spec chartIndex).chart
            (iidMassPairLaw.restrict patch) ≪
          target.restrict (additiveFrequencyTriangle W))
    (hcover : volume
      (additiveFrequencyTriangle W \
        ⋃ chartIndex,
          (spec chartIndex).chart '' (spec chartIndex).regularSource) = 0) :
    volume.restrict (additiveFrequencyTriangle W) ≪
      target.restrict (additiveFrequencyTriangle W) := by
  apply
    volume_restrict_additiveTriangle_absolutelyContinuous_of_countable_local_iidMassPair_patches
      W (fun chartIndex => (spec chartIndex).regularSource)
        (fun chartIndex => (spec chartIndex).chart) target
  · intro chartIndex point hpoint
    let current := spec chartIndex
    let _ : NeZero current.volume := ⟨Nat.ne_of_gt current.volume_pos⟩
    let currentChild₁ : Fin (Fintype.card (Lattice.Site current.volume)) :=
      Fin.cast (ZMod.card current.volume).symm current.child₁
    let currentChild₂ : Fin (Fintype.card (Lattice.Site current.volume)) :=
      Fin.cast (ZMod.card current.volume).symm current.child₂
    have hpointActual : point ∈ actualTwoMassRegularSource
        current.fixed current.site₁ current.site₂
          currentChild₁ currentChild₂ := by
      simpa [current, ActualTwoMassChartSpec.regularSource] using hpoint
    rcases hpointActual with
      ⟨hinterior, hsimple, hpositive₁, hpositive₂, hdet⟩
    obtain ⟨patch, hpointPatch, hopen, _hmeasurable, hsupport,
        hdifferentiable, hinjective⟩ :=
      exists_actualTwoMassChildFrequency_regularPatch_of_simpleSpectrum
        current.fixed current.site_ne currentChild₁ currentChild₂ point
          hinterior hsimple hpositive₁ hpositive₂ hdet
    have hdifferentiableSpec :
        DifferentiableOn Real current.chart patch := by
      simpa [ActualTwoMassChartSpec.chart] using hdifferentiable
    have hinjectiveSpec : InjOn current.chart patch := by
      simpa [ActualTwoMassChartSpec.chart] using hinjective
    refine ⟨patch, hpointPatch, hopen, hsupport,
      ?_, ?_, ?_⟩
    · simpa [current] using hdifferentiableSpec
    · simpa [current] using hinjectiveSpec
    · exact hlocalLower chartIndex point hpoint patch hpointPatch hopen
        hsupport (by simpa [current] using hdifferentiableSpec)
          (by simpa [current] using hinjectiveSpec)
  · exact hcover

end

end ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
