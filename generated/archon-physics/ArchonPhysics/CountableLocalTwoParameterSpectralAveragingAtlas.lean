import Mathlib.Data.Nat.Pairing
import ArchonPhysics.LocalTwoParameterSpectralAveragingAtlas

/-!
# Countably many locally regular two-parameter spectral charts

An actual random operator uses many choices of frozen environment, varied
sites, and ordered child modes.  This module lets those chart types be
indexed by `Nat`, while each chart is specified only through its regular
source and pointwise local inverse-function patches.  Lindelöf extraction is
performed separately for every chart type and `Nat.pair` flattens the two
countable indices into the atlas expected by spectral averaging.
-/

namespace ArchonPhysics.CountableLocalTwoParameterSpectralAveragingAtlas

open Set MeasureTheory
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas

noncomputable section

/-- A countable collection of chart types with pointwise regular patches
automatically yields the enumerated lower spectral-averaging atlas. -/
theorem volume_restrict_additiveTriangle_absolutelyContinuous_of_countable_local_iidMassPair_patches
    (W : Real) (source : Nat → Set (Real × Real))
    (chart : Nat → Real × Real → Real × Real)
    (target : Measure (Real × Real))
    (hlocal : ∀ chartIndex point, point ∈ source chartIndex →
      ∃ patch : Set (Real × Real),
        point ∈ patch ∧
        IsOpen patch ∧
        patch ⊆ iidMassPairSupport ∧
        DifferentiableOn Real (chart chartIndex) patch ∧
        InjOn (chart chartIndex) patch ∧
        Measure.map (chart chartIndex) (iidMassPairLaw.restrict patch) ≪
          target.restrict (additiveFrequencyTriangle W))
    (hcover : volume
      (additiveFrequencyTriangle W \
        ⋃ chartIndex, chart chartIndex '' source chartIndex) = 0) :
    volume.restrict (additiveFrequencyTriangle W) ≪
      target.restrict (additiveFrequencyTriangle W) := by
  classical
  have hlocalSubtype : ∀ chartIndex (point : source chartIndex),
      ∃ patch : Set (Real × Real),
        (point : Real × Real) ∈ patch ∧
        IsOpen patch ∧
        patch ⊆ iidMassPairSupport ∧
        DifferentiableOn Real (chart chartIndex) patch ∧
        InjOn (chart chartIndex) patch ∧
        Measure.map (chart chartIndex) (iidMassPairLaw.restrict patch) ≪
          target.restrict (additiveFrequencyTriangle W) :=
    fun chartIndex point => hlocal chartIndex point point.property
  choose localPatch hpoint hopen hsupport hdifferentiable hinjective hlower
    using hlocalSubtype
  let indexedPatch : (chartIndex : Nat) →
      Option (source chartIndex) → Set (Real × Real) :=
    fun chartIndex index =>
      match index with
      | none => ∅
      | some point => localPatch chartIndex point
  have hindexedOpen : ∀ chartIndex index,
      IsOpen (indexedPatch chartIndex index) := by
    intro chartIndex index
    cases index with
    | none => exact isOpen_empty
    | some point => exact hopen chartIndex point
  have hsourceCover : ∀ chartIndex,
      source chartIndex ⊆ ⋃ index, indexedPatch chartIndex index := by
    intro chartIndex point hpointSource
    exact mem_iUnion.mpr
      ⟨some ⟨point, hpointSource⟩,
        hpoint chartIndex ⟨point, hpointSource⟩⟩
  have hexistsEnumeration : ∀ chartIndex,
      ∃ enumeration : Nat → Option (source chartIndex),
        source chartIndex ⊆
          ⋃ localIndex, indexedPatch chartIndex (enumeration localIndex) := by
    intro chartIndex
    exact
      (HereditarilyLindelofSpace.isLindelof (source chartIndex)).indexed_countable_subcover
        (indexedPatch chartIndex) (hindexedOpen chartIndex)
          (hsourceCover chartIndex)
  choose enumeration henumeration using hexistsEnumeration
  let atlasChart : Nat → Real × Real → Real × Real :=
    fun n => chart (Nat.unpair n).1
  let atlasPatch : Nat → Set (Real × Real) :=
    fun n => indexedPatch (Nat.unpair n).1
      (enumeration (Nat.unpair n).1 (Nat.unpair n).2)
  have hatlasMeasurable (n : Nat) : MeasurableSet (atlasPatch n) :=
    (hindexedOpen _ _).measurableSet
  have hatlasSupport (n : Nat) : atlasPatch n ⊆ iidMassPairSupport := by
    cases hindex : enumeration (Nat.unpair n).1 (Nat.unpair n).2 with
    | none => simp [atlasPatch, indexedPatch, hindex]
    | some point =>
        simpa [atlasPatch, indexedPatch, hindex] using
          hsupport (Nat.unpair n).1 point
  have hatlasDifferentiable (n : Nat) :
      DifferentiableOn Real (atlasChart n) (atlasPatch n) := by
    cases hindex : enumeration (Nat.unpair n).1 (Nat.unpair n).2 with
    | none =>
        simpa [atlasChart, atlasPatch, indexedPatch, hindex] using
          (differentiableOn_empty :
            DifferentiableOn Real (chart (Nat.unpair n).1) ∅)
    | some point =>
        simpa [atlasChart, atlasPatch, indexedPatch, hindex] using
          hdifferentiable (Nat.unpair n).1 point
  have hatlasInjective (n : Nat) :
      InjOn (atlasChart n) (atlasPatch n) := by
    cases hindex : enumeration (Nat.unpair n).1 (Nat.unpair n).2 with
    | none => simp [atlasChart, atlasPatch, indexedPatch, hindex]
    | some point =>
        simpa [atlasChart, atlasPatch, indexedPatch, hindex] using
          hinjective (Nat.unpair n).1 point
  have hatlasLower (n : Nat) :
      Measure.map (atlasChart n) (iidMassPairLaw.restrict (atlasPatch n)) ≪
        target.restrict (additiveFrequencyTriangle W) := by
    cases hindex : enumeration (Nat.unpair n).1 (Nat.unpair n).2 with
    | none => simp [atlasChart, atlasPatch, indexedPatch, hindex]
    | some point =>
        simpa [atlasChart, atlasPatch, indexedPatch, hindex] using
          hlower (Nat.unpair n).1 point
  have himageCover :
      (⋃ chartIndex, chart chartIndex '' source chartIndex) ⊆
        ⋃ n, atlasChart n '' atlasPatch n := by
    intro frequencyPair hfrequency
    rcases mem_iUnion.mp hfrequency with ⟨chartIndex, massPair,
      hmassSource, rfl⟩
    rcases mem_iUnion.mp (henumeration chartIndex hmassSource) with
      ⟨localIndex, hmassPatch⟩
    refine mem_iUnion.mpr ⟨Nat.pair chartIndex localIndex, ?_⟩
    refine ⟨massPair, ?_, ?_⟩
    · change massPair ∈ indexedPatch
        (Nat.unpair (Nat.pair chartIndex localIndex)).1
        (enumeration (Nat.unpair (Nat.pair chartIndex localIndex)).1
          (Nat.unpair (Nat.pair chartIndex localIndex)).2)
      rw [Nat.unpair_pair]
      exact hmassPatch
    · simp [atlasChart, Nat.unpair_pair]
  have hatlasCover : volume
      (additiveFrequencyTriangle W \
        ⋃ n, atlasChart n '' atlasPatch n) = 0 := by
    apply measure_mono_null
      (t := additiveFrequencyTriangle W \
        ⋃ chartIndex, chart chartIndex '' source chartIndex)
    · intro frequencyPair hfrequency
      exact ⟨hfrequency.1, fun hsourceImage =>
        hfrequency.2 (himageCover hsourceImage)⟩
    · exact hcover
  exact
    volume_restrict_additiveTriangle_absolutelyContinuous_of_countable_iidMassPair_atlas
      W atlasPatch hatlasMeasurable hatlasSupport atlasChart
      hatlasDifferentiable hatlasInjective hatlasCover target hatlasLower

end

end ArchonPhysics.CountableLocalTwoParameterSpectralAveragingAtlas
