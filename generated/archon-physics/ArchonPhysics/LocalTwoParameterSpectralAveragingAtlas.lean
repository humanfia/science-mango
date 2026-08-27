import Mathlib.Topology.Compactness.Lindelof
import ArchonPhysics.TwoParameterSpectralAveragingAtlas

/-!
# Local-to-countable two-parameter spectral atlases

This module removes the bookkeeping assumption that a model proof must
provide an already enumerated family of regular mass patches.  In the real
two-mass parameter plane, local regular patches automatically have a
countable subcover.  The resulting countable atlas feeds directly into the
lower spectral-averaging theorem.

The two genuinely model-facing obligations remain visible: the regular
source frequencies cover the physical additive triangle almost everywhere,
and every selected local patch satisfies the weighted lower-averaging
comparison with the target child trace.
-/

namespace ArchonPhysics.LocalTwoParameterSpectralAveragingAtlas

open Set MeasureTheory
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas

noncomputable section

/-- Local regular mass charts automatically assemble into a countable atlas.

The index set of all source points is generally uncountable.  Since the real
mass plane is hereditarily Lindelöf, the open local patches have a countable
subcover.  No countability or explicit enumeration is required from the
model proof. -/
theorem volume_restrict_additiveTriangle_absolutelyContinuous_of_local_iidMassPair_patches
    (W : Real) (source : Set (Real × Real))
    (chart : Real × Real → Real × Real)
    (target : Measure (Real × Real))
    (hlocal : ∀ point ∈ source,
      ∃ patch : Set (Real × Real),
        point ∈ patch ∧
        IsOpen patch ∧
        patch ⊆ iidMassPairSupport ∧
        DifferentiableOn Real chart patch ∧
        InjOn chart patch ∧
        Measure.map chart (iidMassPairLaw.restrict patch) ≪
          target.restrict (additiveFrequencyTriangle W))
    (hcover : volume
      (additiveFrequencyTriangle W \ chart '' source) = 0) :
    volume.restrict (additiveFrequencyTriangle W) ≪
      target.restrict (additiveFrequencyTriangle W) := by
  classical
  have hlocalSubtype : ∀ point : source,
      ∃ patch : Set (Real × Real),
        (point : Real × Real) ∈ patch ∧
        IsOpen patch ∧
        patch ⊆ iidMassPairSupport ∧
        DifferentiableOn Real chart patch ∧
        InjOn chart patch ∧
        Measure.map chart (iidMassPairLaw.restrict patch) ≪
          target.restrict (additiveFrequencyTriangle W) :=
    fun point => hlocal point point.property
  choose localPatch hpoint hopen hsupport hdifferentiable hinjective hlower
    using hlocalSubtype
  let indexedPatch : Option source → Set (Real × Real)
    | none => ∅
    | some point => localPatch point
  have hindexedOpen : ∀ index, IsOpen (indexedPatch index) := by
    intro index
    cases index with
    | none => exact isOpen_empty
    | some point => exact hopen point
  have hsourceCover : source ⊆ ⋃ index, indexedPatch index := by
    intro point hpointSource
    exact mem_iUnion.mpr
      ⟨some ⟨point, hpointSource⟩, hpoint ⟨point, hpointSource⟩⟩
  obtain ⟨enumeration, henumeration⟩ :=
    (HereditarilyLindelofSpace.isLindelof source).indexed_countable_subcover
      indexedPatch hindexedOpen hsourceCover
  have hpatchMeasurable (n : Nat) :
      MeasurableSet (indexedPatch (enumeration n)) :=
    (hindexedOpen (enumeration n)).measurableSet
  have hpatchSupport (n : Nat) :
      indexedPatch (enumeration n) ⊆ iidMassPairSupport := by
    cases hindex : enumeration n with
    | none => simp [indexedPatch]
    | some point =>
        simpa [indexedPatch, hindex] using hsupport point
  have hpatchDifferentiable (n : Nat) :
      DifferentiableOn Real chart (indexedPatch (enumeration n)) := by
    cases hindex : enumeration n with
    | none =>
        simpa [indexedPatch, hindex] using
          (differentiableOn_empty : DifferentiableOn Real chart ∅)
    | some point =>
        simpa [indexedPatch, hindex] using hdifferentiable point
  have hpatchInjective (n : Nat) :
      InjOn chart (indexedPatch (enumeration n)) := by
    cases hindex : enumeration n with
    | none => simp [indexedPatch]
    | some point =>
        simpa [indexedPatch, hindex] using hinjective point
  have hpatchLower (n : Nat) :
      Measure.map chart
          (iidMassPairLaw.restrict (indexedPatch (enumeration n))) ≪
        target.restrict (additiveFrequencyTriangle W) := by
    cases hindex : enumeration n with
    | none => simp [indexedPatch]
    | some point =>
        simpa [indexedPatch, hindex] using hlower point
  have himageCover :
      chart '' source ⊆ ⋃ n, chart '' indexedPatch (enumeration n) := by
    rintro frequencyPair ⟨massPair, hmassSource, rfl⟩
    rcases mem_iUnion.mp (henumeration hmassSource) with ⟨n, hn⟩
    exact mem_iUnion.mpr ⟨n, ⟨massPair, hn, rfl⟩⟩
  have hcountableCover : volume
      (additiveFrequencyTriangle W \
        ⋃ n, chart '' indexedPatch (enumeration n)) = 0 := by
    apply measure_mono_null
      (t := additiveFrequencyTriangle W \ chart '' source)
    · intro frequencyPair hfrequency
      exact ⟨hfrequency.1, fun hsourceImage =>
        hfrequency.2 (himageCover hsourceImage)⟩
    · exact hcover
  exact
    volume_restrict_additiveTriangle_absolutelyContinuous_of_countable_iidMassPair_atlas
      W (fun n => indexedPatch (enumeration n))
      hpatchMeasurable hpatchSupport (fun _ => chart)
      hpatchDifferentiable hpatchInjective hcountableCover target hpatchLower

end

end ArchonPhysics.LocalTwoParameterSpectralAveragingAtlas
