import Mathlib.MeasureTheory.Function.Jacobian
import ArchonPhysics.FiniteMassPolynomialAvoidance
import ArchonPhysics.ContinuousThreeWaveBalanceRigidity

/-!
# Two-parameter spectral-averaging atlases

This module isolates the weakest null-set form of a lower two-parameter
spectral-averaging argument that is sufficient for the child-frequency trace.

The two iid mass coordinates have a law equivalent to Lebesgue measure on
their compact support square.  Consequently, on any measurable patch of that
square, a differentiable injective frequency chart transports target-null
sets to Lebesgue-null sets whenever its averaged pushforward is absolutely
continuous with respect to the target trace.  A countable collection of such
patches whose images cover the additive triangle up to a Lebesgue-null set
therefore proves the required reverse absolute continuity.

This is the measure-theoretic part of the lower spectral-averaging mechanism
in del Rio--Martinez--Schulz-Baldes, *Spectral averaging techniques for Jacobi
matrices* (2008).  Their model-specific Prüfer/coarea estimates are not assumed
here.  Likewise, the multiparameter upper estimates of Aizenman--Warzel,
*On the Joint Distribution of Energy Levels of Random Schroedinger Operators*
(2008), do not by themselves supply the lower domination used below.
-/

namespace ArchonPhysics.TwoParameterSpectralAveragingAtlas

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.RandomEnsemble

noncomputable section

/-- The support square of two independently averaged raw masses. -/
def iidMassPairSupport : Set (Real × Real) :=
  massSupport ×ˢ massSupport

/-- The product law of two independently averaged raw masses. -/
def iidMassPairLaw : Measure (Real × Real) :=
  massCoordinateLaw.prod massCoordinateLaw

/-- On its support interval, Lebesgue measure is absolutely continuous with
respect to the normalized uniform mass law.  Together with the already proved
opposite direction, this says that the two measures have the same null sets
there. -/
theorem volume_restrict_massSupport_absolutelyContinuous_massCoordinateLaw :
    volume.restrict massSupport ≪ massCoordinateLaw := by
  unfold massCoordinateLaw
  apply (Measure.AbsolutelyContinuous.refl
    (volume.restrict massSupport)).smul_right
  simp [massSupport, massLower, massUpper, Real.volume_Icc]

/-- The two-dimensional iid mass law dominates Lebesgue null sets throughout
the full compact mass-support square. -/
theorem volume_restrict_iidMassPairSupport_absolutelyContinuous_iidMassPairLaw :
    volume.restrict iidMassPairSupport ≪ iidMassPairLaw := by
  rw [iidMassPairSupport, iidMassPairLaw, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  exact
    volume_restrict_massSupport_absolutelyContinuous_massCoordinateLaw.prod
      volume_restrict_massSupport_absolutelyContinuous_massCoordinateLaw

/-- Restricting both measures to an arbitrary patch inside the mass square
preserves the lower null-set comparison. -/
theorem volume_restrict_patch_absolutelyContinuous_iidMassPairLaw_restrict
    {patch : Set (Real × Real)}
    (hpatchSupport : patch ⊆ iidMassPairSupport) :
    volume.restrict patch ≪ iidMassPairLaw.restrict patch := by
  have h :=
    volume_restrict_iidMassPairSupport_absolutelyContinuous_iidMassPairLaw.restrict
      patch
  rw [Measure.restrict_restrict_of_subset hpatchSupport] at h
  exact h

/-- Local lower spectral averaging on one differentiable mass patch.

The sole model-facing input is `hlower`: the averaged chart pushforward gives
zero mass only where the target trace does.  Differentiability sends the
resulting Lebesgue-null parameter preimage to a Lebesgue-null frequency image.
Injectivity is used only to make the chart image Borel measurable; no explicit
Radon--Nikodym density or quantitative Jacobian lower bound is required. -/
theorem volume_restrict_chartImage_absolutelyContinuous_of_iidMassPair_lowerAveraging
    {patch : Set (Real × Real)} (hpatchMeasurable : MeasurableSet patch)
    (hpatchSupport : patch ⊆ iidMassPairSupport)
    (chart : Real × Real → Real × Real)
    (hchart : DifferentiableOn Real chart patch)
    (hchartInj : InjOn chart patch)
    (target : Measure (Real × Real))
    (hlower : Measure.map chart (iidMassPairLaw.restrict patch) ≪ target) :
    volume.restrict (chart '' patch) ≪ target := by
  have himageMeasurable : MeasurableSet (chart '' patch) :=
    hpatchMeasurable.image_of_continuousOn_injOn hchart.continuousOn
      hchartInj
  intro exceptional htargetNull
  have hchartAe : AEMeasurable chart (iidMassPairLaw.restrict patch) := by
    apply ContinuousOn.aemeasurable₀ hchart.continuousOn
      hpatchMeasurable.nullMeasurableSet
  have hpreimageMass :
      (iidMassPairLaw.restrict patch) (chart ⁻¹' exceptional) = 0 :=
    Measure.preimage_null_of_map_null hchartAe (hlower htargetNull)
  have hpreimageVolume :
      (volume.restrict patch) (chart ⁻¹' exceptional) = 0 :=
    volume_restrict_patch_absolutelyContinuous_iidMassPairLaw_restrict
      hpatchSupport hpreimageMass
  have hsourceNull : volume (patch ∩ chart ⁻¹' exceptional) = 0 := by
    rw [Measure.restrict_apply₀'
      hpatchMeasurable.nullMeasurableSet] at hpreimageVolume
    simpa [inter_comm] using hpreimageVolume
  have himageNull :
      volume (chart '' (patch ∩ chart ⁻¹' exceptional)) = 0 := by
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume (hchart.mono inter_subset_left) hsourceNull
  rw [Measure.restrict_apply₀' himageMeasurable.nullMeasurableSet]
  apply measure_mono_null
    (t := chart '' (patch ∩ chart ⁻¹' exceptional))
  · rintro frequencyPair ⟨hpairExceptional, massPair, hmassPatch, rfl⟩
    exact ⟨massPair, ⟨hmassPatch, hpairExceptional⟩, rfl⟩
  · exact himageNull

/-- A countable lower-spectral-averaging atlas gives exactly the reverse
absolute continuity required by the canonical child-trace adapter.

`hcover` is the geometric/full-rank content: almost every point of the
physical additive triangle lies in some chart image.  `hlower` is the weighted
spectral content: each iid-mass averaged patch is dominated in null sets by
the target trace. -/
theorem volume_restrict_additiveTriangle_absolutelyContinuous_of_countable_iidMassPair_atlas
    (W : Real) (patch : Nat → Set (Real × Real))
    (hpatchMeasurable : ∀ n, MeasurableSet (patch n))
    (hpatchSupport : ∀ n, patch n ⊆ iidMassPairSupport)
    (chart : Nat → Real × Real → Real × Real)
    (hchart : ∀ n, DifferentiableOn Real (chart n) (patch n))
    (hchartInj : ∀ n, InjOn (chart n) (patch n))
    (hcover : volume
      (additiveFrequencyTriangle W \ ⋃ n, chart n '' patch n) = 0)
    (target : Measure (Real × Real))
    (hlower : ∀ n,
      Measure.map (chart n) (iidMassPairLaw.restrict (patch n)) ≪
        target.restrict (additiveFrequencyTriangle W)) :
    volume.restrict (additiveFrequencyTriangle W) ≪
      target.restrict (additiveFrequencyTriangle W) := by
  have hpatchAc (n : Nat) :
      volume.restrict (chart n '' patch n) ≪
        target.restrict (additiveFrequencyTriangle W) :=
    volume_restrict_chartImage_absolutelyContinuous_of_iidMassPair_lowerAveraging
      (hpatchMeasurable n) (hpatchSupport n) (chart n)
      (hchart n) (hchartInj n) _ (hlower n)
  intro exceptional htargetNull
  have hpatchNull (n : Nat) :
      volume (exceptional ∩ chart n '' patch n) = 0 := by
    have hn := hpatchAc n htargetNull
    rw [Measure.restrict_apply₀'
      ((hpatchMeasurable n).image_of_continuousOn_injOn
        (hchart n).continuousOn (hchartInj n)).nullMeasurableSet] at hn
    exact hn
  have hunionNull :
      volume (⋃ n, exceptional ∩ chart n '' patch n) = 0 :=
    measure_iUnion_null hpatchNull
  have htotalNull :
      volume (exceptional ∩ additiveFrequencyTriangle W) = 0 := by
    apply measure_mono_null
      (t := (additiveFrequencyTriangle W \ ⋃ n, chart n '' patch n) ∪
        ⋃ n, exceptional ∩ chart n '' patch n)
    · intro frequencyPair hpair
      by_cases hinCharts : frequencyPair ∈ ⋃ n, chart n '' patch n
      · right
        rcases mem_iUnion.mp hinCharts with ⟨n, hn⟩
        exact mem_iUnion.mpr ⟨n, hpair.1, hn⟩
      · left
        exact ⟨hpair.2, hinCharts⟩
    · exact measure_union_null hcover hunionNull
  rw [Measure.restrict_apply₀'
    (isClosed_additiveFrequencyTriangle W).measurableSet.nullMeasurableSet]
  exact htotalNull

end

end ArchonPhysics.TwoParameterSpectralAveragingAtlas
