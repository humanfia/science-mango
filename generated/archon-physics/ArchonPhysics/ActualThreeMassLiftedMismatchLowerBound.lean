import ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
import ArchonPhysics.QuantitativeJacobianReversePushforward

/-!
# Reverse bounds for the actual lifted mismatch chart

Upper coarea estimates give absolute continuity but cannot prove that the
on-shell density is positive.  This module records the complementary local
statement for the genuine random-mass harmonic chart.

First, normalized Lebesgue mass sampling dominates unnormalized Lebesgue
measure on its support cube.  Second, the reverse area formula shows that if
an injective actual chart patch contains a product of a positive-area child
set and a mismatch target in its image, then the mismatch pushforward gives
that target positive mass.

The product-image premise is the honest remaining local positivity input.  A
resonance-centered inverse-function patch can supply it when the lifted
Jacobian is nonzero at an interior resonant point.  This file does not assert
that such points exist uniformly over volumes or mode triples.
-/

namespace ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.QuantitativeJacobianReversePushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Normalized uniform mass sampling dominates ordinary Lebesgue measure on
the frozen support interval. -/
theorem volume_restrict_massSupport_le_massCoordinateLaw :
    (volume : Measure Real).restrict massSupport ≤ massCoordinateLaw := by
  unfold massCoordinateLaw ProbabilityTheory.cond
  have hnormalization :
      1 ≤ ((volume : Measure Real) massSupport)⁻¹ := by
    simp [massSupport, massLower, massUpper, Real.volume_Icc]
    norm_num
  rw [Measure.le_iff']
  intro target
  rw [Measure.smul_apply]
  simpa only [one_mul, smul_eq_mul] using
    (mul_le_mul_left hnormalization
      ((volume : Measure Real).restrict massSupport target))

/-- The iid mass-triple law quantitatively dominates volume restricted to
the full support cube. -/
theorem volume_restrict_iidMassTripleSupport_le_iidMassTripleLaw :
    (volume : Measure MassTriple).restrict iidMassTripleSupport ≤
      iidMassTripleLaw := by
  have hone := volume_restrict_massSupport_le_massCoordinateLaw
  have hpair := Measure.prod_mono hone hone
  have htriple := Measure.prod_mono hpair hone
  simpa [iidMassTripleSupport, iidMassPairSupport, iidMassTripleLaw,
    iidMassPairLaw, Measure.volume_eq_prod, Measure.prod_restrict] using
      htriple

/-- Restricting to a patch inside the iid cube preserves the quantitative
source lower bound. -/
theorem volume_restrict_patch_le_iidMassTripleLaw_restrict
    {patch : Set MassTriple} (hpatchSupport : patch ⊆ iidMassTripleSupport) :
    (volume : Measure MassTriple).restrict patch ≤
      iidMassTripleLaw.restrict patch := by
  have h := Measure.restrict_mono_measure
    volume_restrict_iidMassTripleSupport_le_iidMassTripleLaw patch
  rw [Measure.restrict_restrict_of_subset hpatchSupport] at h
  exact h

/-- Reverse coarea after projecting the actual lifted chart to mismatch.
The child set may be any measurable planar set; the target may be any
measurable mismatch set. -/
theorem sourceDensity_mul_childVolume_mul_targetVolume_le_actualMismatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {patch : Set MassTriple} (hpatch : MeasurableSet patch)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        (actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point) patch point)
    (hinjective : InjOn
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) patch)
    (detUpper : Real)
    (hdet : ∀ point ∈ patch,
      |(actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes point).det| ≤ detUpper)
    (source : Measure MassTriple) (sourceDensity : ENNReal)
    (hsource : sourceDensity •
      (volume : Measure MassTriple).restrict patch ≤ source)
    {child : Set (Real × Real)} (_hchild : MeasurableSet child)
    {target : Set Real} (htarget : MeasurableSet target)
    (hproductImage :
      child ×ˢ target ⊆
        actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes '' patch) :
    sourceDensity * (volume : Measure (Real × Real)) child *
        (volume : Measure Real) target ≤
      ENNReal.ofReal detUpper *
        Measure.map Prod.snd
          (Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes) source) target := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  have hreverse :
      sourceDensity •
          (volume : Measure MassTriple).restrict (chart '' patch) ≤
        ENNReal.ofReal detUpper • Measure.map chart source :=
    sourceDensity_smul_volume_restrict_image_le_detUpper_smul_map
      (volume : Measure MassTriple) hpatch chart hchart
      (fun point =>
        actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point)
      hderivative hinjective detUpper hdet source sourceDensity hsource
  have hpreimage :
      MeasurableSet (Prod.snd ⁻¹' target : Set MassTriple) :=
    htarget.preimage measurable_snd
  have hreverseApply :=
    hreverse (Prod.snd ⁻¹' target : Set MassTriple)
  have hproductSubset :
      child ×ˢ target ⊆
        (Prod.snd ⁻¹' target : Set MassTriple) ∩ chart '' patch := by
    intro point hpoint
    exact ⟨hpoint.2, hproductImage hpoint⟩
  have hvolumeMono :
      (volume : Measure MassTriple) (child ×ˢ target) ≤
        (volume : Measure MassTriple)
          ((Prod.snd ⁻¹' target : Set MassTriple) ∩ chart '' patch) :=
    measure_mono hproductSubset
  have hproductVolume :
      (volume : Measure MassTriple) (child ×ˢ target) =
        (volume : Measure (Real × Real)) child *
          (volume : Measure Real) target := by
    change ((volume : Measure (Real × Real)).prod
      (volume : Measure Real)) (child ×ˢ target) = _
    rw [Measure.prod_prod]
  calc
    sourceDensity * (volume : Measure (Real × Real)) child *
          (volume : Measure Real) target =
        sourceDensity *
          (volume : Measure MassTriple) (child ×ˢ target) := by
      rw [hproductVolume]
      rw [mul_assoc]
    _ ≤ sourceDensity *
          (volume : Measure MassTriple)
            ((Prod.snd ⁻¹' target : Set MassTriple) ∩ chart '' patch) :=
      mul_le_mul_right hvolumeMono sourceDensity
    _ ≤ ENNReal.ofReal detUpper *
          Measure.map chart source (Prod.snd ⁻¹' target) := by
      simpa only [Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply hpreimage] using hreverseApply
    _ = ENNReal.ofReal detUpper *
        Measure.map Prod.snd (Measure.map chart source) target := by
      rw [Measure.map_apply measurable_snd htarget]

/-- Bare iid specialization: a product contained in an actual chart image
has its volume controlled by the true mismatch marginal. -/
theorem childVolume_mul_targetVolume_le_actualIidMismatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {patch : Set MassTriple} (hpatch : MeasurableSet patch)
    (hpatchSupport : patch ⊆ iidMassTripleSupport)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        (actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point) patch point)
    (hinjective : InjOn
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) patch)
    (detUpper : Real)
    (hdet : ∀ point ∈ patch,
      |(actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes point).det| ≤ detUpper)
    {child : Set (Real × Real)} (hchild : MeasurableSet child)
    {target : Set Real} (htarget : MeasurableSet target)
    (hproductImage :
      child ×ˢ target ⊆
        actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes '' patch) :
    (volume : Measure (Real × Real)) child *
        (volume : Measure Real) target ≤
      ENNReal.ofReal detUpper *
        Measure.map Prod.snd
          (Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes) iidMassTripleLaw) target := by
  have hsource :
      (1 : ENNReal) • (volume : Measure MassTriple).restrict patch ≤
        iidMassTripleLaw := by
    simpa using
      (volume_restrict_patch_le_iidMassTripleLaw_restrict hpatchSupport).trans
        (Measure.restrict_le_self)
  simpa only [one_mul] using
    sourceDensity_mul_childVolume_mul_targetVolume_le_actualMismatch
      fixed site₀ site₁ site₂ sign modes hpatch hderivative hinjective
      detUpper hdet iidMassTripleLaw 1 hsource hchild htarget hproductImage

/-- Positive child area and positive target length force positive actual
mismatch mass on every such resonance-centered product patch. -/
theorem actualIidMismatch_apply_ne_zero_of_productImage
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {patch : Set MassTriple} (hpatch : MeasurableSet patch)
    (hpatchSupport : patch ⊆ iidMassTripleSupport)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        (actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point) patch point)
    (hinjective : InjOn
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) patch)
    (detUpper : Real)
    (hdet : ∀ point ∈ patch,
      |(actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes point).det| ≤ detUpper)
    {child : Set (Real × Real)} (hchild : MeasurableSet child)
    (hchildPositive : 0 < (volume : Measure (Real × Real)) child)
    {target : Set Real} (htarget : MeasurableSet target)
    (htargetPositive : 0 < (volume : Measure Real) target)
    (hproductImage :
      child ×ˢ target ⊆
        actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes '' patch) :
    Measure.map Prod.snd
        (Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes) iidMassTripleLaw) target ≠ 0 := by
  intro hzero
  have hbound :=
    childVolume_mul_targetVolume_le_actualIidMismatch
      fixed site₀ site₁ site₂ sign modes hpatch hpatchSupport
      hderivative hinjective detUpper hdet hchild htarget hproductImage
  rw [hzero, mul_zero] at hbound
  exact (not_le_of_gt
    (ENNReal.mul_pos hchildPositive.ne' htargetPositive.ne')) hbound

end

end ArchonPhysics.ActualThreeMassLiftedMismatchLowerBound
