import ArchonPhysics.QuantitativeJacobianPushforward

/-!
# Quantitative reverse Jacobian pushforward bounds

The usual lower-Jacobian estimate controls the pushforward of source volume
from above.  For spectral lower-reference estimates one needs the converse
orientation: an upper bound on the absolute Jacobian controls target volume
on the chart image by the pushforward of source volume.

The proof is the area formula on each measurable source slice
`patch ∩ chart ⁻¹' targetSet`.  It is formulated entirely with `ENNReal`
measure scalars.  Thus neither the Jacobian upper bound nor the source-density
scalar needs to be nonzero or finite; in particular the cases
`detUpper = 0` and `sourceDensity = ∞` are covered without cancellation.
-/

namespace ArchonPhysics.QuantitativeJacobianReversePushforward

open Set MeasureTheory
open scoped ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- An upper bound on the absolute Jacobian gives a reverse pushforward
estimate on the chart image.  No positivity assumption on `detUpper` is
needed: if the patch is nonempty, the displayed determinant bound already
forces it to be nonnegative; if the patch is empty, both sides vanish. -/
theorem volume_restrict_image_le_detUpper_smul_map_volume_restrict
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {patch : Set E} (hpatch : MeasurableSet patch)
    (chart : E -> E) (hchart : Measurable chart)
    (derivative : E -> E →L[Real] E)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt chart (derivative point) patch point)
    (hinjective : InjOn chart patch)
    (detUpper : Real)
    (hdet : ∀ point ∈ patch,
      |(derivative point).det| <= detUpper) :
    μ.restrict (chart '' patch) <=
      ENNReal.ofReal detUpper • Measure.map chart (μ.restrict patch) := by
  rw [Measure.le_iff]
  intro targetSet htargetSet
  let sourceSet : Set E := patch ∩ chart ⁻¹' targetSet
  have hsourceSet : MeasurableSet sourceSet :=
    hpatch.inter (htargetSet.preimage hchart)
  have himage : targetSet ∩ chart '' patch = chart '' sourceSet := by
    ext targetPoint
    constructor
    · rintro ⟨htargetPoint, sourcePoint, hsourcePoint, rfl⟩
      exact ⟨sourcePoint, ⟨hsourcePoint, htargetPoint⟩, rfl⟩
    · rintro ⟨sourcePoint, ⟨hsourcePoint, htargetPoint⟩, rfl⟩
      exact ⟨htargetPoint, sourcePoint, hsourcePoint, rfl⟩
  have harea :
      μ (chart '' sourceSet) =
        ∫⁻ point in sourceSet,
          ENNReal.ofReal |(derivative point).det| ∂μ := by
    exact (lintegral_abs_det_fderiv_eq_addHaar_image μ hsourceSet
      (fun point hpoint =>
        (hderivative point hpoint.1).mono inter_subset_left)
      (hinjective.mono inter_subset_left)).symm
  have hdetIntegral :
      (∫⁻ point in sourceSet,
          ENNReal.ofReal |(derivative point).det| ∂μ) <=
        ENNReal.ofReal detUpper * μ sourceSet := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono' hsourceSet
    intro point hpoint
    exact ENNReal.ofReal_le_ofReal (hdet point hpoint.1)
  rw [Measure.restrict_apply htargetSet, Measure.smul_apply,
    Measure.map_apply hchart htargetSet,
    Measure.restrict_apply (htargetSet.preimage hchart), himage, harea]
  simpa [sourceSet, inter_comm] using hdetIntegral

/-- If a source measure dominates `sourceDensity` times patch volume, the
same density times target volume on the chart image is dominated by
`detUpper` times the source pushforward.  The statement permits arbitrary
measures and every `sourceDensity : ENNReal`, including `∞`; no cancellation
or finiteness side condition is used. -/
theorem sourceDensity_smul_volume_restrict_image_le_detUpper_smul_map
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {patch : Set E} (hpatch : MeasurableSet patch)
    (chart : E -> E) (hchart : Measurable chart)
    (derivative : E -> E →L[Real] E)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt chart (derivative point) patch point)
    (hinjective : InjOn chart patch)
    (detUpper : Real)
    (hdet : ∀ point ∈ patch,
      |(derivative point).det| <= detUpper)
    (source : Measure E) (sourceDensity : ENNReal)
    (hsource : sourceDensity • μ.restrict patch <= source) :
    sourceDensity • μ.restrict (chart '' patch) <=
      ENNReal.ofReal detUpper • Measure.map chart source := by
  calc
    sourceDensity • μ.restrict (chart '' patch) <=
        sourceDensity •
          (ENNReal.ofReal detUpper •
            Measure.map chart (μ.restrict patch)) :=
      smul_mono_right sourceDensity
        (volume_restrict_image_le_detUpper_smul_map_volume_restrict
          μ hpatch chart hchart derivative hderivative hinjective detUpper hdet)
    _ = ENNReal.ofReal detUpper •
        Measure.map chart (sourceDensity • μ.restrict patch) := by
      rw [Measure.map_smul, smul_smul, smul_smul]
      exact mul_comm sourceDensity (ENNReal.ofReal detUpper) ▸ rfl
    _ <= ENNReal.ofReal detUpper • Measure.map chart source :=
      smul_mono_right (ENNReal.ofReal detUpper)
        (Measure.map_mono hsource hchart)

end

end ArchonPhysics.QuantitativeJacobianReversePushforward
