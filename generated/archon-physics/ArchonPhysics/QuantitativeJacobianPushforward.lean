import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Quantitative Jacobian bounds for spectral pushforwards

The qualitative spectral atlas only needs a nonzero determinant to preserve
null sets.  Uniform large-time estimates require a quantitative version.  On
an injective patch where the absolute determinant is bounded below by a
positive number, the area formula bounds the pushforward of restricted
Lebesgue measure by the reciprocal determinant times Lebesgue measure.

The theorem is dimension-independent and therefore applies both to two-mass
child charts and to three-mass lifted `(child pair, mismatch)` charts.
-/

namespace ArchonPhysics.QuantitativeJacobianPushforward

open Set MeasureTheory
open scoped ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- A positive lower bound on the true Jacobian determinant gives an explicit
upper density bound for the pushforward of Lebesgue measure restricted to an
injective differentiable patch. -/
theorem map_volume_restrict_le_invDet_smul_volume
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {patch : Set E} (hpatch : MeasurableSet patch)
    (chart : E → E) (hchart : Measurable chart)
    (derivative : E → E →L[Real] E)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt chart (derivative point) patch point)
    (hinjective : InjOn chart patch)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ patch,
      detLower ≤ |(derivative point).det|) :
    Measure.map chart (μ.restrict patch) ≤
      (ENNReal.ofReal detLower)⁻¹ • μ := by
  rw [Measure.le_iff]
  intro targetSet htargetSet
  rw [Measure.map_apply hchart htargetSet,
    Measure.smul_apply]
  let sourceSet : Set E := patch ∩ chart ⁻¹' targetSet
  have hsourceSet : MeasurableSet sourceSet :=
    hpatch.inter (htargetSet.preimage hchart)
  have himageSubset : chart '' sourceSet ⊆ targetSet := by
    rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
    exact hsourcePoint.2
  have harea :
      (∫⁻ point in sourceSet,
          ENNReal.ofReal |(derivative point).det| ∂μ) =
        μ (chart '' sourceSet) := by
    exact lintegral_abs_det_fderiv_eq_addHaar_image μ hsourceSet
      (fun point hpoint =>
        (hderivative point hpoint.1).mono inter_subset_left)
      (hinjective.mono inter_subset_left)
  have hdetIntegral :
      ENNReal.ofReal detLower * μ sourceSet ≤
        ∫⁻ point in sourceSet,
          ENNReal.ofReal |(derivative point).det| ∂μ := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono' hsourceSet
    intro point hpoint
    exact ENNReal.ofReal_le_ofReal (hdet point hpoint.1)
  have hmul :
      ENNReal.ofReal detLower * μ sourceSet ≤ μ targetSet := by
    calc
      ENNReal.ofReal detLower * μ sourceSet ≤
          ∫⁻ point in sourceSet,
            ENNReal.ofReal |(derivative point).det| ∂μ := hdetIntegral
      _ = μ (chart '' sourceSet) := harea
      _ ≤ μ targetSet := measure_mono himageSubset
  have hdetZero : ENNReal.ofReal detLower ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hdetLower
  have hdetTop : ENNReal.ofReal detLower ≠ ∞ := ENNReal.ofReal_ne_top
  have hsourceBound :
      μ sourceSet ≤
        (ENNReal.ofReal detLower)⁻¹ * μ targetSet := by
    rw [← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl hdetZero) (Or.inl hdetTop)).2 (by simpa [mul_comm] using hmul)
  rw [Measure.restrict_apply (htargetSet.preimage hchart)]
  simpa [sourceSet, inter_comm] using hsourceBound

/-- The same estimate for any source measure already dominated by a scalar
multiple of restricted Lebesgue measure. -/
theorem map_le_smul_volume_of_le_volume_restrict_of_det_lower
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {patch : Set E} (hpatch : MeasurableSet patch)
    (chart : E → E) (hchart : Measurable chart)
    (derivative : E → E →L[Real] E)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt chart (derivative point) patch point)
    (hinjective : InjOn chart patch)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ patch,
      detLower ≤ |(derivative point).det|)
    (source : Measure E) (sourceDensity : ENNReal)
    (hsource : source ≤ sourceDensity • μ.restrict patch) :
    Measure.map chart source ≤
      (sourceDensity * (ENNReal.ofReal detLower)⁻¹) •
        μ := by
  calc
    Measure.map chart source ≤
        Measure.map chart (sourceDensity • μ.restrict patch) :=
      Measure.map_mono hsource hchart
    _ = sourceDensity • Measure.map chart (μ.restrict patch) := by
      rw [Measure.map_smul]
    _ ≤ sourceDensity •
        ((ENNReal.ofReal detLower)⁻¹ • μ) :=
      smul_mono_right sourceDensity
        (map_volume_restrict_le_invDet_smul_volume μ hpatch chart hchart
          derivative hderivative hinjective hdetLower hdet)
    _ = (sourceDensity * (ENNReal.ofReal detLower)⁻¹) •
        μ := by rw [mul_smul]

end

end ArchonPhysics.QuantitativeJacobianPushforward
