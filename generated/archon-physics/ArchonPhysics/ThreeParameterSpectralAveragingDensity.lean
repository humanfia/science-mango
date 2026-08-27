import Mathlib.MeasureTheory.Function.Jacobian
import ArchonPhysics.TwoParameterSpectralAveragingAtlas

/-!
# Quantitative three-parameter spectral averaging

This file is the measure-theoretic three-dimensional counterpart of the
two-parameter null-set atlas.  The parameter space is
`((m₀, m₁), m₂)`.  Its iid law is bounded by an explicit multiple of
three-dimensional Lebesgue measure.

The main change-of-variables theorem is quantitative.  On a measurable
injective patch, a positive lower bound for the absolute determinant of the
true Frechet derivative turns a density upper bound on the parameter law
into a density upper bound on the chart pushforward.  Thus its model-facing
input is a Jacobian estimate, not an absolute-continuity assumption on the
desired spectral law.
-/

namespace ArchonPhysics.ThreeParameterSpectralAveragingDensity

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open scoped ENNReal

noncomputable section

/-- Three raw mass coordinates, associated to the nested product convention
used by the lifted `(child pair, mismatch)` observable. -/
abbrev MassTriple := (Real × Real) × Real

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Compact support of three independently averaged raw masses. -/
def iidMassTripleSupport : Set MassTriple :=
  iidMassPairSupport ×ˢ massSupport

/-- Product law of three independently averaged raw masses. -/
def iidMassTripleLaw : Measure MassTriple :=
  iidMassPairLaw.prod massCoordinateLaw

/-- The normalized one-mass law is bounded by the deliberately coarse
constant `3` times Lebesgue measure. -/
theorem massCoordinateLaw_le_three_smul_volume :
    massCoordinateLaw ≤ (3 : ENNReal) • (volume : Measure Real) := by
  unfold massCoordinateLaw ProbabilityTheory.cond
  have hnormalization :
      ((volume : Measure Real) massSupport)⁻¹ ≤ (3 : ENNReal) := by
    simp [massSupport, massLower, massUpper, Real.volume_Icc]
    have hdifference : (6 / 5 : Real) - 4 / 5 = 2 / 5 := by norm_num
    rw [hdifference]
    rw [← ENNReal.ofReal_inv_of_pos
      (by norm_num : (0 : Real) < 2 / 5)]
    norm_num [ENNReal.ofReal_div_of_pos]
    apply (ENNReal.div_le_iff
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ∞)).2
    norm_num
  rw [Measure.le_iff']
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul hnormalization (Measure.restrict_le_self s)
    (by positivity) (by positivity)

/-- Consequently the actual three-mass iid law has an explicit global
Lebesgue density ceiling `27`. -/
theorem iidMassTripleLaw_le_twentySeven_smul_volume :
    iidMassTripleLaw ≤
      (27 : ENNReal) • (volume : Measure MassTriple) := by
  unfold iidMassTripleLaw iidMassPairLaw
  have hone := massCoordinateLaw_le_three_smul_volume
  have hprod := (Measure.prod_mono hone hone)
  have htriple := Measure.prod_mono hprod hone
  have hconstant :
      (3 : ENNReal) * ((3 : ENNReal) * (3 : ENNReal)) = 27 := by
    norm_num
  simpa [Measure.volume_eq_prod, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, mul_assoc, hconstant] using htriple

/-- Quantitative local three-dimensional change of variables.

If `source ≤ K dx`, the chart is injective on `patch`, and the absolute
Jacobian is at least `delta` there, then
`delta · chart₍(source|patch) ≤ K dx`.  This multiplicative form avoids
any division convention at `delta = 0`; applications with a positive
Jacobian lower bound may divide afterwards. -/
theorem smul_map_restrict_le_smul_volume_of_det_fderiv_lower
    (source : Measure MassTriple) (K delta : ENNReal)
    (hsource : source ≤ K • (volume : Measure MassTriple))
    (patch : Set MassTriple) (hpatch : MeasurableSet patch)
    (chart : MassTriple → MassTriple) (hchart : Measurable chart)
    (hdifferentiable : ∀ x ∈ patch, DifferentiableAt Real chart x)
    (hinjective : InjOn chart patch)
    (hdet : ∀ x ∈ patch,
      delta ≤ ENNReal.ofReal
        |(fderiv Real chart x).det|) :
    delta • Measure.map chart (source.restrict patch) ≤
      K • (volume : Measure MassTriple) := by
  rw [Measure.le_iff]
  intro target htarget
  let preimagePatch : Set MassTriple := patch ∩ chart ⁻¹' target
  have hpreimagePatch : MeasurableSet preimagePatch :=
    hpatch.inter (htarget.preimage hchart)
  have hmapApply :
      Measure.map chart (source.restrict patch) target =
        source preimagePatch := by
    rw [Measure.map_apply hchart htarget,
      Measure.restrict_apply (htarget.preimage hchart)]
    simp [preimagePatch, inter_comm]
  have hsourceApply : source preimagePatch ≤
      K * (volume : Measure MassTriple) preimagePatch := by
    have := hsource preimagePatch
    rw [Measure.smul_apply] at this
    exact this
  have himageSubset : chart '' preimagePatch ⊆ target := by
    rintro y ⟨x, hx, rfl⟩
    exact hx.2
  have hvolumeExpansion :
      delta * (volume : Measure MassTriple) preimagePatch ≤
        (volume : Measure MassTriple) (chart '' preimagePatch) := by
    calc
      delta * (volume : Measure MassTriple) preimagePatch =
          ∫⁻ _x in preimagePatch, delta
            ∂(volume : Measure MassTriple) := by simp
      _ ≤ ∫⁻ x in preimagePatch,
          ENNReal.ofReal |(fderiv Real chart x).det|
            ∂(volume : Measure MassTriple) := by
        apply setLIntegral_mono' hpreimagePatch
        intro x hx
        exact hdet x hx.1
      _ = (volume : Measure MassTriple) (chart '' preimagePatch) := by
        apply lintegral_abs_det_fderiv_eq_addHaar_image
          (volume : Measure MassTriple) hpreimagePatch
        · intro x hx
          exact (hdifferentiable x hx.1).hasFDerivAt.hasFDerivWithinAt
        · exact hinjective.mono inter_subset_left
  rw [Measure.smul_apply, Measure.smul_apply, hmapApply]
  calc
    delta * source preimagePatch ≤
        delta * (K * (volume : Measure MassTriple) preimagePatch) := by
      gcongr
    _ = K * (delta * (volume : Measure MassTriple) preimagePatch) := by
      ac_rfl
    _ ≤ K * (volume : Measure MassTriple) (chart '' preimagePatch) := by
      gcongr
    _ ≤ K * (volume : Measure MassTriple) target := by
      gcongr

/-- Specialization to the concrete iid mass triple law. -/
theorem smul_map_iidMassTripleLaw_restrict_le_twentySeven_smul_volume
    (delta : ENNReal)
    (patch : Set MassTriple) (hpatch : MeasurableSet patch)
    (chart : MassTriple → MassTriple) (hchart : Measurable chart)
    (hdifferentiable : ∀ x ∈ patch, DifferentiableAt Real chart x)
    (hinjective : InjOn chart patch)
    (hdet : ∀ x ∈ patch,
      delta ≤ ENNReal.ofReal |(fderiv Real chart x).det|) :
    delta • Measure.map chart (iidMassTripleLaw.restrict patch) ≤
      (27 : ENNReal) • (volume : Measure MassTriple) := by
  exact smul_map_restrict_le_smul_volume_of_det_fderiv_lower
    iidMassTripleLaw 27 delta iidMassTripleLaw_le_twentySeven_smul_volume
      patch hpatch chart hchart hdifferentiable hinjective hdet

end

end ArchonPhysics.ThreeParameterSpectralAveragingDensity
