import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A strict scalar derivative gives a local linear small-ball bound

For a real-valued function of one real variable, a nonzero strict derivative
already contains the quantitative input needed for a local small-ball bound.
Mathlib's strict inverse-function estimate supplies an open neighbourhood on
which the function approximates its derivative, hence is antilipschitz.  The
Lebesgue measure of a subset of `Real` is bounded by its extended diameter,
so no `C²` hypothesis or continuous derivative field is needed.

The constant below is the one returned by
`HasStrictFDerivAt.approximates_deriv_on_open_nhds`: half of the inverse
linear scale is reserved for the nonlinear error.  It is a finite `NNReal`.
-/

namespace ArchonPhysics.StrictDerivativeLocalLinearSmallBall

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The invertible scalar linear map associated with multiplication by a
nonzero strict derivative. -/
def scalarStrictDerivativeEquiv (derivative : Real)
    (hderivative : derivative ≠ 0) : Real ≃L[Real] Real :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 derivative hderivative)

/-- The explicit local antilipschitz constant supplied by the standard
half-margin strict inverse-function estimate. -/
def strictDerivativeAntilipschitzConstant (derivative : Real)
    (hderivative : derivative ≠ 0) : NNReal :=
  let inverseNorm :=
    ‖((scalarStrictDerivativeEquiv derivative hderivative).symm :
      Real →L[Real] Real)‖₊
  (inverseNorm⁻¹ - inverseNorm⁻¹ / 2)⁻¹

/-- A nonzero strict scalar derivative gives an open measurable patch inside
any prescribed neighbourhood, together with the exact Mathlib
`ApproximatesLinearOn` certificate and its antilipschitz consequence. -/
theorem exists_open_measurable_antilipschitz_patch
    {chart : Real → Real} {point derivative : Real}
    (hstrict : HasStrictDerivAt chart derivative point)
    (hderivative : derivative ≠ 0)
    {neighborhood : Set Real} (hneighborhood : neighborhood ∈ nhds point) :
    ∃ patch : Set Real,
      IsOpen patch ∧ MeasurableSet patch ∧ point ∈ patch ∧
      patch ⊆ neighborhood ∧
      ApproximatesLinearOn chart
        (scalarStrictDerivativeEquiv derivative hderivative :
          Real →L[Real] Real) patch
        (‖((scalarStrictDerivativeEquiv derivative hderivative).symm :
            Real →L[Real] Real)‖₊⁻¹ / 2) ∧
      AntilipschitzWith
        (strictDerivativeAntilipschitzConstant derivative hderivative)
        (patch.domRestrict chart) := by
  let derivativeEquiv := scalarStrictDerivativeEquiv derivative hderivative
  have hequiv : (derivativeEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real derivative := by
    apply ContinuousLinearMap.ext
    intro value
    simp [derivativeEquiv, scalarStrictDerivativeEquiv, mul_comm]
  have hstrictEquiv : HasStrictFDerivAt chart
      (derivativeEquiv : Real →L[Real] Real) point := by
    rw [hequiv]
    exact hstrict.hasStrictFDerivAt
  obtain ⟨source, hpointSource, hopenSource, happroxSource⟩ :=
    hstrictEquiv.approximates_deriv_on_open_nhds
  obtain ⟨target, htargetSubset, hopenTarget, hpointTarget⟩ :=
    mem_nhds_iff.mp hneighborhood
  let patch := source ∩ target
  have hopenPatch : IsOpen patch := hopenSource.inter hopenTarget
  have hpointPatch : point ∈ patch := ⟨hpointSource, hpointTarget⟩
  have hpatchSubset : patch ⊆ neighborhood :=
    fun _ hmem ↦ htargetSubset hmem.2
  have happrox : ApproximatesLinearOn chart
      (derivativeEquiv : Real →L[Real] Real) patch
      (‖(derivativeEquiv.symm : Real →L[Real] Real)‖₊⁻¹ / 2) :=
    happroxSource.mono_set inter_subset_left
  have hanti : AntilipschitzWith
      ((‖(derivativeEquiv.symm : Real →L[Real] Real)‖₊⁻¹ -
        ‖(derivativeEquiv.symm : Real →L[Real] Real)‖₊⁻¹ / 2)⁻¹)
      (patch.domRestrict chart) :=
    happrox.antilipschitz
      (derivativeEquiv.subsingleton_or_nnnorm_symm_pos.imp id fun hpositive ↦
        NNReal.half_lt_self (ne_of_gt (inv_pos.mpr hpositive)))
  refine ⟨patch, hopenPatch, hopenPatch.measurableSet, hpointPatch,
    hpatchSubset, ?_, ?_⟩
  · simpa [derivativeEquiv] using happrox
  · simpa [strictDerivativeAntilipschitzConstant, derivativeEquiv] using hanti

/-- An antilipschitz scalar chart controls the Lebesgue measure of the part
of its domain patch mapped into any target by the target's extended
diameter. -/
theorem volume_inter_preimage_le_of_antilipschitz
    {chart : Real → Real} {patch target : Set Real} {K : NNReal}
    (hanti : AntilipschitzWith K (patch.domRestrict chart)) :
    (volume : Measure Real) (patch ∩ chart ⁻¹' target) ≤
      (K : ENNReal) * Metric.ediam target := by
  calc
    (volume : Measure Real) (patch ∩ chart ⁻¹' target) ≤
        Metric.ediam (patch ∩ chart ⁻¹' target) :=
      Real.volume_le_diam _
    _ ≤ (K : ENNReal) * Metric.ediam target := by
      apply Metric.ediam_le
      intro first hfirst second hsecond
      have hpair := hanti
        (⟨first, hfirst.1⟩ : patch) (⟨second, hsecond.1⟩ : patch)
      calc
        edist first second ≤
            (K : ENNReal) * edist (chart first) (chart second) := by
          simpa [Set.domRestrict] using hpair
        _ ≤ (K : ENNReal) * Metric.ediam target := by
          have hfirstTarget : chart first ∈ target := hfirst.2
          have hsecondTarget : chart second ∈ target := hsecond.2
          have hdiam : edist (chart first) (chart second) <=
              Metric.ediam target :=
            Metric.edist_le_ediam_of_mem hfirstTarget hsecondTarget
          calc
            (K : ENNReal) * edist (chart first) (chart second) =
                edist (chart first) (chart second) * (K : ENNReal) := mul_comm _ _
            _ ≤ Metric.ediam target * (K : ENNReal) := mul_left_mono hdiam
            _ = (K : ENNReal) * Metric.ediam target := mul_comm _ _

/-- Centered-interval specialization: a `K`-antilipschitz chart has local
Lebesgue small-ball cost at most `K * 2δ`. -/
theorem volume_inter_preimage_Icc_le_of_antilipschitz
    {chart : Real → Real} {patch : Set Real} {K : NNReal}
    (hanti : AntilipschitzWith K (patch.domRestrict chart))
    (center delta : Real) (_hdelta : 0 ≤ delta) :
    (volume : Measure Real)
        (patch ∩ chart ⁻¹' Icc (center - delta) (center + delta)) ≤
      (K : ENNReal) * ENNReal.ofReal (2 * delta) := by
  refine (volume_inter_preimage_le_of_antilipschitz hanti).trans ?_
  gcongr
  apply Metric.ediam_le_of_forall_dist_le
  intro first hfirst second hsecond
  rw [Real.dist_eq]
  apply (abs_le).2
  constructor <;> linarith [hfirst.1, hfirst.2, hsecond.1, hsecond.2]

/-- Combined local theorem.  A nonzero strict derivative alone yields an
open measurable patch in the requested neighbourhood, an explicit
antilipschitz certificate, and a uniform linear centered-window bound. -/
theorem exists_open_local_linearSmallBall_of_hasStrictDerivAt
    {chart : Real → Real} {point derivative : Real}
    (hstrict : HasStrictDerivAt chart derivative point)
    (hderivative : derivative ≠ 0)
    {neighborhood : Set Real} (hneighborhood : neighborhood ∈ nhds point) :
    ∃ patch : Set Real,
      IsOpen patch ∧ MeasurableSet patch ∧ point ∈ patch ∧
      patch ⊆ neighborhood ∧
      AntilipschitzWith
        (strictDerivativeAntilipschitzConstant derivative hderivative)
        (patch.domRestrict chart) ∧
      ∀ center delta : Real, 0 ≤ delta →
        (volume : Measure Real)
            (patch ∩ chart ⁻¹' Icc (center - delta) (center + delta)) ≤
          (strictDerivativeAntilipschitzConstant derivative hderivative :
            ENNReal) * ENNReal.ofReal (2 * delta) := by
  obtain ⟨patch, hopen, hmeasurable, hpoint, hsubset, _happrox, hanti⟩ :=
    exists_open_measurable_antilipschitz_patch
      hstrict hderivative hneighborhood
  exact ⟨patch, hopen, hmeasurable, hpoint, hsubset, hanti,
    fun center delta hdelta ↦
      volume_inter_preimage_Icc_le_of_antilipschitz
        hanti center delta hdelta⟩

end

end ArchonPhysics.StrictDerivativeLocalLinearSmallBall
