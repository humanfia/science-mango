import ArchonPhysics.ParametricLiftedMismatchSmallBall
import ArchonPhysics.QuantitativeJacobianPushforward

/-!
# A local augmented Jacobian chart gives a linear mismatch small ball

This module composes the two generic endpoints needed by a full-IID spectral
chart.  On a measurable injective patch, a positive determinant lower bound
gives a density ceiling for the chart pushforward.  If the chart image stays
inside a bounded child-frequency cylinder and a finite environment patch,
the mismatch marginal is bounded linearly in the window width.

The theorem is local and quantitative.  It neither assumes nor asserts that
one fixed chart covers every mass configuration; exceptional regions remain
the responsibility of a separate good/bad atlas argument.
-/

namespace ArchonPhysics.ParametricJacobianLinearSmallBall

open ArchonPhysics
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

local instance massTripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance productIsAddHaarMeasure
    (nu : Measure E) [Measure.IsAddHaarMeasure nu] :
    Measure.IsAddHaarMeasure ((volume : Measure MassTriple).prod nu) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Quantitative local small-ball bound obtained directly from an augmented
Jacobian patch. -/
theorem map_restrict_parametricMismatch_smallBall_le_of_detLower
    (nu : Measure E) [Measure.IsAddHaarMeasure nu]
    {patch : Set (MassTriple × E)} (hpatch : MeasurableSet patch)
    (chart : MassTriple × E → MassTriple × E)
    (hchart : Measurable chart)
    (derivative : MassTriple × E →
      (MassTriple × E) →L[Real] (MassTriple × E))
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt chart (derivative point) patch point)
    (hinjective : InjOn chart patch)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ patch,
      detLower ≤ |(derivative point).det|)
    (ceiling : Real) {environment : Set E}
    (henvironment : MeasurableSet environment)
    (himage : chart '' patch ⊆
      parametricLiftedCylinder ceiling environment)
    {delta : Real} (hdelta : 0 ≤ delta) :
    Measure.map parametricMismatch
        (Measure.map chart
          (((volume : Measure MassTriple).prod nu).restrict patch))
        (absoluteMismatchSublevel delta) ≤
      (ENNReal.ofReal detLower)⁻¹ *
          (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
        ENNReal.ofReal (2 * delta) * nu environment := by
  let source : Measure (MassTriple × E) :=
    ((volume : Measure MassTriple).prod nu).restrict patch
  let lifted : Measure (MassTriple × E) := Measure.map chart source
  have hdensity :
      lifted ≤ (ENNReal.ofReal detLower)⁻¹ •
        ((volume : Measure MassTriple).prod nu) := by
    dsimp [lifted, source]
    exact map_volume_restrict_le_invDet_smul_volume
      ((volume : Measure MassTriple).prod nu) hpatch chart hchart derivative
      hderivative hinjective hdetLower hdet
  have hsupport : ∀ᵐ value ∂lifted,
      value ∈ parametricLiftedCylinder ceiling environment := by
    dsimp [lifted, source]
    apply (ae_map_iff hchart.aemeasurable
      (measurableSet_parametricLiftedCylinder ceiling henvironment)).2
    exact ae_restrict_of_forall_mem hpatch fun point hpoint ↦
      himage ⟨point, hpoint, rfl⟩
  exact map_parametricMismatch_absoluteMismatchSublevel_le
    lifted (ENNReal.ofReal detLower)⁻¹ ceiling nu henvironment
      hdensity hsupport hdelta

end

end ArchonPhysics.ParametricJacobianLinearSmallBall
