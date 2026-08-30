import ArchonPhysics.ParametricJacobianLinearSmallBall

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ParametricJacobianLinearSmallBall
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

example {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
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
        ENNReal.ofReal (2 * delta) * nu environment :=
  map_restrict_parametricMismatch_smallBall_le_of_detLower
    nu hpatch chart hchart derivative hderivative hinjective hdetLower hdet
      ceiling henvironment himage hdelta

#print axioms map_restrict_parametricMismatch_smallBall_le_of_detLower

end

end ArchonPhysicsConsumers.Thermalization
