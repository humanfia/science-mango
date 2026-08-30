import ArchonPhysics.ParametricLiftedMismatchSmallBall

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

example {E : Type*} [MeasurableSpace E]
    (lifted : Measure (MassTriple × E)) (C : ENNReal) (ceiling : Real)
    (ν : Measure E) [SFinite ν]
    {environment : Set E} (henvironment : MeasurableSet environment)
    (hdensity : lifted ≤ C • ((volume : Measure MassTriple).prod ν))
    (hsupport : ∀ᵐ point ∂lifted,
      point ∈ parametricLiftedCylinder ceiling environment)
    {delta : Real} (hdelta : 0 ≤ delta) :
    Measure.map parametricMismatch lifted (absoluteMismatchSublevel delta) ≤
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
        ENNReal.ofReal (2 * delta) * ν environment :=
  map_parametricMismatch_absoluteMismatchSublevel_le
    lifted C ceiling ν henvironment hdensity hsupport hdelta

#print axioms map_parametricMismatch_absoluteMismatchSublevel_le

end

end ArchonPhysicsConsumers.Thermalization
