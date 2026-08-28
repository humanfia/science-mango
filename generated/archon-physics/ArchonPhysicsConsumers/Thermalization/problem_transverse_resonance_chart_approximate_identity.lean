import ArchonPhysics.TransverseResonanceChartApproximateIdentity

/-!
# Consumer: transverse resonance-chart collision limit
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.TransverseResonanceChartApproximateIdentity
open Filter MeasureTheory Topology

noncomputable section

theorem transverse_resonance_chart_collision_limit_consumer
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b) :
    Tendsto
      (fun T : Real ↦ ∫ x in a..b,
        normalizedFiniteTimeResonanceKernel (mismatch x) T * mark x)
      atTop (nhds (density 0)) :=
  tendsto_integral_collisionKernel_chart chart

#print axioms transverse_resonance_chart_collision_limit_consumer

end

end ArchonPhysicsConsumers.Thermalization
