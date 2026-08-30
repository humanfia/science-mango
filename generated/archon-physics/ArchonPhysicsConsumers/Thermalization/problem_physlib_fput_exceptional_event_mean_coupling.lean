import ArchonPhysics.PhyslibFPUTExceptionalEventMeanCoupling

/-!
# Consumer: exceptional-event mean coupling

This gate verifies the certificate-free quantitative step from pointwise
good-event control to the mean coupling estimate needed by probabilistic RPA.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTExceptionalEventMeanCoupling

open MeasureTheory
open ArchonPhysics.PhyslibFPUTExceptionalEventMeanCoupling
open ArchonPhysics.PhyslibFPUTMeanStateCouplingToProbabilisticRPA

noncomputable section

#check meanDistance_le_of_exceptionalEvent
#check meanDistance_le_sixth_of_exceptionalEvent
#check cubic_goodEvent_package_of_exceptionalEvent_sixth

/-- Consumer-level sixth-order mean-coupling consequence. -/
theorem exceptional_event_supplies_mean_coupling_sixth
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (actual reference : Omega -> X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    (g Cgood Cbad D : Real)
    (hCgood : 0 <= Cgood) (hCbad : 0 <= Cbad) (hD : 0 <= D)
    (hbadProbability : mu.real bad <= Cbad * |g| ^ 6)
    (hglobal : forall omega,
      dist (actual omega) (reference omega) <= D)
    (hgood : forall omega, omega ∉ bad ->
      dist (actual omega) (reference omega) <= Cgood * |g| ^ 6) :
    (∫ omega, dist (actual omega) (reference omega) ∂mu) <=
      (Cgood + D * Cbad) * |g| ^ 6 :=
  meanDistance_le_sixth_of_exceptionalEvent
    mu actual reference hactual hreference bad hbadMeasurable
      g Cgood Cbad D hCgood hCbad hD hbadProbability hglobal hgood

#print axioms stateDistance_integrable_of_uniform_bound
#print axioms meanDistance_le_of_exceptionalEvent
#print axioms meanDistance_le_sixth_of_exceptionalEvent
#print axioms cubic_goodEvent_package_of_exceptionalEvent_sixth
#print axioms exceptional_event_supplies_mean_coupling_sixth

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTExceptionalEventMeanCoupling
