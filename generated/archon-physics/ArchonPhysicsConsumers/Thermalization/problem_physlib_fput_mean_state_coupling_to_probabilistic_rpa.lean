import ArchonPhysics.PhyslibFPUTMeanStateCouplingToProbabilisticRPA

/-!
# Consumer: mean full-state coupling to probabilistic RPA

This consumer checks both the generic Markov bridge and its cubic/sixth-order
specialization.  It does not assume or claim that the FPUT Hamiltonian flow
already supplies the required mean-distance estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTMeanStateCouplingToProbabilisticRPA

open MeasureTheory
open ArchonPhysics.PhyslibFPUTMeanStateCouplingToProbabilisticRPA

noncomputable section

theorem mean_coupling_contract
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure Omega) (actual reference : Omega → X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (delta p : Real) (hdelta : 0 < delta)
    (hdistanceIntegrable : Integrable
      (fun omega ↦ dist (actual omega) (reference omega)) mu)
    (hmean :
      (∫ omega, dist (actual omega) (reference omega) ∂mu) ≤ delta * p) :
    MeasurableSet (meanStateCouplingBadEvent actual reference delta) ∧
      mu.real (meanStateCouplingBadEvent actual reference delta) ≤ p ∧
      ∀ omega, omega ∉ meanStateCouplingBadEvent actual reference delta →
        dist (actual omega) (reference omega) ≤ delta :=
  meanStateCoupling_goodEvent_package mu actual reference
    hactual hreference delta p hdelta hdistanceIntegrable hmean

theorem cubic_mean_coupling_contract
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure Omega) (actual reference : Omega → X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (g Cstate Cfailure : Real) (hg : g ≠ 0) (hCstate : 0 < Cstate)
    (hdistanceIntegrable : Integrable
      (fun omega ↦ dist (actual omega) (reference omega)) mu)
    (hmeanSixth :
      (∫ omega, dist (actual omega) (reference omega) ∂mu) ≤
        Cstate * Cfailure * |g| ^ 6) :
    MeasurableSet
        (meanStateCouplingBadEvent actual reference
          (Cstate * |g| ^ 3)) ∧
      mu.real
          (meanStateCouplingBadEvent actual reference
            (Cstate * |g| ^ 3)) ≤
        Cfailure * |g| ^ 3 ∧
      ∀ omega,
        omega ∉ meanStateCouplingBadEvent actual reference
          (Cstate * |g| ^ 3) →
        dist (actual omega) (reference omega) ≤ Cstate * |g| ^ 3 :=
  cubic_goodEvent_package_of_meanDistance_sixth
    mu actual reference hactual hreference g Cstate Cfailure
      hg hCstate hdistanceIntegrable hmeanSixth

#print axioms meanStateCouplingBadEvent_probability_le
#print axioms meanStateCoupling_goodEvent_package
#print axioms cubic_goodEvent_package_of_meanDistance_sixth
#print axioms mean_coupling_contract
#print axioms cubic_mean_coupling_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTMeanStateCouplingToProbabilisticRPA
