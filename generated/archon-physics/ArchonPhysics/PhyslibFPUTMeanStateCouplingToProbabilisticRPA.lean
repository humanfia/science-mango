import ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate

/-!
# Mean-state coupling implies a probabilistic full-state RPA event

The probabilistic full-state endpoint interface asks for a measurable bad
event, a bound on its probability, and pointwise state closeness outside that
event.  This module derives all three from the weaker, scalar input

`∫ omega, dist (actual omega) (reference omega) ∂mu <= delta * p`.

The proof is Markov's inequality.  In the cubic endpoint regime
`delta = Cstate * |g|^3` and `p = Cfailure * |g|^3`, the sufficient mean
coupling estimate is therefore sixth order:

`∫ dist <= Cstate * Cfailure * |g|^6`.

This is a genuine reduction of the probabilistic RPA interface, but it does
not prove the remaining model-specific mean-coupling estimate from the FPUT
Hamiltonian flow.
-/

namespace ArchonPhysics.PhyslibFPUTMeanStateCouplingToProbabilisticRPA

open MeasureTheory

noncomputable section

/-- The canonical bad event extracted from a mean full-state coupling: the
state distance is at least the selected good-event radius. -/
def meanStateCouplingBadEvent
    {Omega X : Type*} [PseudoMetricSpace X]
    (actual reference : Omega → X) (delta : Real) : Set Omega :=
  {omega | delta ≤ dist (actual omega) (reference omega)}

/-- The Markov bad event is measurable when the two coupled state maps are
measurable into a Borel metric space. -/
theorem measurableSet_meanStateCouplingBadEvent
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (actual reference : Omega → X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (delta : Real) :
    MeasurableSet (meanStateCouplingBadEvent actual reference delta) := by
  exact measurableSet_le measurable_const (hactual.dist hreference)

/-- Outside the canonical bad event, the coupled states are within `delta`.
The event includes the equality boundary, so the conclusion follows from a
strict inequality and is valid with the weak endpoint bound expected by the
probabilistic certificate. -/
theorem dist_le_of_not_mem_meanStateCouplingBadEvent
    {Omega X : Type*} [PseudoMetricSpace X]
    (actual reference : Omega → X) (delta : Real) (omega : Omega)
    (homega : omega ∉ meanStateCouplingBadEvent actual reference delta) :
    dist (actual omega) (reference omega) ≤ delta := by
  exact le_of_lt (lt_of_not_ge homega)

/-- A mean-distance budget constructs the exact probability and good-event
fields needed by `ProbabilisticFullStateEndpointPropagationData`.

This is stated with the product budget `delta * p`; hence no division or
hidden convention is used. -/
theorem meanStateCouplingBadEvent_probability_le
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) (actual reference : Omega → X)
    (delta p : Real) (hdelta : 0 < delta)
    (hdistanceIntegrable : Integrable
      (fun omega ↦ dist (actual omega) (reference omega)) mu)
    (hmean :
      (∫ omega, dist (actual omega) (reference omega) ∂mu) ≤ delta * p) :
    mu.real (meanStateCouplingBadEvent actual reference delta) ≤ p := by
  have hmarkov :
      delta * mu.real
          (meanStateCouplingBadEvent actual reference delta) ≤
        ∫ omega, dist (actual omega) (reference omega) ∂mu := by
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun omega ↦ dist_nonneg)
      hdistanceIntegrable delta
  exact le_of_mul_le_mul_left (hmarkov.trans hmean) hdelta

/-- Complete reusable good/bad-event package obtained from a mean-distance
coupling estimate. -/
theorem meanStateCoupling_goodEvent_package
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
        dist (actual omega) (reference omega) ≤ delta := by
  refine ⟨measurableSet_meanStateCouplingBadEvent
      actual reference hactual hreference delta, ?_, ?_⟩
  · exact meanStateCouplingBadEvent_probability_le
      mu actual reference delta p hdelta hdistanceIntegrable hmean
  · exact dist_le_of_not_mem_meanStateCouplingBadEvent
      actual reference delta

/-- Cubic RPA specialization.  To obtain both a cubic state radius and a
cubic failure probability by Markov's inequality, it suffices to prove a
sixth-order mean full-state coupling estimate. -/
theorem cubic_goodEvent_package_of_meanDistance_sixth
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
        dist (actual omega) (reference omega) ≤ Cstate * |g| ^ 3 := by
  have habs : 0 < |g| := abs_pos.mpr hg
  have hdelta : 0 < Cstate * |g| ^ 3 :=
    mul_pos hCstate (pow_pos habs 3)
  apply meanStateCoupling_goodEvent_package
    mu actual reference hactual hreference
      (Cstate * |g| ^ 3) (Cfailure * |g| ^ 3)
      hdelta hdistanceIntegrable
  calc
    (∫ omega, dist (actual omega) (reference omega) ∂mu) ≤
        Cstate * Cfailure * |g| ^ 6 := hmeanSixth
    _ = (Cstate * |g| ^ 3) * (Cfailure * |g| ^ 3) := by ring

end

end ArchonPhysics.PhyslibFPUTMeanStateCouplingToProbabilisticRPA
