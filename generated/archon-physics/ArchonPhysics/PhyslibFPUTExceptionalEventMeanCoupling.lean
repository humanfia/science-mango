import ArchonPhysics.PhyslibFPUTMeanStateCouplingToProbabilisticRPA

/-!
# Exceptional-event bounds imply mean full-state coupling

This module moves one step upstream of the mean-coupling hypothesis used by
the probabilistic RPA interface.  It contains no certificate structure and no
Hamiltonian or RPA assumption hidden in a field.

For two measurable full-state maps, a pointwise distance bound `G` off a
measurable exceptional event, a global distance bound `D`, and exceptional
probability at most `p` imply the quantitative estimate

`integral dist <= G + D * p`.

Consequently, sixth-order good-set and exceptional-probability estimates give
the `O(|g|^6)` mean coupling required by the existing cubic Markov/RPA bridge.
The model-specific task that remains is to prove those pointwise and
exceptional-event estimates from the Hamiltonian history expansion.
-/

namespace ArchonPhysics.PhyslibFPUTExceptionalEventMeanCoupling

open MeasureTheory
open ArchonPhysics.PhyslibFPUTMeanStateCouplingToProbabilisticRPA

noncomputable section

/-- Measurable full states with a uniform distance bound have integrable
coupling distance under a probability law. -/
theorem stateDistance_integrable_of_uniform_bound
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (actual reference : Omega -> X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    {D : Real} (hglobal : forall omega,
      dist (actual omega) (reference omega) <= D) :
    Integrable (fun omega => dist (actual omega) (reference omega)) mu := by
  apply Integrable.of_bound
    (hactual.dist hreference).aestronglyMeasurable D
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  exact hglobal omega

/-- Sharp good/bad decomposition for a mean coupling distance.  The bad-set
cost is `D * p`, rather than the `2 * D * p` produced by treating distance as
the difference of two unrelated bounded observables. -/
theorem meanDistance_le_of_exceptionalEvent
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (actual reference : Omega -> X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {p D G : Real}
    (hbadProbability : mu.real bad <= p)
    (hD : 0 <= D) (hG : 0 <= G)
    (hglobal : forall omega,
      dist (actual omega) (reference omega) <= D)
    (hgood : forall omega, omega ∉ bad ->
      dist (actual omega) (reference omega) <= G) :
    (∫ omega, dist (actual omega) (reference omega) ∂mu) <=
      G + D * p := by
  let distance : Omega -> Real := fun omega =>
    dist (actual omega) (reference omega)
  have hdistanceIntegrable : Integrable distance mu :=
    stateDistance_integrable_of_uniform_bound
      mu actual reference hactual hreference hglobal
  have hbadIntegral :
      ‖∫ omega in bad, distance omega ∂mu‖ <= D * mu.real bad := by
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top mu bad)
    intro omega _homega
    simpa only [distance, Real.norm_eq_abs,
      abs_of_nonneg dist_nonneg] using hglobal omega
  have hgoodIntegral :
      ‖∫ omega in badᶜ, distance omega ∂mu‖ <= G * mu.real badᶜ := by
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top mu badᶜ)
    intro omega homega
    simpa only [distance, Real.norm_eq_abs,
      abs_of_nonneg dist_nonneg] using hgood omega homega
  have hsplit := integral_add_compl hbadMeasurable hdistanceIntegrable
  calc
    (∫ omega, dist (actual omega) (reference omega) ∂mu) =
        (∫ omega in bad, distance omega ∂mu) +
          ∫ omega in badᶜ, distance omega ∂mu := by
      simpa only [distance] using hsplit.symm
    _ <= ‖∫ omega in bad, distance omega ∂mu‖ +
          ‖∫ omega in badᶜ, distance omega ∂mu‖ :=
      add_le_add
        (by simpa only [Real.norm_eq_abs] using
          le_abs_self (∫ omega in bad, distance omega ∂mu))
        (by simpa only [Real.norm_eq_abs] using
          le_abs_self (∫ omega in badᶜ, distance omega ∂mu))
    _ <= D * mu.real bad + G * mu.real badᶜ :=
      add_le_add hbadIntegral hgoodIntegral
    _ <= D * p + G * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hbadProbability hD)
        (mul_le_mul_of_nonneg_left measureReal_le_one hG)
    _ = G + D * p := by ring

/-- Sixth-order specialization of the exceptional-event mean estimate. -/
theorem meanDistance_le_sixth_of_exceptionalEvent
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (actual reference : Omega -> X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    (g Cgood Cbad D : Real)
    (hCgood : 0 <= Cgood) (_hCbad : 0 <= Cbad) (hD : 0 <= D)
    (hbadProbability : mu.real bad <= Cbad * |g| ^ 6)
    (hglobal : forall omega,
      dist (actual omega) (reference omega) <= D)
    (hgood : forall omega, omega ∉ bad ->
      dist (actual omega) (reference omega) <= Cgood * |g| ^ 6) :
    (∫ omega, dist (actual omega) (reference omega) ∂mu) <=
      (Cgood + D * Cbad) * |g| ^ 6 := by
  have hbase := meanDistance_le_of_exceptionalEvent
    mu actual reference hactual hreference bad hbadMeasurable
      hbadProbability hD
      (mul_nonneg hCgood (pow_nonneg (abs_nonneg g) 6))
      hglobal hgood
  calc
    (∫ omega, dist (actual omega) (reference omega) ∂mu) <=
        Cgood * |g| ^ 6 + D * (Cbad * |g| ^ 6) := hbase
    _ = (Cgood + D * Cbad) * |g| ^ 6 := by ring

/-- Pointwise sixth-order control off a sufficiently rare exceptional event
supplies the complete cubic-radius/cubic-probability RPA package.  The
coefficient inequality is explicit and contains the entire budget transfer. -/
theorem cubic_goodEvent_package_of_exceptionalEvent_sixth
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (actual reference : Omega -> X)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (sourceBad : Set Omega) (hsourceBadMeasurable : MeasurableSet sourceBad)
    (g Cstate Cfailure Cgood Cbad D : Real)
    (hg : g ≠ 0) (hCstate : 0 < Cstate)
    (hCgood : 0 <= Cgood) (hCbad : 0 <= Cbad) (hD : 0 <= D)
    (hcoefficient : Cgood + D * Cbad <= Cstate * Cfailure)
    (hsourceBadProbability :
      mu.real sourceBad <= Cbad * |g| ^ 6)
    (hglobal : forall omega,
      dist (actual omega) (reference omega) <= D)
    (hgood : forall omega, omega ∉ sourceBad ->
      dist (actual omega) (reference omega) <= Cgood * |g| ^ 6) :
    MeasurableSet
        (meanStateCouplingBadEvent actual reference
          (Cstate * |g| ^ 3)) /\
      mu.real
          (meanStateCouplingBadEvent actual reference
            (Cstate * |g| ^ 3)) <=
        Cfailure * |g| ^ 3 /\
      forall omega,
        omega ∉ meanStateCouplingBadEvent actual reference
          (Cstate * |g| ^ 3) ->
        dist (actual omega) (reference omega) <= Cstate * |g| ^ 3 := by
  have hdistanceIntegrable : Integrable
      (fun omega => dist (actual omega) (reference omega)) mu :=
    stateDistance_integrable_of_uniform_bound
      mu actual reference hactual hreference hglobal
  have hmeanBase := meanDistance_le_sixth_of_exceptionalEvent
    mu actual reference hactual hreference sourceBad hsourceBadMeasurable
      g Cgood Cbad D hCgood hCbad hD hsourceBadProbability hglobal hgood
  have hmeanSixth :
      (∫ omega, dist (actual omega) (reference omega) ∂mu) <=
        Cstate * Cfailure * |g| ^ 6 := by
    exact hmeanBase.trans
      (mul_le_mul_of_nonneg_right hcoefficient
        (pow_nonneg (abs_nonneg g) 6))
  exact cubic_goodEvent_package_of_meanDistance_sixth
    mu actual reference hactual hreference g Cstate Cfailure hg hCstate
      hdistanceIntegrable hmeanSixth

end

end ArchonPhysics.PhyslibFPUTExceptionalEventMeanCoupling
