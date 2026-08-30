import ArchonPhysics.BHOAnnealedEFCLocalizationBorelCantelli

/-!
# Thermalization consumer: annealed EFC to almost-sure localization

This consumer replays the generic probability bridge behind BHO Lemma 3.
The finite-volume annealed EFC expectation inequality is displayed as an
input.  No claim is made here that a particular random-mass operator has
already been proved to satisfy that input.
-/

namespace ArchonPhysicsConsumers.Thermalization.problem_bho_annealed_efc_localization_borel_cantelli

open Filter MeasureTheory
open ArchonPhysics.BHORandomMassLocalizationSchedule
open ArchonPhysics.BHOAnnealedEFCLocalizationBorelCantelli

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
variable (P : Measure Omega)
variable
  (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
  (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
variable {C alpha gamma decayRate : Real}
variable (hC : 0 <= C) (hgamma : 0 < gamma)
variable (hscale : 2 * alpha < gamma) (hdecay : 0 < decayRate)
variable (hnormalized : forall n omega q,
  ∑ x, |coordinate n omega q x| ^ 2 = 1)
variable (hmeasurable : forall n x y,
  Measurable (fun omega =>
    hardEigenfunctionCorrelator hard coordinate n omega x y))
variable (hEFC : forall n x y, IsBHOWindowSeparated gamma x y ->
  (∫⁻ omega,
    hardEigenfunctionCorrelator hard coordinate n omega x y ∂P) <=
    ENNReal.ofReal
      (C * bhoEFCWindowTail alpha gamma decayRate (n + 2)))

include hC hgamma hmeasurable hEFC

/-- The finite-volume Markov/union-bound conclusion. -/
theorem problem_finiteVolume_badEvent_probability_bound (n : Nat) :
    P (bhoEFCBadEvent hard coordinate gamma n) <=
      bhoEFCBadProbabilityBudget C alpha gamma decayRate n :=
  measure_bhoEFCBadEvent_le P hard coordinate hC hgamma
    hmeasurable hEFC n

include hscale hdecay

/-- The actual bad-event probabilities are summable. -/
theorem problem_badEvent_probability_tsum_ne_top :
    (∑' n : Nat, P (bhoEFCBadEvent hard coordinate gamma n)) ≠
      (⊤ : ENNReal) :=
  bhoEFCBadEvent_measure_tsum_ne_top P hard coordinate
    hC hgamma hscale hdecay hmeasurable hEFC

include hnormalized

/-- The full generic Borel--Cantelli localization conclusion. -/
theorem problem_annealedEFC_implies_eventual_localization_ae :
    ∀ᵐ omega ∂P, ∀ᶠ n : Nat in atTop,
      HasBHOLocalizationWindows hard coordinate gamma n omega :=
  eventually_hasBHOLocalizationWindows_ae P hard coordinate
    hC hgamma hscale hdecay hnormalized hmeasurable hEFC

#print axioms exists_abs_ge_volume_rpow_neg_half
#print axioms hasBHOLocalizationWindows_of_not_mem_badEvent
#print axioms measure_bhoEFCBadEvent_le
#print axioms bhoEFCBadProbabilityBudget_tsum_ne_top
#print axioms bhoEFCBadEvent_measure_tsum_ne_top
#print axioms eventually_hasBHOLocalizationWindows_ae
#print axioms problem_finiteVolume_badEvent_probability_bound
#print axioms problem_badEvent_probability_tsum_ne_top
#print axioms problem_annealedEFC_implies_eventual_localization_ae

end

end ArchonPhysicsConsumers.Thermalization.problem_bho_annealed_efc_localization_borel_cantelli
