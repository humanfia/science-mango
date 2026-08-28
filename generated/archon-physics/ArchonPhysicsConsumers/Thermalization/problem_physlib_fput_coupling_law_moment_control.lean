import ArchonPhysics.PhyslibFPUTCouplingLawMomentControl

/-!
# Consumer: coupling control of restart laws and moments

This consumer exposes the good/bad expectation estimate, approximate coupling
control of bounded Lipschitz tests, exact-coupling control of the stronger
bounded-test law distance, and the explicit second/fourth pushforward moments.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCouplingLawMomentControl

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCouplingLawMomentControl
open ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation

noncomputable section

theorem high_probability_good_bad_expectation_contract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {p B G : Real}
    (hbadProbability : mu.real bad ≤ p)
    (hB : 0 ≤ B) (hG : 0 ≤ G)
    (a b : Omega → Real) (ha : Measurable a) (hb : Measurable b)
    (haBound : ∀ omega, |a omega| ≤ B)
    (hbBound : ∀ omega, |b omega| ≤ B)
    (hgood : ∀ omega, omega ∉ bad → |a omega - b omega| ≤ G) :
    |∫ omega, a omega ∂mu - ∫ omega, b omega ∂mu| ≤
      G + 2 * B * p :=
  abs_integral_sub_integral_le_of_highProbability_good
    mu bad hbadMeasurable hbadProbability hB hG a b ha hb
      haBound hbBound hgood

theorem approximate_coupling_law_contract
    {Omega S : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [PseudoMetricSpace S]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → S) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {delta p L : Real}
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (hbadProbability : mu.real bad ≤ p)
    (hnear : ∀ omega, omega ∉ bad → dist (X omega) (Y omega) ≤ delta) :
    BoundedLipschitzTestLawDistanceAtMost
      (Measure.map X mu) (Measure.map Y mu) L (L * delta + 2 * p) :=
  boundedLipschitzTestLawDistanceAtMost_map_of_coupling
    mu X Y hX hY bad hbadMeasurable hdelta hL hbadProbability hnear

theorem exact_coupling_bounded_test_law_contract
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → S) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {p : Real} (hbadProbability : mu.real bad ≤ p)
    (hagree : ∀ omega, omega ∉ bad → X omega = Y omega) :
    BoundedTestLawDistanceAtMost
      (Measure.map X mu) (Measure.map Y mu) (2 * p) :=
  boundedTestLawDistanceAtMost_map_of_exactCoupling
    mu X Y hX hY bad hbadMeasurable hbadProbability hagree

theorem coupled_pushforward_moment_contract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → Complex) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {delta p M : Real}
    (hdelta : 0 ≤ delta) (hM : 0 ≤ M)
    (hbadProbability : mu.real bad ≤ p)
    (hnear : ∀ omega, omega ∉ bad → ‖X omega - Y omega‖ ≤ delta)
    (hXBound : ∀ omega, ‖X omega‖ ≤ M)
    (hYBound : ∀ omega, ‖Y omega‖ ≤ M) :
    |∫ z, Complex.normSq z ∂Measure.map X mu -
        ∫ z, Complex.normSq z ∂Measure.map Y mu| ≤
        2 * M * delta + 2 * M ^ 2 * p ∧
    |∫ z, Complex.normSq z ^ 2 ∂Measure.map X mu -
        ∫ z, Complex.normSq z ^ 2 ∂Measure.map Y mu| ≤
        4 * M ^ 3 * delta + 2 * M ^ 4 * p :=
  pushforward_second_fourth_moment_errors
    mu X Y hX hY bad hbadMeasurable hdelta hM hbadProbability
      hnear hXBound hYBound

#print axioms high_probability_good_bad_expectation_contract
#print axioms approximate_coupling_law_contract
#print axioms exact_coupling_bounded_test_law_contract
#print axioms coupled_pushforward_moment_contract
#print axioms boundedLipschitzTestLawDistanceAtMost_map_of_coupling
#print axioms boundedTestLawDistanceAtMost_map_of_exactCoupling
#print axioms pushforward_second_fourth_moment_errors

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCouplingLawMomentControl
