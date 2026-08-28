import ArchonPhysics.EqualMassPeriodicFPUTAlphaNTJointRemainder

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTAlphaNTJointRemainder
open ArchonPhysics.Lattice
open Filter Topology

noncomputable section

theorem equal_mass_FPUT_counted_alpha_N_T_bounds_consumer
    {c : Real} (hc : 0 < c) (s : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (N : Nat) [NeZero N] (alpha time : Real) (output : Site N) :
    (‖fixedOutputSupportedFourWaveDuhamelSum N alpha time output‖ ≤
      (2048 / c) * |alpha| ^ 2 * |time| * (N : Real) ^ (s + 2)) ∧
    (‖fixedOutputDegenerateTwoToTwoDuhamelRemainder
        N alpha time output‖ ≤
      (8192 / c) * |alpha| ^ 2 * |time| * (N : Real) ^ (s + 1)) :=
  ⟨norm_fixedOutputSupportedFourWaveDuhamelSum_le_of_gapPolynomial
      hc s hgap N alpha time output,
    norm_fixedOutputDegenerateTwoToTwoDuhamelRemainder_le_of_gapPolynomial
      hc s hgap N alpha time output⟩

theorem equal_mass_FPUT_full_and_degenerate_power_windows_consumer
    {c : Real} (hc : 0 < c) (s a b : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (hfull : b + (s + 2) < 2 * a)
    (hdegenerate : b + (s + 1) < 2 * a)
    (output : ∀ n, Site (n + 1)) :
    Tendsto
      (fun n : Nat ↦
        fixedOutputSupportedFourWaveDuhamelSum (n + 1)
          (inverseVolumePowerCoupling a n) (volumePowerTime b n)
          (output n))
      atTop (nhds 0) ∧
    Tendsto
      (fun n : Nat ↦
        fixedOutputDegenerateTwoToTwoDuhamelRemainder (n + 1)
          (inverseVolumePowerCoupling a n) (volumePowerTime b n)
          (output n))
      atTop (nhds 0) :=
  ⟨fixedOutputSupportedFourWaveDuhamelSum_tendsto_zero_powerSchedule
      hc s a b hgap hfull output,
    fixedOutputDegenerateTwoToTwoDuhamelRemainder_tendsto_zero_powerSchedule
      hc s a b hgap hdegenerate output⟩

theorem equal_mass_FPUT_degenerate_plus_Picard_power_window_consumer
    {c : Real} (hc : 0 < c) (s a b : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (hdiagramExponent : b + (s + 1) < 2 * a)
    (output : ∀ n, Site (n + 1))
    (remainder : Nat → Real → Complex)
    (picardBound : GrowingWindowAlphaNTRemainderBound
      (inverseVolumePowerCoupling a) (volumePowerTime b) remainder)
    (hpicardExponent : b * picardBound.timePower <
      a * picardBound.alphaPower + picardBound.volumeDecay) :
    Tendsto
      (fun n : Nat ↦
        fixedOutputDegenerateTwoToTwoDuhamelRemainder (n + 1)
            (inverseVolumePowerCoupling a n) (volumePowerTime b n)
            (output n) +
          remainder n (volumePowerTime b n))
      atTop (nhds 0) :=
  degenerateFourWave_add_picardRemainder_tendsto_zero_powerSchedule
    hc s a b hgap hdiagramExponent output remainder picardBound
      hpicardExponent

#print axioms equal_mass_FPUT_counted_alpha_N_T_bounds_consumer
#print axioms equal_mass_FPUT_full_and_degenerate_power_windows_consumer
#print axioms equal_mass_FPUT_degenerate_plus_Picard_power_window_consumer

end

end ArchonPhysicsConsumers.Thermalization
