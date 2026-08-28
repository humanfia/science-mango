import ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting

/-!
# Consumer: fixed-output four-wave remainder counting

This consumer records the actual fixed-output dimension, the closed
lower-dimensional repeated/cancellation bounds, and the separate
one-to-three resonance exclusion.
-/

namespace ArchonPhysicsConsumers.Thermalization.EqualMassPeriodicFPUTFourWaveRemainderCounting

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.Lattice

noncomputable section

/-- Fixed output leaves two free momenta: the full supported actual diagram
family is `O(N^2)`, including all discrete branch decorations. -/
theorem actualFixedOutputSupported_card_contract
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputSupportedEffectiveFourWaveDiagram N output) ≤
      32 * N ^ 2 := by
  exact card_fixedOutputSupportedEffectiveFourWaveDiagram_le N output

/-- Coincident inner leaves lose one free momentum and are `O(N)`. -/
theorem actualFixedOutputInnerRepeated_card_contract
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputInnerLeafRepeatedDiagram N output) ≤
      32 * N := by
  exact card_fixedOutputInnerLeafRepeatedDiagram_le N output

/-- Literal opposite-sign same-mode inner cancellation is also `O(N)`. -/
theorem actualFixedOutputInnerCancellation_card_contract
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputInnerLeafCancellationDiagram N output) ≤
      32 * N := by
  exact card_fixedOutputInnerLeafCancellationDiagram_le N output

/-- On the complete fixed-output `2 ↔ 2` shell, repeated external modes are
exactly the four displayed graph lines. -/
theorem twoToTwoRepeated_iff_fourGraphLines_contract
    {N : Nat} [NeZero N] (output : Site N)
    (free : Site N × Site N) :
    ¬ Function.Injective (reducedTwoToTwoExternalModes output free) ↔
      IsDegenerateTwoToTwoFreePair output free := by
  exact not_injective_reducedTwoToTwoExternalModes_iff output free

/-- The full shell has exactly `N^2` points, while its complete
repeated/cancelling subset has at most `4N`. -/
theorem twoToTwoShell_main_and_degenerate_card_contract
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (TwoToTwoMomentumShell N output) = N ^ 2 ∧
      Fintype.card (DegenerateTwoToTwoMomentumShell N output) ≤
        4 * N := by
  exact ⟨card_twoToTwoMomentumShell N output,
    card_degenerateTwoToTwoMomentumShell_le N output⟩

/-- The separately retained one-positive/three-negative active sector cannot
be exactly resonant for the acoustic dispersion. -/
theorem actualActiveOneToThree_nonresonant_contract
    {N : Nat} [NeZero N]
    (diagram : ActiveEffectiveFourWaveDiagram N)
    (hsector : IsOneToThreeExternalSignSector diagram.1) :
    totalFourWaveMismatch diagram.1 ≠ 0 := by
  exact active_totalFourWaveMismatch_ne_zero_of_oneToThree diagram hsector

#print axioms actualFixedOutputSupported_card_contract
#print axioms actualFixedOutputInnerRepeated_card_contract
#print axioms actualFixedOutputInnerCancellation_card_contract
#print axioms twoToTwoRepeated_iff_fourGraphLines_contract
#print axioms twoToTwoShell_main_and_degenerate_card_contract
#print axioms actualActiveOneToThree_nonresonant_contract
#print axioms card_degenerateTwoToTwoMomentumShell_le

end

end ArchonPhysicsConsumers.Thermalization.EqualMassPeriodicFPUTFourWaveRemainderCounting
