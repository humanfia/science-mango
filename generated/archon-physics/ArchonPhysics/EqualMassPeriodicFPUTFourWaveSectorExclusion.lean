import ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave

/-!
# Equal-mass periodic FPUT: exclusion of nonzero one-to-three sectors

The clean acoustic dispersion is strictly subadditive for two nonzero
momenta.  Iterating that inequality shows that one wave cannot resonate with
three waves when every input is nonzero.  This removes the `1 ↔ 3` sectors
from the effective four-wave shell before any kinetic or random-phase
argument is introduced.

All statements are exact at fixed finite `N`.  They do not classify the
remaining `2 ↔ 2` shell or assert a thermodynamic limit.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTFourWaveSectorExclusion

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-- Strict three-input subadditivity.  The intermediate sum is allowed to be
zero; in that case positivity of the first two input frequencies supplies the
strict gap. -/
theorem periodicSineFrequency_three_add_lt
    {N : Nat} [NeZero N] {a b c : Site N}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    periodicSineFrequency N (a + b + c) <
      periodicSineFrequency N a + periodicSineFrequency N b +
        periodicSineFrequency N c := by
  by_cases hab : a + b = 0
  · have haPos := periodicSineFrequency_pos_of_ne_zero ha
    have hbPos := periodicSineFrequency_pos_of_ne_zero hb
    rw [hab, zero_add]
    linarith
  · have houter := periodicSineFrequency_add_lt hab hc
    have hinner := periodicSineFrequency_add_lt ha hb
    linarith

/-- A literal three-to-one resonance must contain a zero input mode. -/
theorem threeToOne_resonance_has_zero_input
    {N : Nat} [NeZero N] {output a b c : Site N}
    (hmomentum : output = a + b + c)
    (hfrequency : periodicSineFrequency N output =
      periodicSineFrequency N a + periodicSineFrequency N b +
        periodicSineFrequency N c) :
    a = 0 ∨ b = 0 ∨ c = 0 := by
  by_contra hzero
  simp only [not_or] at hzero
  rw [hmomentum] at hfrequency
  have hstrict := periodicSineFrequency_three_add_lt
    hzero.1 hzero.2.1 hzero.2.2
  linarith

/-- Sign decoration `(+,-,-,-)`: one output versus three inputs. -/
def onePlusThreeMinusSign : Fin 4 → InteractionSign :=
  ![.plus, .minus, .minus, .minus]

/-- The exact signed Fourier conditions in the `(+,-,-,-)` sector force a
translation leg. -/
theorem onePlusThreeMinus_resonance_has_zero_mode
    {N : Nat} [NeZero N] (modes : Fin 4 → Site N)
    (hmomentum : FourierMomentumBalanced onePlusThreeMinusSign modes)
    (hfrequency : periodicSinePhaseMismatch onePlusThreeMinusSign modes = 0) :
    ∃ r, modes r = 0 := by
  have hmomentum' : modes 0 = modes 1 + modes 2 + modes 3 := by
    simp [FourierMomentumBalanced, signedFourierMomentum,
      onePlusThreeMinusSign, Fin.sum_univ_four,
      interactionSignMomentum] at hmomentum
    linear_combination hmomentum
  have hfrequency' : periodicSineFrequency N (modes 0) =
      periodicSineFrequency N (modes 1) +
        periodicSineFrequency N (modes 2) +
          periodicSineFrequency N (modes 3) := by
    simp [periodicSinePhaseMismatch, onePlusThreeMinusSign,
      Fin.sum_univ_four] at hfrequency
    linarith
  rcases threeToOne_resonance_has_zero_input hmomentum' hfrequency' with
    h₁ | h₂ | h₃
  · exact ⟨1, h₁⟩
  · exact ⟨2, h₂⟩
  · exact ⟨3, h₃⟩

/-- Sign decoration `(-,+,+,+)`, the reversed orientation of the same
one-to-three process. -/
def oneMinusThreePlusSign : Fin 4 → InteractionSign :=
  ![.minus, .plus, .plus, .plus]

/-- Reversing every sign does not restore a nonzero `1 ↔ 3` resonance. -/
theorem oneMinusThreePlus_resonance_has_zero_mode
    {N : Nat} [NeZero N] (modes : Fin 4 → Site N)
    (hmomentum : FourierMomentumBalanced oneMinusThreePlusSign modes)
    (hfrequency : periodicSinePhaseMismatch oneMinusThreePlusSign modes = 0) :
    ∃ r, modes r = 0 := by
  have hmomentum' : modes 0 = modes 1 + modes 2 + modes 3 := by
    simp [FourierMomentumBalanced, signedFourierMomentum,
      oneMinusThreePlusSign, Fin.sum_univ_four,
      interactionSignMomentum] at hmomentum
    linear_combination -hmomentum
  have hfrequency' : periodicSineFrequency N (modes 0) =
      periodicSineFrequency N (modes 1) +
        periodicSineFrequency N (modes 2) +
          periodicSineFrequency N (modes 3) := by
    simp [periodicSinePhaseMismatch, oneMinusThreePlusSign,
      Fin.sum_univ_four] at hfrequency
    linarith
  rcases threeToOne_resonance_has_zero_input hmomentum' hfrequency' with
    h₁ | h₂ | h₃
  · exact ⟨1, h₁⟩
  · exact ⟨2, h₂⟩
  · exact ⟨3, h₃⟩

end

end ArchonPhysics.EqualMassPeriodicFPUTFourWaveSectorExclusion
