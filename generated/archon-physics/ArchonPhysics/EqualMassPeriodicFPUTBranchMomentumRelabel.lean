import ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
import ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave

/-!
# Branch-to-physical momentum relabelling for periodic alpha-FPUT

The exact interaction-picture equation labels a branch by a raw Fourier
index and by a phase/conjugate sign.  Its physical travelling-wave momentum
is the raw index on the phase branch and the negated index on the conjugate
branch.  This module proves that this relabelling turns every literal
convolution `k = l + (k-l)` into the same signed three-leg momentum and
frequency decoration used by the finite three-wave-shell results.

All statements are exact at finite volume and cover all eight choices of
output, left-input, and right-input branch.  No random-phase, kinetic, or
limiting hypothesis is introduced.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTBranchMomentumRelabel

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-! ## Physical momentum and frequency invariance -/

/-- Physical travelling-wave momentum represented by a signed branch at a
raw complex Fourier index. -/
def phaseSignedMomentum {N : Nat} : PhaseSign → Site N → Site N
  | .phase, rawMode => rawMode
  | .conjugate, rawMode => -rawMode

@[simp] theorem phaseSignedMomentum_phase
    {N : Nat} (rawMode : Site N) :
    phaseSignedMomentum .phase rawMode = rawMode := rfl

@[simp] theorem phaseSignedMomentum_conjugate
    {N : Nat} (rawMode : Site N) :
    phaseSignedMomentum .conjugate rawMode = -rawMode := rfl

@[simp] theorem phaseSignedMomentum_eq_zero_iff
    {N : Nat} (sign : PhaseSign) (rawMode : Site N) :
    phaseSignedMomentum sign rawMode = 0 ↔ rawMode = 0 := by
  cases sign <;> simp [phaseSignedMomentum]

/-- The positive acoustic dispersion is invariant under reversal of a
periodic Fourier momentum. -/
theorem periodicSineFrequency_neg
    (N : Nat) [NeZero N] (mode : Site N) :
    periodicSineFrequency N (-mode) = periodicSineFrequency N mode := by
  by_cases hmode : mode = 0
  · subst mode
    simp
  · let _ : NeZero mode := ⟨hmode⟩
    unfold periodicSineFrequency
    rw [ZMod.val_neg_of_ne_zero]
    have hN : (N : Real) ≠ 0 := by
      exact_mod_cast NeZero.ne N
    have hcast : ((N - mode.val : Nat) : Real) =
        (N : Real) - (mode.val : Real) := by
      rw [Nat.cast_sub (Nat.le_of_lt mode.val_lt)]
    rw [hcast]
    have hangle :
        Real.pi * ((N : Real) - (mode.val : Real)) / (N : Real) =
          Real.pi - Real.pi * (mode.val : Real) / (N : Real) := by
      field_simp
    rw [hangle, Real.sin_pi_sub]

/-- Consequently the positive acoustic frequency is unchanged by the
phase/conjugate momentum relabelling. -/
@[simp] theorem periodicSineFrequency_phaseSignedMomentum
    (N : Nat) [NeZero N] (sign : PhaseSign) (rawMode : Site N) :
    periodicSineFrequency N (phaseSignedMomentum sign rawMode) =
      periodicSineFrequency N rawMode := by
  cases sign
  · rfl
  · exact periodicSineFrequency_neg N rawMode

/-- The square-root frequency used by the exact Hamiltonian branch equation
is the normalized sine frequency used by the shell analysis. -/
theorem equalMassFourierFrequency_eq_periodicSineFrequency
    (N : Nat) [NeZero N] (mode : Site N) :
    equalMassFourierFrequency N mode = periodicSineFrequency N mode := by
  exact sqrt_cleanCycleModeEnergy_eq_periodicSineFrequency N mode

/-! ## Correct output/input collision signs -/

/-- An output branch contributes its own phase sign to an
output-minus-input mismatch. -/
def phaseSignToOutputInteractionSign : PhaseSign → InteractionSign
  | .phase => .plus
  | .conjugate => .minus

@[simp] theorem coefficient_phaseSignToOutputInteractionSign
    (sign : PhaseSign) :
    (phaseSignToOutputInteractionSign sign).coefficient =
      phaseSignReal sign := by
  cases sign <;>
    simp [phaseSignToOutputInteractionSign, phaseSignReal,
      PhaseSign.exponent, InteractionSign.coefficient]

/-- After physical-momentum relabelling, the signed output momentum is the
raw output index for either branch. -/
@[simp] theorem interactionSignMomentum_output_relabel
    {N : Nat} (sign : PhaseSign) (rawMode : Site N) :
    interactionSignMomentum (phaseSignToOutputInteractionSign sign)
        (phaseSignedMomentum sign rawMode) = rawMode := by
  cases sign <;>
    simp [phaseSignToOutputInteractionSign, interactionSignMomentum,
      phaseSignedMomentum]

/-- After physical-momentum relabelling, the signed input momentum is minus
the raw input index for either branch. -/
@[simp] theorem interactionSignMomentum_input_relabel
    {N : Nat} (sign : PhaseSign) (rawMode : Site N) :
    interactionSignMomentum (phaseSignToInputInteractionSign sign)
        (phaseSignedMomentum sign rawMode) = -rawMode := by
  cases sign <;>
    simp [phaseSignToInputInteractionSign, interactionSignMomentum,
      phaseSignedMomentum]

/-! ## The relabelled three-leg decoration -/

/-- Output sign followed by the two input signs, with the input signs
reversed because the collision mismatch is output minus inputs. -/
def branchRelabelledThreeWaveSign
    (outputSign leftSign rightSign : PhaseSign) :
    Fin 3 → InteractionSign :=
  Fin.cons (phaseSignToOutputInteractionSign outputSign)
    (Fin.cons (phaseSignToInputInteractionSign leftSign)
      (fun _ ↦ phaseSignToInputInteractionSign rightSign))

/-- Physical momenta represented by the three raw labels in a literal
quadratic convolution. -/
def branchRelabelledThreeWaveMode
    {N : Nat} (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) : Fin 3 → Site N :=
  Fin.cons (phaseSignedMomentum outputSign k)
    (Fin.cons (phaseSignedMomentum leftSign l)
      (fun _ ↦ phaseSignedMomentum rightSign (k - l)))

@[simp] theorem branchRelabelledThreeWaveSign_zero
    (outputSign leftSign rightSign : PhaseSign) :
    branchRelabelledThreeWaveSign outputSign leftSign rightSign 0 =
      phaseSignToOutputInteractionSign outputSign := rfl

@[simp] theorem branchRelabelledThreeWaveSign_one
    (outputSign leftSign rightSign : PhaseSign) :
    branchRelabelledThreeWaveSign outputSign leftSign rightSign 1 =
      phaseSignToInputInteractionSign leftSign := rfl

@[simp] theorem branchRelabelledThreeWaveSign_two
    (outputSign leftSign rightSign : PhaseSign) :
    branchRelabelledThreeWaveSign outputSign leftSign rightSign 2 =
      phaseSignToInputInteractionSign rightSign := rfl

@[simp] theorem branchRelabelledThreeWaveMode_zero
    {N : Nat} (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    branchRelabelledThreeWaveMode k l outputSign leftSign rightSign 0 =
      phaseSignedMomentum outputSign k := rfl

@[simp] theorem branchRelabelledThreeWaveMode_one
    {N : Nat} (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    branchRelabelledThreeWaveMode k l outputSign leftSign rightSign 1 =
      phaseSignedMomentum leftSign l := rfl

@[simp] theorem branchRelabelledThreeWaveMode_two
    {N : Nat} (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    branchRelabelledThreeWaveMode k l outputSign leftSign rightSign 2 =
      phaseSignedMomentum rightSign (k - l) := rfl

/-- Every raw convolution `k = l + (k-l)` becomes an exactly balanced
signed physical-momentum triple, for all branch choices. -/
theorem branchRelabelledThreeWave_fourierMomentumBalanced
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    FourierMomentumBalanced
      (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
      (branchRelabelledThreeWaveMode k l
        outputSign leftSign rightSign) := by
  unfold FourierMomentumBalanced signedFourierMomentum
  rw [Fin.sum_univ_three]
  simp
  abel

/-- The shell mismatch of the relabelled physical triple is exactly the
branch mismatch in the Hamiltonian interaction-picture equation. -/
theorem periodicSinePhaseMismatch_branchRelabelledThreeWave
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    periodicSinePhaseMismatch
        (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
        (branchRelabelledThreeWaveMode k l
          outputSign leftSign rightSign) =
      equalMassQuadraticBranchMismatch k l
        outputSign leftSign rightSign := by
  unfold periodicSinePhaseMismatch equalMassQuadraticBranchMismatch
  rw [Fin.sum_univ_three]
  simp [
    equalMassFourierFrequency_eq_periodicSineFrequency,
    coefficient_phaseSignToInputInteractionSign, phaseSignReal]
  ring

/-- One bundled endpoint: the relabelled decoration simultaneously carries
the exact Fourier selector and the exact interaction-picture phase. -/
theorem branchRelabelledThreeWave_exactDecoration
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) :
    FourierMomentumBalanced
        (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
        (branchRelabelledThreeWaveMode k l
          outputSign leftSign rightSign) ∧
      periodicSinePhaseMismatch
          (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
          (branchRelabelledThreeWaveMode k l
            outputSign leftSign rightSign) =
        equalMassQuadraticBranchMismatch k l
          outputSign leftSign rightSign :=
  ⟨branchRelabelledThreeWave_fourierMomentumBalanced
      k l outputSign leftSign rightSign,
    periodicSinePhaseMismatch_branchRelabelledThreeWave
      k l outputSign leftSign rightSign⟩

/-! ## Consequences for the actual branch mismatch -/

/-- A literal quadratic branch term with three nonzero raw Fourier modes is
off the exact three-wave shell, for every choice of the three branch signs. -/
theorem equalMassQuadraticBranchMismatch_ne_zero_of_nonzero
    {N : Nat} [NeZero N] {k l : Site N}
    (outputSign leftSign rightSign : PhaseSign)
    (hk : k ≠ 0) (hl : l ≠ 0) (hright : k - l ≠ 0) :
    equalMassQuadraticBranchMismatch k l
      outputSign leftSign rightSign ≠ 0 := by
  intro hmismatch
  have hfrequency :
      periodicSinePhaseMismatch
          (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
          (branchRelabelledThreeWaveMode k l
            outputSign leftSign rightSign) = 0 :=
    (periodicSinePhaseMismatch_branchRelabelledThreeWave
      k l outputSign leftSign rightSign).trans hmismatch
  obtain ⟨slot, hzero⟩ := threeWave_fourier_resonance_has_zero_mode
    (branchRelabelledThreeWaveSign outputSign leftSign rightSign)
    (branchRelabelledThreeWaveMode k l outputSign leftSign rightSign)
    (branchRelabelledThreeWave_fourierMomentumBalanced
      k l outputSign leftSign rightSign)
    hfrequency
  fin_cases slot <;> simp [hk, hl, hright] at hzero

/-- Quantitative fixed-volume version: the exact branch mismatch is bounded
below by the already-proved nonzero momentum-shell gap.  This bound is not
claimed to be uniform as `N → ∞`. -/
theorem finiteNonzeroMomentumThreeWaveGap_le_branchMismatch
    {N : Nat} [NeZero N] {k l : Site N}
    (outputSign leftSign rightSign : PhaseSign)
    (hk : k ≠ 0) (hl : l ≠ 0) (hright : k - l ≠ 0) :
    finiteNonzeroMomentumThreeWaveGap N ≤
      |equalMassQuadraticBranchMismatch k l
        outputSign leftSign rightSign| := by
  let sign := branchRelabelledThreeWaveSign
    outputSign leftSign rightSign
  let modes := branchRelabelledThreeWaveMode k l
    outputSign leftSign rightSign
  have hnonzero : ∀ slot, modes slot ≠ 0 := by
    intro slot
    fin_cases slot <;> simp [modes, hk, hl, hright]
  have hactive : IsNonzeroMomentumTriple (sign, modes) :=
    ⟨hnonzero,
      branchRelabelledThreeWave_fourierMomentumBalanced
        k l outputSign leftSign rightSign⟩
  have hgap := finiteNonzeroMomentumThreeWaveGap_le N (sign, modes) hactive
  rw [← periodicSinePhaseMismatch_branchRelabelledThreeWave
    k l outputSign leftSign rightSign]
  exact hgap

end

end ArchonPhysics.EqualMassPeriodicFPUTBranchMomentumRelabel
