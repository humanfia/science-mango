import ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave

/-!
# Equal-mass periodic FPUT: the finite two-to-two momentum shell

For one fixed observed/output Fourier mode `k₀`, this module parametrizes the
exact lattice shell

`k₀ + k₁ = k₂ + k₃`

by the two free modes `(k₁, k₂)`, with `k₃ = k₀ + k₁ - k₂`.  Consequently the
shell has exactly `N²` elements.  The acoustic mismatch is rewritten in these
two free parameters and the two elementary pairing lines are shown to have
zero mismatch.

These are finite-volume identities only.  No nontrivial-resonance
classification or large-volume limit is asserted.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.Lattice

noncomputable section

/-- The exact `2 ↔ 2` momentum shell at fixed first/output mode `k₀`.
The stored modes are `(k₁, k₂, k₃)`. -/
abbrev TwoToTwoMomentumShell (N : Nat) (k₀ : Site N) :=
  {modes : Site N × (Site N × Site N) //
    k₀ + modes.1 = modes.2.1 + modes.2.2}

def shellModeOne
    {N : Nat} {k₀ : Site N} (shell : TwoToTwoMomentumShell N k₀) : Site N :=
  shell.1.1

def shellModeTwo
    {N : Nat} {k₀ : Site N} (shell : TwoToTwoMomentumShell N k₀) : Site N :=
  shell.1.2.1

def shellModeThree
    {N : Nat} {k₀ : Site N} (shell : TwoToTwoMomentumShell N k₀) : Site N :=
  shell.1.2.2

theorem shellMomentum_eq
    {N : Nat} {k₀ : Site N} (shell : TwoToTwoMomentumShell N k₀) :
    k₀ + shellModeOne shell =
      shellModeTwo shell + shellModeThree shell :=
  shell.2

/-- Complete a pair of free modes by solving the shell equation for `k₃`. -/
def twoToTwoShellFromFree
    {N : Nat} (k₀ : Site N) (free : Site N × Site N) :
    TwoToTwoMomentumShell N k₀ :=
  ⟨(free.1, (free.2, k₀ + free.1 - free.2)), by
    calc
      k₀ + free.1 = (k₀ + free.1 - free.2) + free.2 :=
        (sub_add_cancel (k₀ + free.1) free.2).symm
      _ = free.2 + (k₀ + free.1 - free.2) := add_comm _ _⟩

@[simp] theorem shellModeOne_twoToTwoShellFromFree
    {N : Nat} (k₀ : Site N) (free : Site N × Site N) :
    shellModeOne (twoToTwoShellFromFree k₀ free) = free.1 := rfl

@[simp] theorem shellModeTwo_twoToTwoShellFromFree
    {N : Nat} (k₀ : Site N) (free : Site N × Site N) :
    shellModeTwo (twoToTwoShellFromFree k₀ free) = free.2 := rfl

@[simp] theorem shellModeThree_twoToTwoShellFromFree
    {N : Nat} (k₀ : Site N) (free : Site N × Site N) :
    shellModeThree (twoToTwoShellFromFree k₀ free) =
      k₀ + free.1 - free.2 := rfl

/-- Explicit two-parameter equivalence for the full fixed-`k₀` shell. -/
def freePairEquivTwoToTwoMomentumShell
    {N : Nat} (k₀ : Site N) :
    (Site N × Site N) ≃ TwoToTwoMomentumShell N k₀ where
  toFun := twoToTwoShellFromFree k₀
  invFun shell := (shellModeOne shell, shellModeTwo shell)
  left_inv free := rfl
  right_inv shell := by
    apply Subtype.ext
    have hk₃ :
        k₀ + shellModeOne shell - shellModeTwo shell = shellModeThree shell := by
      calc
        k₀ + shellModeOne shell - shellModeTwo shell =
            (shellModeTwo shell + shellModeThree shell) - shellModeTwo shell := by
          rw [shellMomentum_eq shell]
        _ = shellModeThree shell := by abel
    change
      (shellModeOne shell,
          (shellModeTwo shell,
            k₀ + shellModeOne shell - shellModeTwo shell)) = shell.1
    rw [hk₃]
    rfl

/-- The fixed-output `2 ↔ 2` shell has two freely chosen Fourier modes. -/
theorem card_twoToTwoMomentumShell
    (N : Nat) [NeZero N] (k₀ : Site N) :
    Fintype.card (TwoToTwoMomentumShell N k₀) = N ^ 2 := by
  calc
    Fintype.card (TwoToTwoMomentumShell N k₀) =
        Fintype.card (Site N × Site N) :=
      (Fintype.card_congr (freePairEquivTwoToTwoMomentumShell k₀)).symm
    _ = Fintype.card (Site N) * Fintype.card (Site N) := Fintype.card_prod _ _
    _ = N ^ 2 := by rw [ZMod.card]; ring

/-! ## Reduced acoustic mismatch -/

/-- Acoustic `(+,+,-,-)` mismatch on the exact shell. -/
def twoToTwoShellMismatch
    {N : Nat} [NeZero N] (k₀ : Site N)
    (shell : TwoToTwoMomentumShell N k₀) : Real :=
  periodicSineFrequency N k₀ +
    periodicSineFrequency N (shellModeOne shell) -
    periodicSineFrequency N (shellModeTwo shell) -
    periodicSineFrequency N (shellModeThree shell)

/-- The same mismatch after eliminating `k₃` with the momentum selector. -/
def reducedTwoToTwoMismatch
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) : Real :=
  periodicSineFrequency N k₀ + periodicSineFrequency N k₁ -
    periodicSineFrequency N k₂ -
    periodicSineFrequency N (k₀ + k₁ - k₂)

theorem twoToTwoShellMismatch_fromFree
    {N : Nat} [NeZero N] (k₀ : Site N) (free : Site N × Site N) :
    twoToTwoShellMismatch k₀ (twoToTwoShellFromFree k₀ free) =
      reducedTwoToTwoMismatch k₀ free.1 free.2 := rfl

/-- Every shell mismatch rewrites to the two-free-mode reduced mismatch. -/
theorem twoToTwoShellMismatch_eq_reduced
    {N : Nat} [NeZero N] (k₀ : Site N)
    (shell : TwoToTwoMomentumShell N k₀) :
    twoToTwoShellMismatch k₀ shell =
      reducedTwoToTwoMismatch k₀
        (shellModeOne shell) (shellModeTwo shell) := by
  unfold twoToTwoShellMismatch reducedTwoToTwoMismatch
  have hk₃ :
      shellModeThree shell =
        k₀ + shellModeOne shell - shellModeTwo shell := by
    calc
      shellModeThree shell =
          (shellModeTwo shell + shellModeThree shell) - shellModeTwo shell := by
        abel
      _ = k₀ + shellModeOne shell - shellModeTwo shell := by
        rw [← shellMomentum_eq shell]
  rw [hk₃]

/-- Direct pairing line `(k₂,k₃)=(k₀,k₁)`. -/
theorem reducedTwoToTwoMismatch_pairing_left
    {N : Nat} [NeZero N] (k₀ k₁ : Site N) :
    reducedTwoToTwoMismatch k₀ k₁ k₀ = 0 := by
  unfold reducedTwoToTwoMismatch
  rw [show k₀ + k₁ - k₀ = k₁ by abel]
  ring

/-- Exchange pairing line `(k₂,k₃)=(k₁,k₀)`. -/
theorem reducedTwoToTwoMismatch_pairing_right
    {N : Nat} [NeZero N] (k₀ k₁ : Site N) :
    reducedTwoToTwoMismatch k₀ k₁ k₁ = 0 := by
  unfold reducedTwoToTwoMismatch
  rw [show k₀ + k₁ - k₁ = k₀ by abel]
  ring

end


end ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
