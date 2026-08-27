import ArchonPhysics.FreeFPUTA0DirectCubicBridge
import ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion

/-!
# Separation of the free A0 and quadratic A1 phase charges

The singleton free initial character carries one signed phase factor, whereas
every quadratic first-Picard character carries two signed phase factors.  Their
integer charges therefore cannot agree: the sum of all charge coordinates is
odd for `A0` and even for `A1`.

The proof keeps repeated input modes and opposite-sign cancellations.  As an
exact consequence, every `A0`/`A1` equal-charge selector is empty and the
first-order Haar interference vanishes for arbitrary deterministic
coefficients.  No distinct-mode assumption, probabilistic cancellation,
collision interpretation, or long-time limit is used.
-/

namespace ArchonPhysics.FreeFPUTA0A1ChargeSeparation

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The unique free `A0` charge cannot equal the charge of any quadratic `A1`
term.  Summing all charge coordinates reduces the assertion to the parity
separation between one sign and two signs. -/
theorem freeInitialPhaseCharge_ne_quadraticPhaseCharge
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    freeInitialPhaseCharge observed 0 ≠ quadraticPhaseCharge term := by
  classical
  rcases term with ⟨modes, s₀, s₁⟩
  intro hcharge
  have hsum := congrArg
    (fun charge : Lattice.Site N → Int ↦ ∑ mode, charge mode) hcharge
  fin_cases s₀ <;> fin_cases s₁ <;>
    simp [freeInitialPhaseCharge, quadraticPhaseCharge, binarySignedMode,
      SignedMode.charge, binaryPhaseSign, PhaseSign.exponent,
      Finset.sum_add_distrib] at hsum

/-- Since no `A0` and quadratic `A1` indices have equal charge, their complete
equal-charge complex cross sum vanishes for arbitrary coefficients. -/
theorem equalChargeCrossPairSum_freeInitial_quadratic_eq_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (zCoefficient : FreeInitialPhaseTerm → Complex)
    (wCoefficient : QuadraticPhaseTerm N → Complex) :
    equalChargeCrossPairSum zCoefficient (freeInitialPhaseCharge observed)
        wCoefficient quadraticPhaseCharge = 0 := by
  classical
  unfold equalChargeCrossPairSum
  rw [Fin.sum_univ_one]
  apply Finset.sum_eq_zero
  intro term hterm
  rw [if_neg
    (freeInitialPhaseCharge_ne_quadraticPhaseCharge observed term)]

/-- The real `A0`/quadratic-`A1` equal-charge interference is identically zero
for arbitrary coefficients. -/
theorem equalChargeFamilyInterference_freeInitial_quadratic_eq_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (zCoefficient : FreeInitialPhaseTerm → Complex)
    (wCoefficient : QuadraticPhaseTerm N → Complex) :
    equalChargeFamilyInterference zCoefficient (freeInitialPhaseCharge observed)
        wCoefficient quadraticPhaseCharge = 0 := by
  unfold equalChargeFamilyInterference
  rw [equalChargeCrossPairSum_freeInitial_quadratic_eq_zero]
  norm_num

/-- Exact vanishing of the first-order Haar coefficient between the singleton
free `A0` family and an arbitrary quadratic `A1` family. -/
theorem integral_secondMomentFirst_freeInitial_quadratic_eq_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (zCoefficient : FreeInitialPhaseTerm → Complex)
    (wCoefficient : QuadraticPhaseTerm N → Complex) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      secondMomentFirst
        (finitePhaseCorrection zCoefficient
          (freeInitialPhaseCharge observed) phase)
        (finitePhaseCorrection wCoefficient quadraticPhaseCharge phase)
      ∂finitePhaseHaarLaw (Lattice.Site N)) = 0 := by
  rw [integral_secondMomentFirst_finitePhaseCorrections,
    equalChargeFamilyInterference_freeInitial_quadratic_eq_zero]

end

end ArchonPhysics.FreeFPUTA0A1ChargeSeparation
