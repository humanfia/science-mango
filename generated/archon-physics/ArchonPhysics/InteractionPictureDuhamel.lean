import ArchonPhysics.PhaseRenormalization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact finite-time interaction-picture Duhamel identity

This is the model-independent integrating-factor step used in phonon kinetic
expansions.  If a complex amplitude obeys

`a' = F - i * Omega * a`,

then its interaction-picture amplitude has derivative
`exp(i * Omega * t) * F`, and the fundamental theorem of calculus gives the
exact finite-time Duhamel formula.

The forcing equation and interval integrability are explicit hypotheses.  No
microscopic mode equation, perturbation expansion, expectation, collision
operator, or kinetic limit is asserted.
-/

namespace ArchonPhysics.InteractionPictureDuhamel

open Set
open ArchonPhysics.PhaseRenormalization

noncomputable section

/-- The interaction-picture derivative after cancelling a supplied free
frequency drift. -/
theorem hasDerivAt_interactionPicture
    {Omega t : Real} {a : Real → Complex} {F : Real → Complex}
    (ha : HasDerivAt a
      (F t - (Complex.I * (Omega : Complex)) * a t) t) :
    HasDerivAt (fun s ↦ phaseRenormalize (Omega * s) (a s))
      (phaseFactor (Omega * t) * F t) t := by
  apply hasDerivAt_phaseRenormalize_of_sub_phaseDrift
  · simpa using (hasDerivAt_id t).const_mul Omega
  · exact ha

/-- A phase rotation followed by its opposite rotation is the identity. -/
@[simp] theorem phaseRenormalize_neg_phaseRenormalize
    (theta : Real) (z : Complex) :
    phaseRenormalize (-theta) (phaseRenormalize theta z) = z := by
  rw [phaseRenormalize, phaseRenormalize, phaseFactor, phaseFactor,
    ← mul_assoc, ← Complex.exp_add]
  simp

/-- Exact interaction-picture Duhamel formula on an arbitrary oriented real
interval from `0` to `t`. -/
theorem interactionPicture_eq_initial_add_integral
    {Omega t : Real} {a : Real → Complex} {F : Real → Complex}
    (ha : ∀ s ∈ uIcc 0 t, HasDerivAt a
      (F s - (Complex.I * (Omega : Complex)) * a s) s)
    (hIntegrable : IntervalIntegrable
      (fun s ↦ phaseFactor (Omega * s) * F s) MeasureTheory.volume 0 t) :
    phaseRenormalize (Omega * t) (a t) =
      a 0 + ∫ s in 0..t, phaseFactor (Omega * s) * F s := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ phaseRenormalize (Omega * s) (a s))
    (f' := fun s ↦ phaseFactor (Omega * s) * F s)
    (fun s hs ↦ hasDerivAt_interactionPicture (ha s hs)) hIntegrable
  rw [hFTC]
  simp [phaseRenormalize, phaseFactor]

/-- Equivalent Schrödinger-picture form, obtained by applying the inverse
phase to the exact interaction-picture identity. -/
theorem amplitude_eq_inversePhase_initial_add_integral
    {Omega t : Real} {a : Real → Complex} {F : Real → Complex}
    (ha : ∀ s ∈ uIcc 0 t, HasDerivAt a
      (F s - (Complex.I * (Omega : Complex)) * a s) s)
    (hIntegrable : IntervalIntegrable
      (fun s ↦ phaseFactor (Omega * s) * F s) MeasureTheory.volume 0 t) :
    a t = phaseRenormalize (-(Omega * t))
      (a 0 + ∫ s in 0..t, phaseFactor (Omega * s) * F s) := by
  rw [← interactionPicture_eq_initial_add_integral ha hIntegrable]
  simp

end

end ArchonPhysics.InteractionPictureDuhamel
