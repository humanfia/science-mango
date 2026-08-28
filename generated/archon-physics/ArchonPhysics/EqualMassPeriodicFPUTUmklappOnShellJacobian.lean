import ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

/-!
# Equal-mass periodic FPUT: exact Umklapp on-shell Jacobian

For fixed external momenta `k₀,k₁`, the one-wrap four-wave mismatch is

`4 * (A - B * sin θ)`.

This file identifies the exact transverse Jacobian at every resonant root.
The resulting discriminant is an explicit function of `k₀,k₁`; positivity of
that discriminant is exactly the nondegenerate resonance condition.  This is
an algebraic input to the collision-density/coarea step and does not assume a
kinetic equation.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

noncomputable section

/-- The constant term `A` in the reduced Umklapp mismatch. -/
def umklappResonanceNumerator (k₀ k₁ : Real) : Real :=
  Real.sin ((k₀ + k₁) / 4) * Real.cos ((k₀ - k₁) / 4)

/-- The coefficient `B` of the moving sine in the reduced mismatch. -/
def umklappResonanceDenominator (k₀ k₁ : Real) : Real :=
  Real.cos ((k₀ + k₁) / 4)

/-- Squared transverse Jacobian divided by four, evaluated on shell. -/
def umklappTransverseDiscriminant (k₀ k₁ : Real) : Real :=
  umklappResonanceDenominator k₀ k₁ ^ 2 -
    umklappResonanceNumerator k₀ k₁ ^ 2

/-- The transparent open condition for a nondegenerate Umklapp shell. -/
theorem umklappTransverseDiscriminant_pos_iff
    (k₀ k₁ : Real) :
    0 < umklappTransverseDiscriminant k₀ k₁ ↔
      |umklappResonanceNumerator k₀ k₁| <
        |umklappResonanceDenominator k₀ k₁| := by
  rw [umklappTransverseDiscriminant]
  constructor
  · intro h
    rw [← sq_lt_sq]
    linarith
  · intro h
    rw [← sq_lt_sq] at h
    linarith

/-- At a resonant root, the squared free-momentum derivative is exactly four
times the explicit transverse discriminant. -/
theorem umklappK₂DerivativeFactor_sq_of_resonant
    {k₀ k₁ k₂ : Real}
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    umklappK₂DerivativeFactor k₀ k₁ k₂ ^ 2 =
      4 * umklappTransverseDiscriminant k₀ k₁ := by
  rw [umklappReducedFourWaveMismatch_factor] at hresonant
  have hrelation :
      umklappResonanceNumerator k₀ k₁ =
        umklappResonanceDenominator k₀ k₁ *
          Real.sin ((2 * k₂ - k₀ - k₁) / 4) := by
    dsimp [umklappResonanceNumerator, umklappResonanceDenominator]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq
    ((2 * k₂ - k₀ - k₁) / 4)
  have hrelationSquare := congrArg (fun value : Real ↦ value ^ 2) hrelation
  rw [umklappK₂DerivativeFactor]
  dsimp [umklappTransverseDiscriminant, umklappResonanceNumerator,
    umklappResonanceDenominator] at hrelationSquare ⊢
  nlinarith

/-- Positive discriminant excludes a tangential resonant root. -/
theorem umklappK₂DerivativeFactor_ne_zero_of_resonant
    {k₀ k₁ k₂ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    umklappK₂DerivativeFactor k₀ k₁ k₂ ≠ 0 := by
  intro hzero
  have hsquare := umklappK₂DerivativeFactor_sq_of_resonant hresonant
  rw [hzero] at hsquare
  norm_num at hsquare
  linarith

/-- Exact absolute Jacobian on every nondegenerate Umklapp resonant branch. -/
theorem abs_umklappK₂DerivativeFactor_of_resonant
    {k₀ k₁ k₂ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    |umklappK₂DerivativeFactor k₀ k₁ k₂| =
      2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁) := by
  have hsquare := umklappK₂DerivativeFactor_sq_of_resonant hresonant
  have hsqrt := Real.sq_sqrt hdisc.le
  have habsSquare :
      |umklappK₂DerivativeFactor k₀ k₁ k₂| ^ 2 =
        4 * umklappTransverseDiscriminant k₀ k₁ := by
    simpa only [sq_abs] using hsquare
  nlinarith [abs_nonneg (umklappK₂DerivativeFactor k₀ k₁ k₂),
    Real.sqrt_nonneg (umklappTransverseDiscriminant k₀ k₁)]

/-- Consequently the physical coarea weight has a closed inverse-Jacobian
factor, independent of which nondegenerate Umklapp root is chosen. -/
theorem inv_abs_umklappK₂DerivativeFactor_of_resonant
    {k₀ k₁ k₂ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    |umklappK₂DerivativeFactor k₀ k₁ k₂|⁻¹ =
      (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁))⁻¹ := by
  rw [abs_umklappK₂DerivativeFactor_of_resonant hdisc hresonant]

end


end ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
