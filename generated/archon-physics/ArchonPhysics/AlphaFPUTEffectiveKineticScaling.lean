import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebraic kinetic scales after alpha-FPUT normal forms

If the dimensionless alpha-FPUT weak parameter is `epsilon`, eliminating the
quadratic three-wave source produces an effective quartic amplitude of order
`epsilon^2`.  A four-wave golden-rule rate is therefore of order
`epsilon^4`.  In a finite-volume regime where disconnected quartets must be
eliminated further, the first connected six-wave amplitude is of order
`epsilon^4`, hence its golden-rule rate is of order `epsilon^8`.

This module proves only those exact power identities.  It does not prove that
the relevant effective coefficient is nonzero, that a collision network is
connected, or that the Hamiltonian dynamics converges to a kinetic equation.
-/

namespace ArchonPhysics.AlphaFPUTEffectiveKineticScaling

noncomputable section

/-- Effective quartic amplitude after one alpha-FPUT normal-form step. -/
def effectiveFourWaveCoupling (epsilon : Real) : Real := epsilon ^ 2

/-- Golden-rule rate obtained by squaring the effective quartic amplitude. -/
def effectiveFourWaveRate (epsilon : Real) : Real :=
  effectiveFourWaveCoupling epsilon ^ 2

/-- Corresponding inverse rate. -/
def effectiveFourWaveKineticTime (epsilon : Real) : Real :=
  1 / effectiveFourWaveRate epsilon

/-- Effective connected six-wave amplitude after the further finite-volume
normal-form eliminations. -/
def effectiveSixWaveCoupling (epsilon : Real) : Real := epsilon ^ 4

/-- Golden-rule rate obtained by squaring the effective six-wave amplitude. -/
def effectiveSixWaveRate (epsilon : Real) : Real :=
  effectiveSixWaveCoupling epsilon ^ 2

/-- Corresponding inverse six-wave rate. -/
def effectiveSixWaveKineticTime (epsilon : Real) : Real :=
  1 / effectiveSixWaveRate epsilon

theorem effectiveFourWaveRate_eq_pow_four (epsilon : Real) :
    effectiveFourWaveRate epsilon = epsilon ^ 4 := by
  unfold effectiveFourWaveRate effectiveFourWaveCoupling
  ring

theorem effectiveSixWaveRate_eq_pow_eight (epsilon : Real) :
    effectiveSixWaveRate epsilon = epsilon ^ 8 := by
  unfold effectiveSixWaveRate effectiveSixWaveCoupling
  ring

theorem effectiveFourWaveKineticTime_eq_inv_pow_four (epsilon : Real) :
    effectiveFourWaveKineticTime epsilon = 1 / epsilon ^ 4 := by
  rw [effectiveFourWaveKineticTime, effectiveFourWaveRate_eq_pow_four]

theorem effectiveSixWaveKineticTime_eq_inv_pow_eight (epsilon : Real) :
    effectiveSixWaveKineticTime epsilon = 1 / epsilon ^ 8 := by
  rw [effectiveSixWaveKineticTime, effectiveSixWaveRate_eq_pow_eight]

/-- Dimensionless alpha-FPUT weak parameter from a force coefficient and
energy density, in the conventional amplitude normalization. -/
def alphaFPUTWeakParameter (alpha energyDensity : Real) : Real :=
  alpha * Real.sqrt energyDensity

theorem alphaFPUTWeakParameter_pow_four
    {energyDensity : Real} (henergy : 0 ≤ energyDensity) (alpha : Real) :
    alphaFPUTWeakParameter alpha energyDensity ^ 4 =
      alpha ^ 4 * energyDensity ^ 2 := by
  unfold alphaFPUTWeakParameter
  have hsqrt : Real.sqrt energyDensity ^ 2 = energyDensity :=
    Real.sq_sqrt henergy
  calc
    (alpha * Real.sqrt energyDensity) ^ 4 =
        alpha ^ 4 * (Real.sqrt energyDensity ^ 2) ^ 2 := by ring
    _ = alpha ^ 4 * energyDensity ^ 2 := by rw [hsqrt]

theorem alphaFPUTWeakParameter_pow_eight
    {energyDensity : Real} (henergy : 0 ≤ energyDensity) (alpha : Real) :
    alphaFPUTWeakParameter alpha energyDensity ^ 8 =
      alpha ^ 8 * energyDensity ^ 4 := by
  unfold alphaFPUTWeakParameter
  have hsqrt : Real.sqrt energyDensity ^ 2 = energyDensity :=
    Real.sq_sqrt henergy
  calc
    (alpha * Real.sqrt energyDensity) ^ 8 =
        alpha ^ 8 * (Real.sqrt energyDensity ^ 2) ^ 4 := by ring
    _ = alpha ^ 8 * energyDensity ^ 4 := by rw [hsqrt]

/-- Exact energy-density form of the four-wave inverse rate. -/
theorem effectiveFourWaveKineticTime_weakParameter
    {energyDensity : Real} (henergy : 0 ≤ energyDensity) (alpha : Real) :
    effectiveFourWaveKineticTime
        (alphaFPUTWeakParameter alpha energyDensity) =
      1 / (alpha ^ 4 * energyDensity ^ 2) := by
  rw [effectiveFourWaveKineticTime_eq_inv_pow_four,
    alphaFPUTWeakParameter_pow_four henergy]

/-- Exact energy-density form of the finite-volume six-wave inverse rate. -/
theorem effectiveSixWaveKineticTime_weakParameter
    {energyDensity : Real} (henergy : 0 ≤ energyDensity) (alpha : Real) :
    effectiveSixWaveKineticTime
        (alphaFPUTWeakParameter alpha energyDensity) =
      1 / (alpha ^ 8 * energyDensity ^ 4) := by
  rw [effectiveSixWaveKineticTime_eq_inv_pow_eight,
    alphaFPUTWeakParameter_pow_eight henergy]

end

end ArchonPhysics.AlphaFPUTEffectiveKineticScaling
