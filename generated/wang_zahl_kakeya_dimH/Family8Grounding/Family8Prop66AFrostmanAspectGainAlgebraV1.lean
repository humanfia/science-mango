import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

/-!
# Proposition 6.6(A): exact scalar target and Family 8 RHS algebra

This file records only the lossless scalar algebra in Equation (32) of
Guth--Wang--Zahl, Proposition 6.6(A).  It does **not** assert the proposition's
geometric/analytic multiplicity estimate.  In particular, no structure field
or renamed copy of that missing estimate is introduced here.

The important distinction is that the paper applies Proposition 6.6(A) with
`beta = gamma`; the exponent `3 * gamma / 2` is the aspect-ratio gain produced
by tube families factoring through planks.  It is not obtained by specializing
the Katz--Tao plank exponent itself to `3 / 2`.
-/

open scoped ENNReal NNReal

namespace Family8Prop66AFrostmanAspectGainAlgebraV1

open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- The paper normalization `delta^2 * #T` in Proposition 6.6(A). -/
def proposition66ACardScaleVolume (delta : NNReal) (tubeCount : Nat) : ENNReal :=
  (delta : ENNReal) ^ (2 : Nat) * (tubeCount : ENNReal)

/-- The exact displayed right-hand side of Proposition 6.6(A), Equation (32),
with numerical prefactor one.  This is a scalar definition, not a theorem
claiming that average multiplicity is bounded by it. -/
def proposition66AFrostmanFactor
    (delta a b : NNReal) (tubeCount : Nat)
    (CF : ENNReal) (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) *
    CF ^ (1 - beta / 2) *
      ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
        (delta : ENNReal) ^ (-2 * beta) *
          proposition66ACardScaleVolume delta tubeCount ^ (1 - beta / 2)

/-- The entire new content of the Proposition 6.6(A) target, relative to the
Family 8 Frostman multiplicity RHS, is the Frostman-constant loss times the
`(a / b)^(3 beta / 2)` aspect gain. -/
def proposition66AFrostmanAspectGain
    (a b : NNReal) (CF : ENNReal) (beta : Real) : ENNReal :=
  CF ^ (1 - beta / 2) *
    ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2)

/-- Lossless normalization of Equation (32) by the already-audited Family 8
Frostman RHS. -/
theorem proposition66AFrostmanFactor_eq_gain_mul_frostmanMultiplicityRHS
    (delta a b : NNReal) (tubeCount : Nat)
    (CF : ENNReal) (epsilon beta : Real) :
    proposition66AFrostmanFactor delta a b tubeCount CF epsilon beta =
      proposition66AFrostmanAspectGain a b CF beta *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta tubeCount) epsilon beta := by
  unfold proposition66AFrostmanFactor proposition66AFrostmanAspectGain
    frostmanMultiplicityRHS
  ac_rfl

/-- Section 8 uses `beta = gamma`; this specialization exposes the literal
`(a / b)^(3 * gamma / 2)` gain without changing parameter semantics. -/
theorem proposition66AFrostmanFactor_eq_sectionEightGain
    (delta a b : NNReal) (tubeCount : Nat)
    (CF : ENNReal) (epsilon gamma : Real) :
    proposition66AFrostmanFactor delta a b tubeCount CF epsilon gamma =
      (CF ^ (1 - gamma / 2) *
        ((a : ENNReal) / (b : ENNReal)) ^ (3 * gamma / 2)) *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta tubeCount) epsilon gamma := by
  exact proposition66AFrostmanFactor_eq_gain_mul_frostmanMultiplicityRHS
    delta a b tubeCount CF epsilon gamma

/-- A quantitative aspect-ratio upper bound gives exactly the corresponding
small-scale power gain.  This is the numerical step used after the geometric
plank factorization has produced `a / b`. -/
theorem aspect_three_halves_rpow_le
    {delta : NNReal} {aspect : ENNReal} {q beta : Real}
    (haspect : aspect ≤ (delta : ENNReal) ^ q)
    (hbeta : 0 ≤ beta) :
    aspect ^ (3 * beta / 2) ≤
      (delta : ENNReal) ^ (q * (3 * beta / 2)) := by
  have hexponent : 0 ≤ 3 * beta / 2 := by linarith
  calc
    aspect ^ (3 * beta / 2) ≤
        ((delta : ENNReal) ^ q) ^ (3 * beta / 2) :=
      ENNReal.rpow_le_rpow haspect hexponent
    _ = (delta : ENNReal) ^ (q * (3 * beta / 2)) :=
      (ENNReal.rpow_mul (delta : ENNReal) q (3 * beta / 2)).symm

/-- Mechanical power-budget form of the Proposition 6.6(A) scalar.  The two
premises are genuine upper bounds on the Frostman constant and aspect ratio;
the missing analytic proposition is not among the inputs. -/
theorem proposition66AFrostmanFactor_le_powerBudget
    {delta a b : NNReal} {tubeCount : Nat}
    {CF : ENNReal} {epsilon beta eta q : Real}
    (hCF : CF ≤ (delta : ENNReal) ^ (-eta))
    (haspect : (a : ENNReal) / (b : ENNReal) ≤
      (delta : ENNReal) ^ q)
    (hbeta : 0 ≤ beta) (hbetaTwo : beta ≤ 2) :
    proposition66AFrostmanFactor delta a b tubeCount CF epsilon beta ≤
      ((delta : ENNReal) ^ ((-eta) * (1 - beta / 2)) *
        (delta : ENNReal) ^ (q * (3 * beta / 2))) *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta tubeCount) epsilon beta := by
  have hOneSub : 0 ≤ 1 - beta / 2 := by linarith
  have hCFpow :
      CF ^ (1 - beta / 2) ≤
        (delta : ENNReal) ^ ((-eta) * (1 - beta / 2)) := by
    calc
      CF ^ (1 - beta / 2) ≤
          ((delta : ENNReal) ^ (-eta)) ^ (1 - beta / 2) :=
        ENNReal.rpow_le_rpow hCF hOneSub
      _ = (delta : ENNReal) ^ ((-eta) * (1 - beta / 2)) :=
        (ENNReal.rpow_mul (delta : ENNReal) (-eta) (1 - beta / 2)).symm
  have haspectPow :
      ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) ≤
        (delta : ENNReal) ^ (q * (3 * beta / 2)) :=
    aspect_three_halves_rpow_le haspect hbeta
  rw [proposition66AFrostmanFactor_eq_gain_mul_frostmanMultiplicityRHS]
  unfold proposition66AFrostmanAspectGain
  have hgain :
      CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) ≤
        (delta : ENNReal) ^ ((-eta) * (1 - beta / 2)) *
          (delta : ENNReal) ^ (q * (3 * beta / 2)) :=
    mul_le_mul hCFpow haspectPow (by positivity) (by positivity)
  calc
    (CF ^ (1 - beta / 2) *
        ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2)) *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta tubeCount) epsilon beta =
      frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta tubeCount) epsilon beta *
        (CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2)) := by
        ac_rfl
    _ ≤ frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta tubeCount) epsilon beta *
        ((delta : ENNReal) ^ ((-eta) * (1 - beta / 2)) *
          (delta : ENNReal) ^ (q * (3 * beta / 2))) :=
      mul_le_mul_right hgain _
    _ = ((delta : ENNReal) ^ ((-eta) * (1 - beta / 2)) *
          (delta : ENNReal) ^ (q * (3 * beta / 2))) *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta tubeCount) epsilon beta := by
      ac_rfl

#print axioms proposition66AFrostmanFactor_eq_gain_mul_frostmanMultiplicityRHS
#print axioms proposition66AFrostmanFactor_eq_sectionEightGain
#print axioms aspect_three_halves_rpow_le
#print axioms proposition66AFrostmanFactor_le_powerBudget

end

end Family8Prop66AFrostmanAspectGainAlgebraV1
