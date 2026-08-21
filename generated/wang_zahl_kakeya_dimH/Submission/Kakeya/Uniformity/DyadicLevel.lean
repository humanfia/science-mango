import ChallengeDeps

namespace Submission.Kakeya.Uniformity

/-!
# Dyadic levels

This module provides the discrete magnitude bands used in the finite
pigeonhole and multiscale uniformity arguments.
-/

/-- A dyadic level records a nonnegative exponent. -/
structure DyadicLevel where
  exponent : Nat
deriving DecidableEq

/-- Membership in the half-open natural-valued band `[2^k, 2^(k+1))`. -/
def inDyadicBand (level : DyadicLevel) (magnitude : Nat) : Prop :=
  2 ^ level.exponent ≤ magnitude ∧ magnitude < 2 ^ (level.exponent + 1)

/-- The public band predicate unfolds to its exact dyadic inequalities. -/
@[simp]
theorem inDyadicBand_iff (level : DyadicLevel) (magnitude : Nat) :
    inDyadicBand level magnitude ↔
      2 ^ level.exponent ≤ magnitude ∧
        magnitude < 2 ^ (level.exponent + 1) :=
  Iff.rfl

end Submission.Kakeya.Uniformity
