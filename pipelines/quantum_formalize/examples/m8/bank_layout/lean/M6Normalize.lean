import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
open scoped BigOperators
namespace M6.Normalize
/-- Actual integer coefficient division; exactness is proved separately. -/
noncomputable def divide (k : ℤ) (p : Polynomial ℤ) : Polynomial ℤ :=
  ∑ d ∈ p.support, Polynomial.C (p.coeff d / k) * Polynomial.X^d
end M6.Normalize
