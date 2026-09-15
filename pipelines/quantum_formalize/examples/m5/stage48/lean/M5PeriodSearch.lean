import M5Accepted
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

namespace M5.PeriodSearch

noncomputable def candidates (F : M5.BinaryPolynomial) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (2 ^ F.natDegree)).filter (fun N => F ∣ M5.cyclicModulus N)

noncomputable def finiteSearch (F : M5.BinaryPolynomial) : ℕ := by
  classical
  exact if h : (candidates F).Nonempty then (candidates F).min' h else 0

end M5.PeriodSearch
