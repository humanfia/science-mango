import ArchonPhysics.FiniteOscillatoryResonanceSplit

/-!
# Consumer: finite oscillatory resonance split

This consumer specializes the finite resonance interfaces to three modes.  It
checks the exact sector split, the secular exact-resonance term, and the
time-independent `O(|g|)` estimate for the nonresonant sector.  The finite
inverse-mismatch sum remains explicit.
-/

namespace ArchonPhysicsConsumers.Thermalization.FiniteOscillatoryResonanceSplit

open scoped BigOperators
open ArchonPhysics.FiniteOscillatoryResonanceSplit

noncomputable section

/-- A three-mode oscillatory sum splits exactly into its resonant and
nonresonant sectors. -/
theorem problem_threeMode_exact_resonance_split
    (coefficient : Fin 3 → Complex) (mismatch : Fin 3 → Real)
    (time : Real) :
    oscillatorySum Finset.univ coefficient mismatch time =
      resonantOscillatorySum Finset.univ coefficient mismatch time +
        nonresonantOscillatorySum Finset.univ coefficient mismatch time := by
  exact oscillatorySum_eq_resonant_add_nonresonant
    Finset.univ coefficient mismatch time

/-- On the same three-mode system, every exact resonance retains precisely
its secular elapsed-time factor. -/
theorem problem_threeMode_resonant_secular_term
    (coefficient : Fin 3 → Complex) (mismatch : Fin 3 → Real)
    (time : Real) :
    resonantOscillatorySum Finset.univ coefficient mismatch time =
      (∑ α ∈ resonantIndices Finset.univ mismatch, coefficient α) * time := by
  exact resonantOscillatorySum_eq_time_sum
    Finset.univ coefficient mismatch time

/-- The coupled three-mode nonresonant sector is bounded linearly in `|g|`,
with a constant independent of the elapsed time. -/
theorem problem_threeMode_nonresonant_O_abs_coupling
    (coupling : Real) (coefficient : Fin 3 → Complex)
    (mismatch : Fin 3 → Real) (time : Real) :
    ‖coupledNonresonantOscillatorySum coupling Finset.univ
        coefficient mismatch time‖ ≤
      2 * |coupling| * ∑ α ∈ nonresonantIndices Finset.univ mismatch,
        ‖coefficient α‖ / |mismatch α| := by
  exact norm_coupledNonresonantOscillatorySum_le
    coupling Finset.univ coefficient mismatch time

#print axioms problem_threeMode_exact_resonance_split
#print axioms problem_threeMode_resonant_secular_term
#print axioms problem_threeMode_nonresonant_O_abs_coupling

end


end ArchonPhysicsConsumers.Thermalization.FiniteOscillatoryResonanceSplit
