import Mathlib
import ArchonPhysics
import Physlib.CondensedMatter.LatticeModels.Basic

/-!
# Finite periodic lattice

A finite one-dimensional periodic lattice, retaining the position, momentum,
site-mass, and forward-difference data needed by the later thermalization
models.  This file deliberately contains no thermalization or localization
claim.
-/

namespace ArchonPhysics.Generated.FinitePeriodic

noncomputable section

/-- The sites of a periodic lattice with `N` sites. -/
abbrev Site (N : ℕ) := ZMod N

/-- A real-valued field on the sites of a finite periodic lattice. -/
abbrev Field (N : ℕ) := Site N → ℝ

/-- A finite periodic lattice with real positions, momenta, and positive site masses. -/
structure Lattice (N : ℕ) where
  positive_size : 0 < N
  position : Field N
  momentum : Field N
  mass : Field N
  mass_pos : ∀ i, 0 < mass i

/-- The forward difference `D q i = q (i + 1) - q i` on the periodic lattice. -/
def forwardDifference {N : ℕ} (q : Field N) (i : Site N) : ℝ :=
  q (i + 1) - q i

/-- The sum of the forward differences of a field around the periodic lattice. -/
def totalForwardDifference {N : ℕ} [NeZero N] (q : Field N) : ℝ :=
  ∑ i : Site N, forwardDifference q i

/-- The kinetic quadratic form of momenta with positive site masses. -/
def kineticQuadraticForm {N : ℕ} [NeZero N] (mass momentum : Field N) : ℝ :=
  ∑ i : Site N, momentum i ^ 2 / (2 * mass i)

/-- The basic finite-dimensional identity supplied by the periodic lattice model. -/
theorem finite_periodic_physics_formalization_target
    {N : ℕ} [NeZero N] (L : Lattice N) :
    (∀ i, 0 < L.mass i) ∧
      totalForwardDifference L.position = 0 := by
  constructor
  · exact L.mass_pos
  · unfold totalForwardDifference forwardDifference
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (by
      simpa using (Equiv.sum_comp (Equiv.addRight (1 : Site N)) L.position))

end

end ArchonPhysics.Generated.FinitePeriodic
