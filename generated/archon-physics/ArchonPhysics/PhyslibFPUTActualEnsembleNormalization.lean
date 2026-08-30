import ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

/-!
# Normalization of the actual finite FPUT ensemble

The empty block observable is identically one in every sample.  Hence its
finite weighted expectation is exactly one as soon as the real weights sum
to one.  This removes the empty-moment premise from later propagation-of-
chaos statements; it is normalization, not a dynamical or RPA assumption.
-/

namespace ArchonPhysics.PhyslibFPUTActualEnsembleNormalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- The empty finite weighted block moment is the complexification of the
total real weight. -/
theorem finiteWeightedBlockMoment_empty
    (weight : Omega -> Real)
    (path : Omega -> I -> Real -> Complex)
    (time : Real) :
    finiteWeightedBlockMoment weight path ∅ time =
      ((∑ omega, weight omega : Real) : Complex) := by
  simp [finiteWeightedBlockMoment, signedBlockMonomial,
    Complex.ofReal_sum]

omit [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq Omega] in
/-- Probability normalization makes the actual empty FPUT block moment
exactly one, uniformly in the Hamiltonian trajectory and in time. -/
theorem actualFiniteCubicEnsembleBlockMoment_empty
    {N : Nat} [NeZero N]
    (weight : Omega -> Real)
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (hweight : ∑ omega, weight omega = 1)
    (time : Real) :
    actualFiniteCubicEnsembleBlockMoment
      weight mass entry p q ∅ time = 1 := by
  rw [actualFiniteCubicEnsembleBlockMoment,
    finiteWeightedBlockMoment_empty]
  simp [hweight]

end

end ArchonPhysics.PhyslibFPUTActualEnsembleNormalization
