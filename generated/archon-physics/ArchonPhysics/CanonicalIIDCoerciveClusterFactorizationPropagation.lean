import ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure

/-!
# Continuous canonical cluster-factorization propagation

This module turns the exact derivative of the canonical iid coercive
factorization defect into a finite-time norm estimate.  Initial
factorization and source smallness remain explicit hypotheses; no RPA or
recollision estimate is inserted here.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagation

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A uniform bound on the exact continuous-law source propagates an exact
zero initial factorization defect for any finite time. -/
theorem norm_canonicalCoerciveClusterFactorizationDefect_le_of_source
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I)
    (hzero : canonicalCoerciveClusterFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right 0 = 0)
    (time epsilon : Real)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right s‖ ≤ epsilon) :
    ‖canonicalCoerciveClusterFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right time‖ ≤
        epsilon * |time| := by
  apply norm_connectedCumulant_le_of_initial_eq_zero
  · exact hzero
  · intro s _hs
    exact hasDerivAt_canonicalCoerciveClusterFactorizationDefect
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right s
  · exact hsource

end

end ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagation
