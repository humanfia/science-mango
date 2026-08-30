import ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagation

/-!
# Continuous cluster propagation from a nonzero initial defect

For annealed random masses, two charge-balanced Haar blocks can retain a
mass covariance at time zero.  This module therefore records the exact
finite-time estimate with that initial defect retained instead of silently
setting it to zero.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagationWithInitial

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A uniform source bound controls growth from an arbitrary continuous-law
initial factorization defect. -/
theorem norm_canonicalCoerciveClusterFactorizationDefect_le_initial_add_source
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time epsilon : Real)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right s‖ ≤ epsilon) :
    ‖canonicalCoerciveClusterFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right time‖ ≤
        ‖canonicalCoerciveClusterFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right 0‖ +
          epsilon * |time| := by
  let defect := canonicalCoerciveClusterFactorizationDefect (N := N)
    kappa beta g hbeta a entry left right
  let source := canonicalCoerciveClusterFactorizationDefectSource (N := N)
    kappa beta g hbeta a entry left right
  have hchange : ‖defect time - defect 0‖ ≤ epsilon * |time| := by
    apply norm_connectedCumulant_sub_zero_le_of_source_bound
    · intro s _hs
      exact hasDerivAt_canonicalCoerciveClusterFactorizationDefect
        hN ha0 ha1 kappa beta g hbeta entry hpositive left right s
    · exact hsource
  calc
    ‖defect time‖ = ‖(defect time - defect 0) + defect 0‖ := by ring_nf
    _ ≤ ‖defect time - defect 0‖ + ‖defect 0‖ := norm_add_le _ _
    _ ≤ epsilon * |time| + ‖defect 0‖ :=
      add_le_add hchange le_rfl
    _ = ‖defect 0‖ + epsilon * |time| := by ring

end

end ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagationWithInitial
