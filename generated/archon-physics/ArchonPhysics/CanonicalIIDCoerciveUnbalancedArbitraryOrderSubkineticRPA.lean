import ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyArbitraryOrderClusterClosure
import ArchonPhysics.CanonicalIIDCoerciveUnbalancedSubkineticRPA

/-!
# Unconditional arbitrary-order unbalanced-sector subkinetic RPA

The exact initial Haar selector and conserved-energy source-slot estimates
already give binary factorization throughout every charge-unbalanced sector
on time sequences satisfying `|g| |t| -> 0`.  This module feeds that result
into the ordered-cluster telescope.  Thus every fixed finite cluster order
factorizes whenever each telescope prefix remains charge-unbalanced and its
two charge supports are disjoint.

No RPA renewal, Markov approximation, cutoff-radius hypothesis,
small-denominator estimate, or recollision estimate is assumed.  The result
is deliberately subkinetic and does not claim the target `t ~ g^-2` scale.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveUnbalancedArbitraryOrderSubkineticRPA

open Filter Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyArbitraryOrderClusterClosure
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveUniformBlockMomentBound
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
open ArchonPhysics.CanonicalIIDCoerciveUnbalancedSubkineticRPA
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every fixed ordered cluster factorizes on a subkinetic time sequence if
each prefix-versus-next-block split lies in the exact Haar-unbalanced sector.
The conclusion concerns the actual canonical iid mass-phase ensemble. -/
theorem canonicalAnnealedUnbalancedHigherOrderRPA_tendsto_zero_at_subkineticTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta G : Real) (hG : 0 <= G)
    (g time : Nat -> Real) (hgG : forall system, |g system| <= G)
    (hg : Tendsto g atTop (nhds 0))
    (hsubkinetic : Tendsto
      (fun system => |g system| * |time system|) atTop (nhds 0))
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (cluster : Nat -> Finset I)
    (hindex : forall level,
      Disjoint (orderedClusterUnion cluster (level + 1))
        (cluster (level + 1)))
    (hcharge : forall level, Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry
          (orderedClusterUnion cluster (level + 1))))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry
          (cluster (level + 1)))))
    (hleft : forall level,
      canonicalOrderedSignedBlockCharge (N := N) entry
        (orderedClusterUnion cluster (level + 1)) ≠ 0)
    (count : Nat) :
    Tendsto
      (fun system => orderedClusterFactorizationDefect
        (canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g system) hbeta a entry)
        cluster count (time system))
      atTop (nhds 0) := by
  apply
    tendsto_orderedCanonicalSignedClusterFactorizationDefect_zero_of_tendsto_coupling_zero
      hN ha0 ha1 kappa beta g hg hbeta entry hpositive cluster time
  · intro level
    cases level with
    | zero =>
        simpa [orderedClusterUnion,
          canonicalCoerciveClusterFactorizationDefect,
          blockFactorizationDefect,
          canonicalSignedBlockBochnerIntegral_empty] using
            (tendsto_const_nhds : Tendsto
              (fun _ : Nat => (0 : Complex)) atTop (nhds 0))
    | succ level =>
        apply tendsto_zero_iff_norm_tendsto_zero.mpr
        exact
          canonicalAnnealedUnbalancedBinaryRPA_tendsto_zero_at_subkineticTime
            hN ha0 ha1 kappa beta G hG g time hgG hg hsubkinetic hbeta
              entry hpositive (hindex level) (hcharge level) (hleft level)

end

end ArchonPhysics.CanonicalIIDCoerciveUnbalancedArbitraryOrderSubkineticRPA
