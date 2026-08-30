import ArchonPhysics.CanonicalIIDCoerciveBinarySubkineticCriterion
import ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyUnitSlotCost
import ArchonPhysics.CanonicalIIDCoerciveInitialHaarFactorizationDefect

/-!
# Unconditional unbalanced-sector subkinetic RPA

This module closes a genuine positive-time sector of the canonical iid
Hamiltonian problem.  Haar selection makes the initial binary defect exactly
zero whenever one phase-separated block has nonzero total charge.  Conserved
energy supplies coupling- and time-uniform normalized source-slot bounds.
Consequently the actual annealed defect tends to zero on every time sequence
with `|g| |t| -> 0`.

No cutoff-radius bound, RPA renewal, Markov approximation, small-denominator
estimate, or recollision hypothesis occurs.  The conclusion is subkinetic;
it does not claim the target `t ~ g^-2` scale.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveUnbalancedSubkineticRPA

open Filter Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveBinarySubkineticCriterion
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyUnitSlotCost
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarFactorizationDefect
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.UniformMassGaugeCoercivity

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual annealed binary factorization defect vanishes throughout the
charge-unbalanced sector on every subkinetic time sequence.  The constant `G`
is only a uniform bound on the weak-coupling sequence and enters the explicit
conserved-energy envelope. -/
theorem canonicalAnnealedUnbalancedBinaryRPA_tendsto_zero_at_subkineticTime
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
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right)))
    (hleft : canonicalOrderedSignedBlockCharge (N := N) entry left ≠ 0) :
    Tendsto (fun system =>
      ‖canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry left right (time system)‖)
      atTop (nhds 0) := by
  obtain ⟨C, hC, hPoincare⟩ :=
    exists_uniform_massWeighted_poincareConstant (N := N)
  let quadraticBudget : Real :=
    canonicalExplicitClusterUnitQuadraticSourceSlotCost
      N C kappa beta G left right
  let quarticBudget : Real :=
    canonicalExplicitClusterUnitQuarticSourceSlotCost
      N C kappa beta G left right
  have hquarticTime : Tendsto
      (fun system => |g system| ^ 2 * |time system|)
      atTop (nhds 0) := by
    have habs : Tendsto (fun system => |g system|) atTop (nhds 0) := by
      simpa using hg.abs
    have hproduct := habs.mul hsubkinetic
    convert hproduct using 1
    funext system
    ring
    norm_num
  apply canonicalBinaryDefect_tendsto_zero_at_subkineticTime
    hN ha0 ha1 kappa beta g time hbeta entry hpositive hindex
      (quadraticBudget := quadraticBudget)
      (quarticBudget := quarticBudget)
  · intro system
    exact
      canonicalCoerciveClusterFactorizationDefect_zero_eq_zero_of_leftCharge
        hN ha0 ha1 kappa beta (g system) hbeta entry hpositive
          hindex hcharge hleft
  · intro system s _hs
    exact
      canonicalClusterUnitQuadraticSourceSlotNormSum_le_explicitEnergyCost
        hN ha0 ha1 C hC.le hPoincare kappa beta (g system) G
          hbeta hG (hgG system) entry hpositive left right s
  · intro system s _hs
    exact
      canonicalClusterUnitQuarticSourceSlotNormSum_le_explicitEnergyCost
        hN ha0 ha1 C hC.le hPoincare kappa beta (g system) G
          hbeta hG (hgG system) entry hpositive left right s
  · exact hsubkinetic
  · exact hquarticTime

end

end ArchonPhysics.CanonicalIIDCoerciveUnbalancedSubkineticRPA
