import ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
import ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagation

/-!
# Continuous canonical binary kinetic-time criterion

For one fixed pair of disjoint finite ordered blocks, the exact canonical iid
alpha--beta source carries the physical powers `kappa * g` and `beta * g^2`.
Uniform bounds on the corresponding unit source-slot norm sums therefore
give the finite-time estimate

`‖defect(t)‖ ≤ (|kappa*g| * Q + |beta*g^2| * C) * |t|`.

The final theorem records the resulting kinetic-time squeeze.  The decay of
the unit channel budgets and the zero initial defect remain explicit; no
garden, RPA, or recollision estimate is assumed implicitly.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveBinaryHigherOrderKineticCriterion

open Filter Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveClusterFactorizationPropagation
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Continuous-law binary factorization estimate with the quadratic and
quartic coupling powers exposed explicitly. -/
theorem norm_canonicalCoerciveClusterFactorizationDefect_le_binary_channels
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hzero : canonicalCoerciveClusterFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right 0 = 0)
    (time quadraticBudget quarticBudget : Real)
    (hquadratic : ∀ s ∈ Set.uIcc 0 time,
      canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right s ≤ quadraticBudget)
    (hquartic : ∀ s ∈ Set.uIcc 0 time,
      canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right s ≤ quarticBudget) :
    ‖canonicalCoerciveClusterFactorizationDefect (N := N)
      kappa beta g hbeta a entry left right time‖ ≤
        (|kappa * g| * quadraticBudget +
          |beta * g ^ 2| * quarticBudget) * |time| := by
  apply norm_canonicalCoerciveClusterFactorizationDefect_le_of_source
    hN ha0 ha1 kappa beta g hbeta entry hpositive
      left right hzero time
      (|kappa * g| * quadraticBudget +
        |beta * g ^ 2| * quarticBudget)
  intro s hs
  apply
    (norm_canonicalCoerciveClusterFactorizationDefectSource_le_coupling_unitSlotNormSums
      hN ha0 ha1 kappa beta g hbeta entry hpositive hindex s).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hquadratic s hs) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (hquartic s hs) (abs_nonneg _))

/-- If the explicit coupling-weighted channel budget vanishes after
multiplication by the kinetic observation time, then the actual continuous
canonical binary factorization defect vanishes there as well. -/
theorem norm_canonicalCoerciveClusterFactorizationDefect_tendsto_zero_at_kineticTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta tau : Real)
    (g : Nat → Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hzero : ∀ system,
      canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry left right 0 = 0)
    (quadraticBudget quarticBudget : Nat → Real)
    (hquadratic : ∀ system, ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta (g system) hbeta a entry left right s ≤
          quadraticBudget system)
    (hquartic : ∀ system, ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta (g system) hbeta a entry left right s ≤
          quarticBudget system)
    (hchannel : Tendsto (fun system =>
      (|kappa * g system| * quadraticBudget system +
        |beta * (g system) ^ 2| * quarticBudget system) *
          |tau / (g system) ^ 2|) atTop (nhds 0)) :
    Tendsto (fun system =>
      ‖canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry left right
          (tau / (g system) ^ 2)‖) atTop (nhds 0) := by
  apply squeeze_zero
  · intro system
    exact norm_nonneg _
  · intro system
    exact norm_canonicalCoerciveClusterFactorizationDefect_le_binary_channels
      hN ha0 ha1 kappa beta (g system) hbeta entry hpositive hindex
        (hzero system) (tau / (g system) ^ 2)
        (quadraticBudget system) (quarticBudget system)
        (hquadratic system) (hquartic system)
  · exact hchannel

end

end ArchonPhysics.CanonicalIIDCoerciveBinaryHigherOrderKineticCriterion
