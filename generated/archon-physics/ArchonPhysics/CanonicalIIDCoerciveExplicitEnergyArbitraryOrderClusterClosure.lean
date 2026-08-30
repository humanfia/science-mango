import ArchonPhysics.CanonicalIIDCoerciveBinaryKineticCriterionWithInitial
import ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound

/-!
# Explicit-energy closure of canonical ordered cluster factorization

For a coupling sequence tending to zero, the explicit conserved-energy
estimate supplies uniform bounds for every fixed canonical block moment.
Together with the exact empty-block normalization and convergence of every
prefix binary factorization defect, the ordered-cluster telescope therefore
closes at every fixed finite order.

The first theorem keeps prefix binary convergence as an explicit premise.
The kinetic-time specialization obtains that premise from the existing
binary theorem while retaining, separately at every prefix, the exact
initial annealed covariance decay and the coupling-weighted quadratic and
quartic channel decay.  None of those scientific inputs is inferred here.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyArbitraryOrderClusterClosure

open scoped BigOperators Topology

open Filter
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveBinaryKineticCriterionWithInitial
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound
open ArchonPhysics.CanonicalIIDCoerciveUniformBlockMomentBound
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTUniformMomentDecoherencePropagation
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- At every fixed finite order, coupling convergence supplies the uniform
moment premise automatically.  Prefix binary factorization convergence is
kept as the sole asymptotic input to the ordered telescope. -/
theorem tendsto_orderedCanonicalSignedClusterFactorizationDefect_zero_of_tendsto_coupling_zero
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta : Real) (g : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (cluster : Nat → Finset I) (time : Nat → Real)
    (hbinary : ∀ level, Tendsto
      (fun scale => canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g scale) hbeta a entry
        (orderedClusterUnion cluster level) (cluster level) (time scale))
      atTop (nhds 0))
    (count : Nat) :
    Tendsto
      (fun scale => orderedClusterFactorizationDefect
        (canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g scale) hbeta a entry)
        cluster count (time scale))
      atTop (nhds 0) := by
  apply tendsto_orderedClusterFactorizationDefect_zero_of_uniformMomentBound
    (fun scale => canonicalSignedBlockBochnerIntegral (N := N)
      kappa beta (g scale) hbeta a entry)
    cluster time
    (fun scale => canonicalSignedBlockBochnerIntegral_empty
      kappa beta (g scale) hbeta a entry (time scale))
    ?_
    (canonicalSignedBlockBochnerIntegral_hmoment_of_tendsto_coupling_zero
      hN ha0 ha1 kappa beta g hg hbeta entry hpositive cluster time)
    count
  intro level
  simpa only [canonicalCoerciveClusterFactorizationDefect] using
    hbinary level

/-- Kinetic-time arbitrary-order endpoint with every nonautomatic input
visible.  For each prefix, disjointness permits the binary channel estimate;
`hinitial` is the surviving annealed random-mass covariance decay, while
`hchannel` is the full coupling-weighted quadratic/quartic source decay.
The theorem does not prove either input. -/
theorem canonicalHigherOrderRPA_tendsto_zero_at_kineticTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta tau : Real) (g : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (cluster : Nat → Finset I)
    (hindex : ∀ level,
      Disjoint (orderedClusterUnion cluster level) (cluster level))
    (quadraticBudget quarticBudget : Nat → Nat → Real)
    (hquadratic : ∀ level system, ∀ s ∈
      Set.uIcc 0 (tau / (g system) ^ 2),
      canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta (g system) hbeta a entry
        (orderedClusterUnion cluster level) (cluster level) s ≤
          quadraticBudget level system)
    (hquartic : ∀ level system, ∀ s ∈
      Set.uIcc 0 (tau / (g system) ^ 2),
      canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta (g system) hbeta a entry
        (orderedClusterUnion cluster level) (cluster level) s ≤
          quarticBudget level system)
    (hinitial : ∀ level, Tendsto (fun system =>
      ‖canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta (g system) hbeta a entry
        (orderedClusterUnion cluster level) (cluster level) 0‖)
      atTop (nhds 0))
    (hchannel : ∀ level, Tendsto (fun system =>
      (|kappa * g system| * quadraticBudget level system +
        |beta * (g system) ^ 2| * quarticBudget level system) *
          |tau / (g system) ^ 2|)
      atTop (nhds 0))
    (count : Nat) :
    Tendsto
      (fun system => orderedClusterFactorizationDefect
        (canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g system) hbeta a entry)
        cluster count (tau / (g system) ^ 2))
      atTop (nhds 0) := by
  apply
    tendsto_orderedCanonicalSignedClusterFactorizationDefect_zero_of_tendsto_coupling_zero
      hN ha0 ha1 kappa beta g hg hbeta entry hpositive cluster
        (fun system => tau / (g system) ^ 2) ?_ count
  intro level
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact
    canonicalBinaryDefect_tendsto_zero_at_kineticTime_of_initial_and_channels
      hN ha0 ha1 kappa beta tau g hbeta entry hpositive (hindex level)
      (quadraticBudget level) (quarticBudget level)
      (hquadratic level) (hquartic level) (hinitial level) (hchannel level)

end

end ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyArbitraryOrderClusterClosure
