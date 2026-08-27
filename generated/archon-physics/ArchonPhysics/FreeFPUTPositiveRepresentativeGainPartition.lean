import ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
import ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

/-!
# Positive representative gain partition

The exact physical A1 formula already removes every canonical representative
with a nonpositive collision frequency by proving its Hamiltonian vertex is
zero.  This module partitions the remaining positive representatives into
the pairwise all-distinct sector and its genuine mode-degenerate complement.

Thus the complementary gain below contains repeated-mode geometry only; it
does not retain any already-vanishing zero-frequency term.
-/

namespace ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

noncomputable section

/-- Positive canonical representatives outside the pairwise all-distinct
sector. -/
def positiveNonAllDistinctQuadraticSwapRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveQuadraticSwapOrbitRepresentatives N m observed).filter
    fun q ↦ ¬ ObservedQuadraticAllDistinct observed q

/-- The all-distinct filter of the pre-existing positive representative
set, packaged so its classical decidability does not leak into theorem
signatures. -/
def positiveAllDistinctQuadraticSwapRepresentativesViaPositive
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveQuadraticSwapOrbitRepresentatives N m observed).filter
    fun q ↦ ObservedQuadraticAllDistinct observed q

/-- The all-distinct representative set used by the local closure is exactly
the all-distinct filter of the pre-existing positive representative set. -/
theorem positiveAllDistinctQuadraticSwapRepresentatives_eq_viaPositive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveAllDistinctQuadraticSwapRepresentatives m observed =
      positiveAllDistinctQuadraticSwapRepresentativesViaPositive
        N m observed := by
  classical
  ext q
  simp only [positiveAllDistinctQuadraticSwapRepresentatives,
    positiveAllDistinctQuadraticSwapRepresentativesViaPositive,
    positiveQuadraticSwapOrbitRepresentatives,
    Finset.mem_filter]
  tauto

@[simp] theorem mem_positiveNonAllDistinctQuadraticSwapRepresentatives_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    q ∈ positiveNonAllDistinctQuadraticSwapRepresentatives N m observed ↔
      q ∈ quadraticSwapOrbitRepresentatives N ∧
        PositiveModeTuple m (quadraticCollisionModes observed q) ∧
        ¬ ObservedQuadraticAllDistinct observed q := by
  classical
  simp only [positiveNonAllDistinctQuadraticSwapRepresentatives,
    positiveQuadraticSwapOrbitRepresentatives, Finset.mem_filter]
  tauto

/-- Exact positive A1 contribution carried by non-all-distinct canonical
representatives. -/
def positiveNonAllDistinctRepresentativeA1GainRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveNonAllDistinctQuadraticSwapRepresentatives N m observed,
    allDistinctLocalA1Gain m kappa time energy observed q

/-- The positive canonical A1 kernel sum is exactly the all-distinct gain
plus the mode-degenerate positive remainder. -/
theorem positiveRepresentativeA1GainSum_eq_allDistinct_add_nonAllDistinct
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed,
      ((quadraticSwapOrbit q).card : Real) ^ 2 *
        finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (q.1 r)) =
      allDistinctRepresentativeA1GainSum
          m kappa time energy observed +
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed := by
  classical
  unfold allDistinctRepresentativeA1GainSum allDistinctLocalA1Gain
    positiveNonAllDistinctRepresentativeA1GainRemainder
    positiveNonAllDistinctQuadraticSwapRepresentatives
  rw [positiveAllDistinctQuadraticSwapRepresentatives_eq_viaPositive]
  unfold positiveAllDistinctQuadraticSwapRepresentativesViaPositive
  exact (Finset.sum_filter_add_sum_filter_not
    (positiveQuadraticSwapOrbitRepresentatives N m observed)
    (fun q ↦ ObservedQuadraticAllDistinct observed q)
    (fun q ↦ ((quadraticSwapOrbit q).card : Real) ^ 2 *
      finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) *
      ∏ r : Fin 2,
        modeAction energy (modeFrequency m) (q.1 r))).symm

end

end ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
