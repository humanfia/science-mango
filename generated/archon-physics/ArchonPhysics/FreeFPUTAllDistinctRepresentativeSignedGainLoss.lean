import ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
import ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex

/-!
# Representative-level all-distinct signed gain--loss sum

This module sums the local all-distinct gain--loss identity over one canonical
representative of every quadratic input-swap orbit.  The finite index set also
retains only collision triples with positive mode frequencies, exactly the
hypothesis required by the collision-kernel bridge.

The result is an exact representative-indexed signed-flux formula.  It is
deliberately a nested sum of the already proved local images: no assertion is
made here that their union is the complete connected-return fiber.  That
surjectivity statement is a separate theorem.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

/-- Canonical swap-orbit representatives whose observed/input modes are
pairwise distinct and whose three collision frequencies are positive. -/
def positiveAllDistinctQuadraticSwapRepresentatives
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (quadraticSwapOrbitRepresentatives N).filter fun q ↦
    ObservedQuadraticAllDistinct observed q ∧
      PositiveModeTuple m (quadraticCollisionModes observed q)

@[simp] theorem mem_positiveAllDistinctQuadraticSwapRepresentatives_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    q ∈ positiveAllDistinctQuadraticSwapRepresentatives m observed ↔
      q ∈ quadraticSwapOrbitRepresentatives N ∧
        ObservedQuadraticAllDistinct observed q ∧
        PositiveModeTuple m (quadraticCollisionModes observed q) := by
  classical
  simp [positiveAllDistinctQuadraticSwapRepresentatives]

/-- Sum of the coherent A1 orbit gains over the admissible canonical
representatives. -/
def allDistinctRepresentativeA1GainSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveAllDistinctQuadraticSwapRepresentatives m observed,
    allDistinctLocalA1Gain m kappa time energy observed q

/-- Nested sum of the literal eight-tree feedback images.  Keeping the sum
nested avoids assuming disjointness or global coverage before those facts are
proved. -/
def allDistinctRepresentativeConnectedFeedbackSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveAllDistinctQuadraticSwapRepresentatives m observed,
    allDistinctConnectedReturnTreeFeedbackSum
      m kappa time energy observed q

/-- Representative-indexed sum of the local gain and feedback packages. -/
def allDistinctRepresentativeSignedGainLossSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveAllDistinctQuadraticSwapRepresentatives m observed,
    allDistinctLocalSignedGainLoss m kappa time energy observed q

/-- The signed three-wave collision sum over the same admissible canonical
representatives. -/
def allDistinctRepresentativeSignedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveAllDistinctQuadraticSwapRepresentatives m observed,
    4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
      quadraticSignedCollisionFlux q
        (modeAction energy (modeFrequency m)) observed

/-- The representative sum separates exactly into its A1 and connected-tree
parts; this is only distributivity of the finite sum and introduces no fiber
coverage assumption. -/
theorem allDistinctRepresentativeSignedGainLossSum_eq_gain_add_feedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    allDistinctRepresentativeSignedGainLossSum
        m kappa time energy observed =
      allDistinctRepresentativeA1GainSum
          m kappa time energy observed +
        allDistinctRepresentativeConnectedFeedbackSum
          m kappa time energy observed := by
  classical
  unfold allDistinctRepresentativeSignedGainLossSum
    allDistinctRepresentativeA1GainSum
    allDistinctRepresentativeConnectedFeedbackSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rfl

/-- Exact finite-volume signed gain--loss formula over all admissible
canonical swap-orbit representatives. -/
theorem allDistinctRepresentativeSignedGainLossSum_eq_signedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    allDistinctRepresentativeSignedGainLossSum
        m kappa time energy observed =
      allDistinctRepresentativeSignedFluxSum
        m kappa time energy observed := by
  classical
  unfold allDistinctRepresentativeSignedGainLossSum
    allDistinctRepresentativeSignedFluxSum
  apply Finset.sum_congr rfl
  intro q hq
  have hmem :=
    (mem_positiveAllDistinctQuadraticSwapRepresentatives_iff
      m observed q).mp hq
  exact allDistinctLocalSignedGainLoss_eq_signedCollisionFlux
    m kappa time energy observed q hmem.2.1 hEnergy hmem.2.2

/-- The representative A1 gain plus the nested connected-tree feedback is
exactly the representative signed-flux sum. -/
theorem allDistinctRepresentativeGain_add_feedback_eq_signedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    allDistinctRepresentativeA1GainSum
        m kappa time energy observed +
      allDistinctRepresentativeConnectedFeedbackSum
        m kappa time energy observed =
      allDistinctRepresentativeSignedFluxSum
        m kappa time energy observed := by
  rw [← allDistinctRepresentativeSignedGainLossSum_eq_gain_add_feedback,
    allDistinctRepresentativeSignedGainLossSum_eq_signedFluxSum
      m kappa time energy observed hEnergy]

end

end ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
