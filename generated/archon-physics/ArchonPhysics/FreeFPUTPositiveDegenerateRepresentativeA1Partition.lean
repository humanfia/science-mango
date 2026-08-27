import ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
import ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
import ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection
import ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection

/-!
# Positive degenerate representative A1 partition

This module resolves the positive, non-all-distinct canonical A1 remainder
into its four mutually exclusive mode-equality strata.  The equal-children
stratum away from the observed mode is further split by equality or
inequality of the two binary phase signs.  Those two sub-strata are exactly
the hypotheses used by the existing same-sign and opposite-sign local
correction modules, and their A1 kernels agree definitionally with the
physical representative kernel.

Only the first-Picard A1 gain is partitioned here.  In particular, the
observed-child feedback, the all-equal first-match correction, cross-orbit
coherence, and any global kinetic or thermalization limit remain outside
the conclusions below.
-/

namespace ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
open ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection
open ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

noncomputable section

/-- Positive canonical representatives with equal children at a mode
different from the observed mode. -/
def positiveRepeatedChildrenAwayRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) :=
  repeatedChildrenAwayFromObservedTerms observed
    (positiveQuadraticSwapOrbitRepresentatives N m observed)

/-- Positive canonical representatives at which only child zero is the
observed mode. -/
def positiveObservedOnlyAtChildZeroRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) :=
  observedOnlyAtChildZeroTerms observed
    (positiveQuadraticSwapOrbitRepresentatives N m observed)

/-- Positive canonical representatives at which only child one is the
observed mode. -/
def positiveObservedOnlyAtChildOneRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) :=
  observedOnlyAtChildOneTerms observed
    (positiveQuadraticSwapOrbitRepresentatives N m observed)

/-- Positive canonical representatives for which all three collision modes
are equal. -/
def positiveObservedAtBothChildrenRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) :=
  observedAtBothChildrenTerms observed
    (positiveQuadraticSwapOrbitRepresentatives N m observed)

/-- A1 gain carried by equal children away from the observed mode. -/
def positiveRepeatedChildrenAwayRepresentativeA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveRepeatedChildrenAwayRepresentatives N m observed,
    allDistinctLocalA1Gain m kappa time energy observed q

/-- A1 gain carried by the observed-at-child-zero-only stratum. -/
def positiveObservedOnlyAtChildZeroRepresentativeA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveObservedOnlyAtChildZeroRepresentatives N m observed,
    allDistinctLocalA1Gain m kappa time energy observed q

/-- A1 gain carried by the observed-at-child-one-only stratum. -/
def positiveObservedOnlyAtChildOneRepresentativeA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveObservedOnlyAtChildOneRepresentatives N m observed,
    allDistinctLocalA1Gain m kappa time energy observed q

/-- A1 gain carried by the all-three-modes-equal stratum. -/
def positiveObservedAtBothChildrenRepresentativeA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveObservedAtBothChildrenRepresentatives N m observed,
    allDistinctLocalA1Gain m kappa time energy observed q

/-- Exact four-stratum decomposition of the physical positive degenerate
A1 remainder. -/
theorem positiveNonAllDistinctRepresentativeA1GainRemainder_eq_four_strata
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveNonAllDistinctRepresentativeA1GainRemainder
        m kappa time energy observed =
      positiveRepeatedChildrenAwayRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedAtBothChildrenRepresentativeA1Gain
          m kappa time energy observed := by
  classical
  simpa only [positiveNonAllDistinctRepresentativeA1GainRemainder,
    positiveNonAllDistinctQuadraticSwapRepresentatives,
    nonAllDistinctQuadraticTerms,
    positiveRepeatedChildrenAwayRepresentativeA1Gain,
    positiveObservedOnlyAtChildZeroRepresentativeA1Gain,
    positiveObservedOnlyAtChildOneRepresentativeA1Gain,
    positiveObservedAtBothChildrenRepresentativeA1Gain,
    positiveRepeatedChildrenAwayRepresentatives,
    positiveObservedOnlyAtChildZeroRepresentatives,
    positiveObservedOnlyAtChildOneRepresentatives,
    positiveObservedAtBothChildrenRepresentatives] using
    (sum_filter_not_allDistinct_eq_four_strata observed
      (positiveQuadraticSwapOrbitRepresentatives N m observed)
      (allDistinctLocalA1Gain m kappa time energy observed))

/-- Same-sign portion of the equal-children-away representative stratum. -/
def positiveRepeatedChildSameSignRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveRepeatedChildrenAwayRepresentatives N m observed).filter
    fun q ↦ q.2.1 = q.2.2

/-- Opposite-sign portion of the equal-children-away representative
stratum. -/
def positiveRepeatedChildOppositeSignRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveRepeatedChildrenAwayRepresentatives N m observed).filter
    fun q ↦ q.2.1 ≠ q.2.2

/-- Membership in the same-sign filter is exactly the separated local
hypothesis of `FreeFPUTRepeatedChildSameSignCorrection`, together with
membership in the positive canonical base. -/
@[simp] theorem mem_positiveRepeatedChildSameSignRepresentatives_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    q ∈ positiveRepeatedChildSameSignRepresentatives N m observed ↔
      q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed ∧
        ObservedSeparatedRepeatedChildSameSign observed q := by
  classical
  simp only [positiveRepeatedChildSameSignRepresentatives,
    positiveRepeatedChildrenAwayRepresentatives,
    repeatedChildrenAwayFromObservedTerms, Finset.mem_filter]
  unfold RepeatedChildrenAwayFromObserved
    ObservedSeparatedRepeatedChildSameSign RepeatedChildSameSign
  tauto

/-- Membership in the opposite-sign filter is exactly the separated local
hypothesis of `FreeFPUTRepeatedChildOppositeSignCorrection`, together with
membership in the positive canonical base. -/
@[simp] theorem mem_positiveRepeatedChildOppositeSignRepresentatives_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    q ∈ positiveRepeatedChildOppositeSignRepresentatives N m observed ↔
      q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed ∧
        ObservedSeparatedRepeatedChildOppositeSign observed q := by
  classical
  simp only [positiveRepeatedChildOppositeSignRepresentatives,
    positiveRepeatedChildrenAwayRepresentatives,
    repeatedChildrenAwayFromObservedTerms, Finset.mem_filter]
  unfold RepeatedChildrenAwayFromObserved
    ObservedSeparatedRepeatedChildOppositeSign RepeatedChildOppositeSign
  tauto

/-- The physical representative A1 kernel is literally the A1 kernel named
in the same-sign local correction module. -/
theorem allDistinctLocalA1Gain_eq_repeatedChildLocalA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    allDistinctLocalA1Gain m kappa time energy observed q =
      repeatedChildLocalA1Gain m kappa time energy observed q := rfl

/-- The physical representative A1 kernel is likewise the A1 kernel named
in the opposite-sign local correction module. -/
theorem allDistinctLocalA1Gain_eq_repeatedChildOppositeSignLocalA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    allDistinctLocalA1Gain m kappa time energy observed q =
      repeatedChildOppositeSignLocalA1Gain
        m kappa time energy observed q := rfl

/-- Same-sign part of the physical repeated-child-away A1 gain, expressed
with the kernel from its local correction module. -/
def positiveRepeatedChildSameSignRepresentativeA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
    repeatedChildLocalA1Gain m kappa time energy observed q

/-- Opposite-sign part of the physical repeated-child-away A1 gain,
expressed with the kernel from its local correction module. -/
def positiveRepeatedChildOppositeSignRepresentativeA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives N m observed,
    repeatedChildOppositeSignLocalA1Gain m kappa time energy observed q

/-- Exact mutually exclusive same-sign/opposite-sign split of the
equal-children-away A1 layer. -/
theorem positiveRepeatedChildrenAwayRepresentativeA1Gain_eq_sign_partition
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveRepeatedChildrenAwayRepresentativeA1Gain
        m kappa time energy observed =
      positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed := by
  classical
  unfold positiveRepeatedChildrenAwayRepresentativeA1Gain
    positiveRepeatedChildSameSignRepresentativeA1Gain
    positiveRepeatedChildOppositeSignRepresentativeA1Gain
    positiveRepeatedChildSameSignRepresentatives
    positiveRepeatedChildOppositeSignRepresentatives
  simpa only [allDistinctLocalA1Gain,
    repeatedChildLocalA1Gain,
    repeatedChildOppositeSignLocalA1Gain] using
    (Finset.sum_filter_add_sum_filter_not
      (positiveRepeatedChildrenAwayRepresentatives N m observed)
      (fun q : QuadraticPhaseTerm N ↦ q.2.1 = q.2.2)
      (allDistinctLocalA1Gain m kappa time energy observed)).symm

/-- Five-term refinement of the four-stratum formula, obtained by resolving
the repeated-children-away layer into the two local correction regimes. -/
theorem positiveNonAllDistinctRepresentativeA1GainRemainder_eq_five_strata
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveNonAllDistinctRepresentativeA1GainRemainder
        m kappa time energy observed =
      positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedAtBothChildrenRepresentativeA1Gain
          m kappa time energy observed := by
  rw [positiveNonAllDistinctRepresentativeA1GainRemainder_eq_four_strata,
    positiveRepeatedChildrenAwayRepresentativeA1Gain_eq_sign_partition]

end

end ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
