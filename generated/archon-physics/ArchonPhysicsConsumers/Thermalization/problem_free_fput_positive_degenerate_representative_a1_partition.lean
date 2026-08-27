import ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition

/-!
# Consumer: positive degenerate representative A1 partition

This gate exposes the exact A1-gain decomposition of the positive
non-all-distinct canonical remainder.  It deliberately makes no assertion
that the corresponding observed-child or all-equal feedback has been
globally closed.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
open ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection
open ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

noncomputable section

/-- The physical positive non-all-distinct A1 remainder is exactly the sum
of its four mutually exclusive mode-equality strata. -/
theorem problem_positiveNonAllDistinctA1Gain_eq_four_strata
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
          m kappa time energy observed :=
  positiveNonAllDistinctRepresentativeA1GainRemainder_eq_four_strata
    m kappa time energy observed

/-- The equal-children-away term itself is exactly the disjoint same-sign
and opposite-sign sum, using the A1 kernels from the two existing local
correction modules. -/
theorem problem_positiveRepeatedChildrenAwayA1Gain_eq_sign_partition
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveRepeatedChildrenAwayRepresentativeA1Gain
        m kappa time energy observed =
      positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed :=
  positiveRepeatedChildrenAwayRepresentativeA1Gain_eq_sign_partition
    m kappa time energy observed

/-- The two refined filters are precisely the domains of the existing
same-sign and opposite-sign local correction theorems. -/
theorem problem_positiveRepeatedChild_sign_strata_are_local_domains
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    (q ∈ positiveRepeatedChildSameSignRepresentatives N m observed ↔
        q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed ∧
          ObservedSeparatedRepeatedChildSameSign observed q) ∧
      (q ∈ positiveRepeatedChildOppositeSignRepresentatives N m observed ↔
        q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed ∧
          ObservedSeparatedRepeatedChildOppositeSign observed q) :=
  ⟨mem_positiveRepeatedChildSameSignRepresentatives_iff m observed q,
    mem_positiveRepeatedChildOppositeSignRepresentatives_iff m observed q⟩

/-- Fully refined A1-only formula.  The final three terms still require
their own feedback analysis before any degenerate gain--loss closure can be
claimed. -/
theorem problem_positiveNonAllDistinctA1Gain_eq_five_strata
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
          m kappa time energy observed :=
  positiveNonAllDistinctRepresentativeA1GainRemainder_eq_five_strata
    m kappa time energy observed

#print axioms problem_positiveNonAllDistinctA1Gain_eq_four_strata
#print axioms problem_positiveRepeatedChildrenAwayA1Gain_eq_sign_partition
#print axioms problem_positiveRepeatedChild_sign_strata_are_local_domains
#print axioms problem_positiveNonAllDistinctA1Gain_eq_five_strata

end

end ArchonPhysicsConsumers.Thermalization
