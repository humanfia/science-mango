import ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
import ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
import ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget

/-!
# Actual two-mass resampling bridge for the annealed child sector

This file connects the child-repeated mode-pair parametrization used by the
actual two-mass spectral charts to the predicate-restricted ordered-triple
measure used by the canonical random lattice.  The resulting identities are
finite-volume equalities, before any estimate or limiting argument.
-/

open scoped ENNReal

namespace ArchonPhysics.ActualTwoMassChildRepeatedAnnealedBridge

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

/-- A child-repeated ordered triple contains exactly the parent label and the
common child label. -/
def childRepeatedModePairEquiv {N : Nat} [NeZero N] :
    ChildRepeatedModePair N ≃
      {modes : OrderedModeTriple N // ChildRepeated modes} where
  toFun modes := ⟨childRepeatedModeTriple modes, by
    simp [ChildRepeated, childRepeatedModeTriple]⟩
  invFun modes := (modes.1 0, modes.1 1)
  left_inv modes := by
    ext <;> rfl
  right_inv modes := by
    apply Subtype.ext
    funext r
    fin_cases r
    · rfl
    · rfl
    · exact modes.2

local instance childRepeated_decidablePred {N : Nat} [NeZero N] :
    DecidablePred (ChildRepeated : OrderedModeTriple N → Prop) :=
  Classical.decPred _

/-- Reindex a sum over all child-repeated triples by their two independent
mode labels. -/
theorem sum_if_childRepeated_eq_sum_subtype
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (F : OrderedModeTriple N → M) :
    (∑ modes : OrderedModeTriple N,
        if ChildRepeated modes then F modes else 0) =
      ∑ modes : {modes : OrderedModeTriple N // ChildRepeated modes},
        F modes.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) F

/-- The equivalent pair-labelled form of the same subtype sum. -/
theorem sum_childRepeatedModePair_eq_sum_subtype
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (F : OrderedModeTriple N → M) :
    (∑ modes : ChildRepeatedModePair N,
        F (childRepeatedModeTriple modes)) =
      ∑ modes : {modes : OrderedModeTriple N // ChildRepeated modes},
        F modes.1 := by
  exact Fintype.sum_equiv childRepeatedModePairEquiv _ _ fun _ ↦ rfl

end

end ArchonPhysics.ActualTwoMassChildRepeatedAnnealedBridge
