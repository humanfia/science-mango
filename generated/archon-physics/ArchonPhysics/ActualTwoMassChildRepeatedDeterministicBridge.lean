import ArchonPhysics.ActualTwoMassChildRepeatedAnnealedBridge

/-!
# Deterministic child-pair measure reindexing

The predicate-restricted child-repeated frequency measure is exactly the
pair-indexed measure used by actual two-mass resampling.
-/

open scoped ENNReal

namespace ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedBridge
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

local instance positiveOrderedTriple_decidablePred
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    DecidablePred (IsPositiveOrderedTriple m) :=
  Classical.decPred _

/-- The reduced frequency point attached to one parent/child mode pair. -/
def childRepeatedReducedFrequencyPair
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ChildRepeatedModePair N) : Real × Real :=
  (orderedModeFrequency (harmonicHermitian m) modes.1,
    orderedModeFrequency (harmonicHermitian m) modes.2)

theorem childRepeatedFrequencyProjection_orderedFrequencyTriple_modeTriple
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ChildRepeatedModePair N) :
    childRepeatedFrequencyProjection
        (orderedFrequencyTriple m (childRepeatedModeTriple modes)) =
      childRepeatedReducedFrequencyPair m modes := by
  rfl

/-- Pair-indexed form of the canonical reduced child law at one fixed mass
configuration. -/
def childRepeatedReducedPerSitePairMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Measure (Real × Real) :=
  (N : ENNReal)⁻¹ •
    ∑ modes : ChildRepeatedModePair N,
      if IsPositiveOrderedTriple m (childRepeatedModeTriple modes) then
        ENNReal.ofReal
            (harmonicOrderedNormalizedInteractionWeight m
              (childRepeatedModeTriple modes)) •
          Measure.dirac (childRepeatedReducedFrequencyPair m modes)
      else 0

/-- Exact deterministic identification of the projected predicate-restricted
triple measure with the pair-indexed measure used by two-mass resampling. -/
theorem map_perSiteChildRepeatedFrequencyMeasure_eq_pairMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Measure.map childRepeatedFrequencyProjection
        (perSitePositiveWeightedFrequencyTripleMeasureWhere
          m ChildRepeated) =
      childRepeatedReducedPerSitePairMeasure m := by
  classical
  unfold perSitePositiveWeightedFrequencyTripleMeasureWhere
    positiveWeightedFrequencyTripleMeasureWhere
    childRepeatedReducedPerSitePairMeasure
  rw [Measure.map_smul,
    Measure.map_finset_sum'
      measurable_childRepeatedFrequencyProjection.aemeasurable]
  congr 1
  calc
    (∑ modes : OrderedModeTriple N,
        Measure.map childRepeatedFrequencyProjection
          (if IsPositiveOrderedTriple m modes ∧ ChildRepeated modes then
            ENNReal.ofReal
                (harmonicOrderedNormalizedInteractionWeight m modes) •
              Measure.dirac (orderedFrequencyTriple m modes)
          else 0)) =
      ∑ modes : OrderedModeTriple N,
        if ChildRepeated modes then
          (if IsPositiveOrderedTriple m modes then
            ENNReal.ofReal
                (harmonicOrderedNormalizedInteractionWeight m modes) •
              Measure.dirac
                (childRepeatedFrequencyProjection
                  (orderedFrequencyTriple m modes))
          else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      by_cases hpositive : IsPositiveOrderedTriple m modes
      · by_cases hchild : ChildRepeated modes
        · simp only [hpositive, hchild, and_self, if_true,
            Measure.map_smul,
            Measure.map_dirac'
              measurable_childRepeatedFrequencyProjection]
        · simp [hpositive, hchild]
      · simp [hpositive]
    _ = ∑ modes :
          {modes : OrderedModeTriple N // ChildRepeated modes},
        if IsPositiveOrderedTriple m modes.1 then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m modes.1) •
            Measure.dirac
              (childRepeatedFrequencyProjection
                (orderedFrequencyTriple m modes.1))
        else 0 :=
      sum_if_childRepeated_eq_sum_subtype _
    _ = ∑ modes : ChildRepeatedModePair N,
        if IsPositiveOrderedTriple m (childRepeatedModeTriple modes) then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m
                (childRepeatedModeTriple modes)) •
            Measure.dirac
              (childRepeatedFrequencyProjection
                (orderedFrequencyTriple m (childRepeatedModeTriple modes)))
        else 0 := by
      exact (sum_childRepeatedModePair_eq_sum_subtype
        (F := fun modes =>
          if IsPositiveOrderedTriple m modes then
            ENNReal.ofReal
                (harmonicOrderedNormalizedInteractionWeight m modes) •
              Measure.dirac
                (childRepeatedFrequencyProjection
                  (orderedFrequencyTriple m modes))
          else 0)).symm
    _ = ∑ modes : ChildRepeatedModePair N,
        if IsPositiveOrderedTriple m (childRepeatedModeTriple modes) then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m
                (childRepeatedModeTriple modes)) •
            Measure.dirac (childRepeatedReducedFrequencyPair m modes)
        else 0 := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      by_cases hpositive :
          IsPositiveOrderedTriple m (childRepeatedModeTriple modes)
      · simp only [hpositive, if_true]
        rw [childRepeatedFrequencyProjection_orderedFrequencyTriple_modeTriple]
      · simp [hpositive]

end

end ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge
