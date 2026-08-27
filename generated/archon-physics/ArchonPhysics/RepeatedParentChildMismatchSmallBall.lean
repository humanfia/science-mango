import ArchonPhysics.RepeatedParentChildMismatchMeasureBridge

/-!
# Quadratic mismatch small balls for repeated parent--child sectors

This module evaluates the complete repeated parent--child mismatch measures
on symmetric windows about zero.  In the decay channel their mismatch
magnitudes are exactly the remaining positive child frequency, so the measure
of `|Delta| <= delta` is exactly the acoustic cumulative interaction weight.
The disjoint mode-partition sectors inherit the same uniform quadratic bound
by measure domination.
-/

namespace ArchonPhysics.RepeatedParentChildMismatchSmallBall

open ArchonPhysics
open ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
open ArchonPhysics.RepeatedParentChildMismatchMeasureBridge
open MeasureTheory Set

noncomputable section

/-- Symmetric closed mismatch window. -/
def absoluteMismatchSublevel (delta : Real) : Set Real :=
  {mismatch | |mismatch| <= delta}

theorem measurableSet_absoluteMismatchSublevel (delta : Real) :
    MeasurableSet (absoluteMismatchSublevel delta) := by
  exact (isClosed_le continuous_abs continuous_const).measurableSet

/-- The complete `0 = 1` plane has exactly the cumulative remaining-child
weight in a symmetric mismatch window. -/
theorem positiveRepeatedZeroOneMismatchMeasure_absoluteSublevel_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    positiveRepeatedZeroOneMismatchMeasure m
        (absoluteMismatchSublevel delta) =
      ENNReal.ofReal
        (positiveRepeatedZeroOneSoftChildInteractionWeight m delta) := by
  classical
  unfold positiveRepeatedZeroOneMismatchMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  have hterm (k q : OrderedModeIndex N) :
      ((if IsPositiveOrderedTriple m ![k, k, q] then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m ![k, k, q]) •
            Measure.dirac
              (orderedThreeWaveMismatch
                m decayInteractionSign ![k, k, q])
        else 0) : Measure Real) (absoluteMismatchSublevel delta) =
        ENNReal.ofReal
          (if IsPositiveOrderedTriple m ![k, k, q] ∧
              orderedModeFrequency (harmonicHermitian m) q <= delta then
            harmonicOrderedNormalizedInteractionWeight m ![k, k, q]
          else 0) := by
    have habs :
        |orderedThreeWaveMismatch m decayInteractionSign ![k, k, q]| =
          orderedModeFrequency (harmonicHermitian m) q :=
      abs_orderedThreeWaveMismatch_decay_of_parent_eq_childOne
        m ![k, k, q] (by simp)
    by_cases hpositive : IsPositiveOrderedTriple m ![k, k, q]
    · by_cases hsoft :
          orderedModeFrequency (harmonicHermitian m) q <= delta
      · simp [hpositive, hsoft, absoluteMismatchSublevel, habs]
      · simp [hpositive, hsoft, absoluteMismatchSublevel, habs]
    · simp [hpositive]
  calc
    (∑ k, ∑ q,
      ((if IsPositiveOrderedTriple m ![k, k, q] then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m ![k, k, q]) •
            Measure.dirac
              (orderedThreeWaveMismatch
                m decayInteractionSign ![k, k, q])
        else 0) : Measure Real) (absoluteMismatchSublevel delta)) =
        ∑ k, ∑ q, ENNReal.ofReal
          (if IsPositiveOrderedTriple m ![k, k, q] ∧
              orderedModeFrequency (harmonicHermitian m) q <= delta then
            harmonicOrderedNormalizedInteractionWeight m ![k, k, q]
          else 0) := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro q _hq
      exact hterm k q
    _ = ENNReal.ofReal
        (positiveRepeatedZeroOneSoftChildInteractionWeight m delta) := by
      unfold positiveRepeatedZeroOneSoftChildInteractionWeight
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro q _hq
        split_ifs
        · exact harmonicOrderedNormalizedInteractionWeight_nonneg
            m ![k, k, q]
        · rfl
      · intro k _hk
        apply Finset.sum_nonneg
        intro q _hq
        split_ifs
        · exact harmonicOrderedNormalizedInteractionWeight_nonneg
            m ![k, k, q]
        · rfl

end

end ArchonPhysics.RepeatedParentChildMismatchSmallBall
