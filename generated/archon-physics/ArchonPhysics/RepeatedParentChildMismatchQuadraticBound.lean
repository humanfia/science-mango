import ArchonPhysics.RepeatedParentChildMismatchSmallBall

/-!
# Uniform quadratic mismatch bounds for repeated parent--child sectors

The explicit small-ball identity for the first equality plane is extended to
the second plane and transferred to the two disjoint mode-partition sectors.
For every frozen iid realization and every finite volume, the real per-site
mass in `|Delta| <= delta` is bounded by `5 * delta^2 / 8`.
-/

namespace ArchonPhysics.RepeatedParentChildMismatchQuadraticBound

open ArchonPhysics
open ArchonPhysics.ActualThreeMassRepeatedChildModeObstruction
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
open ArchonPhysics.RepeatedParentChildMismatchMeasureBridge
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open MeasureTheory Set

noncomputable section

/-- The complete `0 = 2` plane has exactly its remaining-child cumulative
weight in a symmetric mismatch window. -/
theorem positiveRepeatedZeroTwoMismatchMeasure_absoluteSublevel_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    positiveRepeatedZeroTwoMismatchMeasure m
        (absoluteMismatchSublevel delta) =
      ENNReal.ofReal
        (positiveRepeatedZeroTwoSoftChildInteractionWeight m delta) := by
  classical
  unfold positiveRepeatedZeroTwoMismatchMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  have hterm (k q : OrderedModeIndex N) :
      ((if IsPositiveOrderedTriple m ![k, q, k] then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m ![k, q, k]) •
            Measure.dirac
              (orderedThreeWaveMismatch
                m decayInteractionSign ![k, q, k])
        else 0) : Measure Real) (absoluteMismatchSublevel delta) =
        ENNReal.ofReal
          (if IsPositiveOrderedTriple m ![k, q, k] ∧
              orderedModeFrequency (harmonicHermitian m) q <= delta then
            harmonicOrderedNormalizedInteractionWeight m ![k, q, k]
          else 0) := by
    have habs :
        |orderedThreeWaveMismatch m decayInteractionSign ![k, q, k]| =
          orderedModeFrequency (harmonicHermitian m) q :=
      abs_orderedThreeWaveMismatch_decay_of_parent_eq_childTwo
        m ![k, q, k] (by simp)
    by_cases hpositive : IsPositiveOrderedTriple m ![k, q, k]
    · by_cases hsoft :
          orderedModeFrequency (harmonicHermitian m) q <= delta
      · simp [hpositive, hsoft, absoluteMismatchSublevel, habs]
      · simp [hpositive, hsoft, absoluteMismatchSublevel, habs]
    · simp [hpositive]
  calc
    (∑ k, ∑ q,
      ((if IsPositiveOrderedTriple m ![k, q, k] then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m ![k, q, k]) •
            Measure.dirac
              (orderedThreeWaveMismatch
                m decayInteractionSign ![k, q, k])
        else 0) : Measure Real) (absoluteMismatchSublevel delta)) =
        ∑ k, ∑ q, ENNReal.ofReal
          (if IsPositiveOrderedTriple m ![k, q, k] ∧
              orderedModeFrequency (harmonicHermitian m) q <= delta then
            harmonicOrderedNormalizedInteractionWeight m ![k, q, k]
          else 0) := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro q _hq
      exact hterm k q
    _ = ENNReal.ofReal
        (positiveRepeatedZeroTwoSoftChildInteractionWeight m delta) := by
      unfold positiveRepeatedZeroTwoSoftChildInteractionWeight
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro q _hq
        split_ifs
        · exact harmonicOrderedNormalizedInteractionWeight_nonneg
            m ![k, q, k]
        · rfl
      · intro k _hk
        apply Finset.sum_nonneg
        intro q _hq
        split_ifs
        · exact harmonicOrderedNormalizedInteractionWeight_nonneg
            m ![k, q, k]
        · rfl

theorem positiveRepeatedZeroOneSoftChildInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    0 <= positiveRepeatedZeroOneSoftChildInteractionWeight m delta := by
  classical
  unfold positiveRepeatedZeroOneSoftChildInteractionWeight
  apply Finset.sum_nonneg
  intro k _hk
  apply Finset.sum_nonneg
  intro q _hq
  split_ifs
  · exact harmonicOrderedNormalizedInteractionWeight_nonneg m ![k, k, q]
  · rfl

theorem positiveRepeatedZeroTwoSoftChildInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    0 <= positiveRepeatedZeroTwoSoftChildInteractionWeight m delta := by
  rw [positiveRepeatedZeroTwoSoftChildInteractionWeight_eq_zeroOne]
  exact positiveRepeatedZeroOneSoftChildInteractionWeight_nonneg m delta

/-- The disjoint `0 = 1` partition sector inherits the complete-plane
small-ball upper bound. -/
theorem parentChildOneRepeated_mismatchMeasure_absoluteSublevel_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildOneRepeated
        (absoluteMismatchSublevel delta) <=
      ENNReal.ofReal
        (positiveRepeatedZeroOneSoftChildInteractionWeight m delta) := by
  calc
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildOneRepeated
        (absoluteMismatchSublevel delta) <=
      positiveRepeatedZeroOneMismatchMeasure m
        (absoluteMismatchSublevel delta) :=
      parentChildOneRepeated_mismatchMeasure_le_completePlane m _
    _ = _ :=
      positiveRepeatedZeroOneMismatchMeasure_absoluteSublevel_eq m delta

/-- The disjoint `0 = 2` sector has the symmetric bound. -/
theorem parentChildTwoRepeated_mismatchMeasure_absoluteSublevel_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildTwoRepeated
        (absoluteMismatchSublevel delta) <=
      ENNReal.ofReal
        (positiveRepeatedZeroTwoSoftChildInteractionWeight m delta) := by
  calc
    positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildTwoRepeated
        (absoluteMismatchSublevel delta) <=
      positiveRepeatedZeroTwoMismatchMeasure m
        (absoluteMismatchSublevel delta) :=
      parentChildTwoRepeated_mismatchMeasure_le_completePlane m _
    _ = _ :=
      positiveRepeatedZeroTwoMismatchMeasure_absoluteSublevel_eq m delta

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Frozen-iid per-site quadratic small-ball bound for the first disjoint
parent--child sector. -/
theorem iid_parentChildOneRepeated_mismatchMeasure_toReal_div_volume_le_sq
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1) :
    (positiveWeightedMismatchMeasureWhere
        (ensemble.restrictPositiveMass (N := N) omega)
        decayInteractionSign ParentChildOneRepeated
        (absoluteMismatchSublevel delta)).toReal / (N : Real) <=
      (5 / 8 : Real) * delta ^ 2 := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hmeasure :=
    parentChildOneRepeated_mismatchMeasure_absoluteSublevel_le m delta
  have hreal :
      (positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildOneRepeated
        (absoluteMismatchSublevel delta)).toReal <=
          positiveRepeatedZeroOneSoftChildInteractionWeight m delta := by
    simpa [ENNReal.toReal_ofReal,
      positiveRepeatedZeroOneSoftChildInteractionWeight_nonneg m delta] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hN : 0 <= (N : Real) := by positivity
  exact (div_le_div_of_nonneg_right hreal hN).trans
    (iid_positiveRepeatedZeroOneSoftChildInteractionWeight_div_volume_le_sq
      ensemble omega hdelta hdelta1)

/-- Frozen-iid per-site quadratic bound for the second sector. -/
theorem iid_parentChildTwoRepeated_mismatchMeasure_toReal_div_volume_le_sq
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1) :
    (positiveWeightedMismatchMeasureWhere
        (ensemble.restrictPositiveMass (N := N) omega)
        decayInteractionSign ParentChildTwoRepeated
        (absoluteMismatchSublevel delta)).toReal / (N : Real) <=
      (5 / 8 : Real) * delta ^ 2 := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hmeasure :=
    parentChildTwoRepeated_mismatchMeasure_absoluteSublevel_le m delta
  have hreal :
      (positiveWeightedMismatchMeasureWhere
        m decayInteractionSign ParentChildTwoRepeated
        (absoluteMismatchSublevel delta)).toReal <=
          positiveRepeatedZeroTwoSoftChildInteractionWeight m delta := by
    simpa [ENNReal.toReal_ofReal,
      positiveRepeatedZeroTwoSoftChildInteractionWeight_nonneg m delta] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hN : 0 <= (N : Real) := by positivity
  exact (div_le_div_of_nonneg_right hreal hN).trans
    (iid_positiveRepeatedZeroTwoSoftChildInteractionWeight_div_volume_le_sq
      ensemble omega hdelta hdelta1)

end

end ArchonPhysics.RepeatedParentChildMismatchQuadraticBound
