import ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas

/-!
# Quantitative good/bad small ball for the actual three-site outer mismatch

This module converts the compact augmented-chart domination into a scalar
small-ball bound.  For every compact interior set separated from the inverse
mass diagonal it produces one finite coefficient and keeps the exact iid
mass of the compact complement.  A concrete `delta`-dependent compact set is
introduced below, where the complement is estimated independently.
-/

open scoped ENNReal

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas
open ArchonPhysics.ActualThreeSiteIteratedA2OuterInverseMassStrip
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- Centered near-mismatch event in the three raw mass coordinates. -/
def threeSiteOuterNearMismatchEvent (epsilon : Real) : Set MassTriple :=
  {triple | |threeSiteOuterTripleMismatch triple| ≤ epsilon}

theorem measurableSet_threeSiteOuterNearMismatchEvent (epsilon : Real) :
    MeasurableSet (threeSiteOuterNearMismatchEvent epsilon) := by
  exact measurableSet_le
    continuous_threeSiteOuterTripleMismatch.abs.measurable measurable_const

/-- Bounded target box for the augmented chart.  The retained masses lie in
`[0,2]` throughout the iid support. -/
def threeSiteOuterAugmentedSmallBallTarget (epsilon : Real) : Set MassTriple :=
  (Icc (-epsilon) epsilon ×ˢ Icc 0 2) ×ˢ Icc 0 2

theorem measurableSet_threeSiteOuterAugmentedSmallBallTarget
    (epsilon : Real) :
    MeasurableSet (threeSiteOuterAugmentedSmallBallTarget epsilon) :=
  (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc

/-- Exact volume of the bounded augmented target box. -/
theorem volume_threeSiteOuterAugmentedSmallBallTarget
    {epsilon : Real} (_hepsilon : 0 ≤ epsilon) :
    (volume : Measure MassTriple)
        (threeSiteOuterAugmentedSmallBallTarget epsilon) =
      8 * ENNReal.ofReal epsilon := by
  change ((volume : Measure (Real × Real)).prod (volume : Measure Real))
      ((Icc (-epsilon) epsilon ×ˢ Icc 0 2) ×ˢ Icc 0 2) = _
  rw [Measure.prod_prod]
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  rw [Real.volume_Icc]
  have hlength : epsilon - -epsilon = 2 * epsilon := by ring
  rw [hlength,
    ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
  norm_num
  ring

/-- On a compact interior inverse-separated set, the actual scalar mismatch
has a linear small-ball bound plus the exact compact-complement mass.  The
coefficient is finite, but no dependence on the compact set is claimed. -/
theorem exists_finiteCoefficient_threeSiteOuter_compact_goodBad_smallBall
    (K : Set MassTriple) (hK : IsCompact K)
    (hKInterior : K ⊆ interior iidMassTripleSupport)
    (hKSeparated : ∀ triple ∈ K, triple.1.1⁻¹ ≠ triple.2⁻¹) :
    ∃ coefficient : ENNReal, coefficient ≠ ∞ ∧
      ∀ epsilon : Real, 0 ≤ epsilon →
        iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
          coefficient * ENNReal.ofReal epsilon + iidMassTripleLaw Kᶜ := by
  classical
  obtain ⟨detLower, atlasCard, hdetLower, hmap⟩ :=
    exists_detLower_atlasCard_threeSiteOuterAugmented_map_restrict_le
      K hK hKInterior hKSeparated
  let density : ENNReal :=
    (atlasCard : ENNReal) * (27 * (ENNReal.ofReal detLower)⁻¹)
  let coefficient : ENNReal := density * 8
  have hdetNonzero : ENNReal.ofReal detLower ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hdetLower
  have hdensityFinite : density ≠ ∞ := by
    dsimp [density]
    exact ENNReal.mul_ne_top (by finiteness)
      (ENNReal.mul_ne_top (by finiteness)
        (ENNReal.inv_ne_top.mpr hdetNonzero))
  have hcoefficientFinite : coefficient ≠ ∞ := by
    exact ENNReal.mul_ne_top hdensityFinite (by finiteness)
  refine ⟨coefficient, hcoefficientFinite, ?_⟩
  intro epsilon hepsilon
  let event := threeSiteOuterNearMismatchEvent epsilon
  let target := threeSiteOuterAugmentedSmallBallTarget epsilon
  have hevent : MeasurableSet event :=
    measurableSet_threeSiteOuterNearMismatchEvent epsilon
  have htarget : MeasurableSet target :=
    measurableSet_threeSiteOuterAugmentedSmallBallTarget epsilon
  have hKmeasurable : MeasurableSet K := hK.isClosed.measurableSet
  have hgoodSubset : event ∩ K ⊆
      (threeSiteOuterAugmentedChart ⁻¹' target) ∩ K := by
    intro triple htriple
    have hsupport := interior_subset (hKInterior htriple.2)
    rw [iidMassTripleSupport, iidMassPairSupport] at hsupport
    have hfirstNonneg : 0 ≤ triple.1.1 :=
      le_trans (le_of_lt massLower_pos) hsupport.1.1.1
    have hthirdNonneg : 0 ≤ triple.2 :=
      le_trans (le_of_lt massLower_pos) hsupport.2.1
    have hfirstUpper : triple.1.1 ≤ 2 := by
      exact hsupport.1.1.2.trans (by norm_num [massUpper])
    have hthirdUpper : triple.2 ≤ 2 := by
      exact hsupport.2.2.trans (by norm_num [massUpper])
    refine ⟨?_, htriple.2⟩
    change ((threeSiteOuterTripleMismatch triple, triple.1.1), triple.2) ∈
      (Icc (-epsilon) epsilon ×ˢ Icc 0 2) ×ˢ Icc 0 2
    exact ⟨⟨abs_le.mp htriple.1, ⟨hfirstNonneg, hfirstUpper⟩⟩,
      ⟨hthirdNonneg, hthirdUpper⟩⟩
  have hgood : iidMassTripleLaw.restrict K event ≤
      coefficient * ENNReal.ofReal epsilon := by
    have hmapApply := hmap target
    rw [Measure.smul_apply] at hmapApply
    calc
      iidMassTripleLaw.restrict K event =
          iidMassTripleLaw (event ∩ K) := by
        rw [Measure.restrict_apply hevent]
      _ ≤ iidMassTripleLaw
          ((threeSiteOuterAugmentedChart ⁻¹' target) ∩ K) :=
        measure_mono hgoodSubset
      _ = iidMassTripleLaw.restrict K
          (threeSiteOuterAugmentedChart ⁻¹' target) := by
        rw [Measure.restrict_apply
          (htarget.preimage measurable_threeSiteOuterAugmentedChart)]
      _ = Measure.map threeSiteOuterAugmentedChart
          (iidMassTripleLaw.restrict K) target := by
        rw [Measure.map_apply measurable_threeSiteOuterAugmentedChart htarget]
      _ ≤ density * (volume : Measure MassTriple) target := by
        exact hmapApply
      _ = coefficient * ENNReal.ofReal epsilon := by
        rw [volume_threeSiteOuterAugmentedSmallBallTarget hepsilon]
        simp [coefficient, density, mul_assoc]
  have hbad : iidMassTripleLaw.restrict Kᶜ event ≤ iidMassTripleLaw Kᶜ := by
    rw [Measure.restrict_apply hevent]
    exact measure_mono inter_subset_right
  have hsplit : iidMassTripleLaw =
      iidMassTripleLaw.restrict K + iidMassTripleLaw.restrict Kᶜ :=
    (iidMassTripleLaw.restrict_add_restrict_compl hKmeasurable).symm
  calc
    iidMassTripleLaw event = iidMassTripleLaw.restrict K event +
        iidMassTripleLaw.restrict Kᶜ event := by
      simpa only [Measure.add_apply] using congrArg (fun μ => μ event) hsplit
    _ ≤ coefficient * ENNReal.ofReal epsilon + iidMassTripleLaw Kᶜ :=
      add_le_add hgood hbad

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
