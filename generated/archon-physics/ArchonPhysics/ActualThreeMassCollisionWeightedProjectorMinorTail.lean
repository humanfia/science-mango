import ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
import ArchonPhysics.QuantitativeJacobianGoodBadPushforward

open scoped Matrix BigOperators ENNReal

namespace ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorTail

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
open ArchonPhysics.QuantitativeJacobianGoodBadPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter MeasureTheory Set

noncomputable section

theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_univ_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ univ =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)) univ := by
  classical
  unfold actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [Measure.map_apply
    (measurable_actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes) MeasurableSet.univ]
  simp

theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_univ_le_spectral
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ univ ≤
      actualThreeMassSpectralPerSiteWeightCeiling := by
  rw [actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_univ_eq]
  exact actualThreeMassAllDistinct_sourceMass_div_volume_le_spectral
    fixed hfixed site₀ site₁ site₂

theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_Iio_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ (Iio 0) = 0 := by
  change actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
    fixed site₀ site₁ site₂ 0 = 0
  rw [actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel_eq_source]
  suffices hsum :
      (∑ modes : OrderedModeTriple N,
        (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes))
          {triple |
            actualThreeMassProjectorMinorMagnitude
                fixed site₀ site₁ site₂ modes triple < 0}) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  rw [show {triple |
      actualThreeMassProjectorMinorMagnitude
          fixed site₀ site₁ site₂ modes triple < 0} = ∅ by
    ext triple
    simp [actualThreeMassProjectorMinorMagnitude]]
  exact measure_empty

/-- Fixed-volume actual tail continuity.  If the genuine collision-weighted
minor law has no atom at zero, its reciprocal-natural bad levels vanish.
This gives no volume-uniform rate and therefore does not by itself beat the
linear sinc peak along a thermodynamic time sequence. -/
theorem tendsto_actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel_zero_of_singleton
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (hzero :
      actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ ({0} : Set Real) = 0) :
    Tendsto
      (fun n : Nat =>
        actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
          fixed site₀ site₁ site₂ (1 / ((n : Real) + 1)))
      atTop (nhds 0) := by
  let source : Measure Real :=
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
      fixed site₀ site₁ site₂
  let good : Nat → Set Real := fun n => Ici (1 / ((n : Real) + 1))
  let _ : IsFiniteMeasure source := ⟨by
    have hbound :=
      actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_univ_le_spectral
        fixed hfixed site₀ site₁ site₂
    exact hbound.trans_lt (by
      unfold actualThreeMassSpectralPerSiteWeightCeiling
      exact ENNReal.ofReal_lt_top)⟩
  have hgood : ∀ n, MeasurableSet (good n) := fun _n => measurableSet_Ici
  have hmono : Monotone good := by
    intro n m hnm x hx
    dsimp [good] at hx ⊢
    have hnpos : (0 : Real) < (n : Real) + 1 := by positivity
    have hnmReal : (n : Real) + 1 ≤ (m : Real) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact (one_div_le_one_div_of_le hnpos hnmReal).trans hx
  have hnegative : source (Iio 0) = 0 := by
    exact
      actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_Iio_zero
        fixed site₀ site₁ site₂
  have hnonnegativeAE : ∀ᵐ x ∂source, 0 ≤ x := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp hnegative
    filter_upwards [hnotMem] with x hx
    exact not_lt.mp hx
  have hnonzeroAE : ∀ᵐ x ∂source, x ≠ 0 := by
    exact measure_eq_zero_iff_ae_notMem.mp hzero
  have hcover : ∀ᵐ x ∂source, x ∈ ⋃ n, good n := by
    filter_upwards [hnonnegativeAE, hnonzeroAE] with x hxnonneg hxne
    have hxpos : 0 < x := lt_of_le_of_ne hxnonneg (Ne.symm hxne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hxpos
    exact mem_iUnion.mpr ⟨n, hn.le⟩
  have hlimit :=
    tendsto_measure_compl_good_zero_of_monotone_of_ae_iUnion
      source good hgood hmono hcover
  simpa [source, good,
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel] using
      hlimit

end

end ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorTail
