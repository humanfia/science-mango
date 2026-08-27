import ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution

open scoped Matrix BigOperators ENNReal

namespace ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
open ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

theorem iidMassTriple_mem_support_ae :
    ∀ᵐ triple ∂iidMassTripleLaw, triple ∈ iidMassTripleSupport := by
  have hpair : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ iidMassPairSupport := by
    rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [massCoordinate_mem_support_ae] with first hfirst
      filter_upwards [massCoordinate_mem_support_ae] with second hsecond
      exact ⟨hfirst, hsecond⟩
    · exact measurableSet_Icc.prod measurableSet_Icc
  rw [iidMassTripleLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hpair] with pair hpair
    filter_upwards [massCoordinate_mem_support_ae] with third hthird
    exact ⟨hpair, hthird⟩
  · exact (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc

/-- Frozen-support ceiling for the exact nonsingular multiplier left after
the elementary frequency and raw-mass Jacobian factors cancel. -/
def actualThreeMassProjectorResidualScaleCeiling : ENNReal :=
  ENNReal.ofReal
    ((2 * Real.sqrt 5) ^ 3 * (((6 / 5 : Real) ^ 2) ^ 3))

theorem actualThreeMassProjectorResidualScale_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (triple : MassTriple)
    (htriple : triple ∈ iidMassTripleSupport) :
    actualThreeMassProjectorResidualScale
        fixed site₀ site₁ site₂ modes triple ≤
      actualThreeMassProjectorResidualScaleCeiling := by
  unfold actualThreeMassProjectorResidualScale
    actualThreeMassProjectorResidualScaleCeiling
  apply ENNReal.ofReal_le_ofReal
  have hfrequencyProduct :
      (∏ r : Fin 3, 2 * orderedModeFrequency
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
          (modes r)) ≤
        (2 * Real.sqrt 5) ^ 3 := by
    have hprod := Finset.prod_le_prod
      (s := Finset.univ)
      (f := fun r : Fin 3 => 2 * orderedModeFrequency
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
          (modes r))
      (g := fun _r : Fin 3 => 2 * Real.sqrt 5)
      (fun r _hr => mul_nonneg zero_le_two (Real.sqrt_nonneg _))
      (fun r _hr => mul_le_mul_of_nonneg_left
        (actualThreeMass_orderedModeFrequency_le_sqrt_five
          fixed hfixed site₀ site₁ site₂ triple (modes r)) zero_le_two)
    simpa [Fin.prod_univ_three, pow_succ] using hprod
  have hrawMem (s : Fin 3) :
      actualThreeMassRawCoordinate triple s ∈ massSupport := by
    fin_cases s
    · simpa [actualThreeMassRawCoordinate] using htriple.1.1
    · simpa [actualThreeMassRawCoordinate] using htriple.1.2
    · simpa [actualThreeMassRawCoordinate] using htriple.2
  have hmassProduct :
      (∏ s : Fin 3, (actualThreeMassRawCoordinate triple s) ^ 2) ≤
        (((6 / 5 : Real) ^ 2) ^ 3) := by
    have hprod := Finset.prod_le_prod
      (s := Finset.univ)
      (f := fun s : Fin 3 => (actualThreeMassRawCoordinate triple s) ^ 2)
      (g := fun _s : Fin 3 => (6 / 5 : Real) ^ 2)
      (fun s _hs => sq_nonneg (actualThreeMassRawCoordinate triple s))
      (fun s _hs => by
        have hnonneg : 0 ≤ actualThreeMassRawCoordinate triple s :=
          massLower_pos.le.trans (hrawMem s).1
        have hupper : actualThreeMassRawCoordinate triple s ≤ (6 / 5 : Real) := by
          simpa [massUpper] using (hrawMem s).2
        exact (sq_le_sq₀ hnonneg (by norm_num)).2 hupper)
    simpa [Fin.prod_univ_three, pow_succ] using hprod
  calc
    (∏ r : Fin 3, 2 * orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
            (modes r)) *
        ∏ s : Fin 3, (actualThreeMassRawCoordinate triple s) ^ 2 ≤
      (2 * Real.sqrt 5) ^ 3 *
        ∏ s : Fin 3, (actualThreeMassRawCoordinate triple s) ^ 2 :=
      mul_le_mul_of_nonneg_right hfrequencyProduct
        (Finset.prod_nonneg fun s _hs =>
          sq_nonneg (actualThreeMassRawCoordinate triple s))
    _ ≤ (2 * Real.sqrt 5) ^ 3 * (((6 / 5 : Real) ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left hmassProduct (by positivity)

theorem actualThreeMassProjectorResidualScale_le_ae
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    ∀ᵐ triple ∂iidMassTripleLaw,
      actualThreeMassProjectorResidualScale
          fixed site₀ site₁ site₂ modes triple ≤
        actualThreeMassProjectorResidualScaleCeiling := by
  filter_upwards [iidMassTriple_mem_support_ae] with triple htriple
  exact actualThreeMassProjectorResidualScale_le
    fixed hfixed site₀ site₁ site₂ modes triple htriple

theorem withDensity_actualThreeMassAllDistinctProjectorResidualWeight_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    iidMassTripleLaw.withDensity
        (actualThreeMassAllDistinctProjectorResidualWeight
          fixed site₀ site₁ site₂ modes) ≤
      actualThreeMassProjectorResidualScaleCeiling •
        iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes) := by
  calc
    iidMassTripleLaw.withDensity
        (actualThreeMassAllDistinctProjectorResidualWeight
          fixed site₀ site₁ site₂ modes) ≤
      iidMassTripleLaw.withDensity
        (actualThreeMassProjectorResidualScaleCeiling •
          actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes) := by
      apply withDensity_mono
      filter_upwards
        [actualThreeMassProjectorResidualScale_le_ae
          fixed hfixed site₀ site₁ site₂ modes] with triple hscale
      unfold actualThreeMassAllDistinctProjectorResidualWeight
      change actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂ modes triple *
          actualThreeMassProjectorResidualScale
            fixed site₀ site₁ site₂ modes triple ≤
        actualThreeMassProjectorResidualScaleCeiling *
          actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes triple
      rw [mul_comm actualThreeMassProjectorResidualScaleCeiling]
      exact mul_le_mul_right hscale _
    _ = actualThreeMassProjectorResidualScaleCeiling •
        iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes) := by
      exact withDensity_smul _
        (measurable_actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂ modes)

/-- The actual weighted projector-minor distribution has an explicit total
mass bound independent of the volume.  This is a finite-mass estimate only;
it does not assert the stronger small-minor tail needed for inverse moments. -/
theorem actualThreeMassAllDistinctWeightedProjectorMinorDistribution_univ_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N) :
    actualThreeMassAllDistinctWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ univ ≤
      actualThreeMassProjectorResidualScaleCeiling *
        actualThreeMassSpectralPerSiteWeightCeiling := by
  classical
  have hmode (modes : OrderedModeTriple N) :
      Measure.map
          (actualThreeMassProjectorMinorMagnitude
            fixed site₀ site₁ site₂ modes)
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctProjectorResidualWeight
              fixed site₀ site₁ site₂ modes)) univ ≤
        actualThreeMassProjectorResidualScaleCeiling *
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)) univ := by
    rw [Measure.map_apply
      (measurable_actualThreeMassProjectorMinorMagnitude
        fixed site₀ site₁ site₂ modes) MeasurableSet.univ]
    simp only [preimage_univ]
    calc
      (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctProjectorResidualWeight
            fixed site₀ site₁ site₂ modes)) univ ≤
        (actualThreeMassProjectorResidualScaleCeiling •
          iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)) univ :=
        (withDensity_actualThreeMassAllDistinctProjectorResidualWeight_le
          fixed hfixed site₀ site₁ site₂ modes) univ
      _ = actualThreeMassProjectorResidualScaleCeiling *
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes)) univ := by simp
  unfold actualThreeMassAllDistinctWeightedProjectorMinorDistribution
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          Measure.map
            (actualThreeMassProjectorMinorMagnitude
              fixed site₀ site₁ site₂ modes)
            (iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctProjectorResidualWeight
                fixed site₀ site₁ site₂ modes)) univ ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassProjectorResidualScaleCeiling *
            (iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes)) univ := by
      exact mul_le_mul_right
        (Finset.sum_le_sum fun modes _hmodes => hmode modes) _
    _ = actualThreeMassProjectorResidualScaleCeiling *
        ((N : ENNReal)⁻¹ *
          ∑ modes : OrderedModeTriple N,
            (iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes)) univ) := by
      rw [← Finset.mul_sum]
      ac_rfl
    _ ≤ actualThreeMassProjectorResidualScaleCeiling *
        actualThreeMassSpectralPerSiteWeightCeiling :=
      mul_le_mul_right
        (actualThreeMassAllDistinct_sourceMass_div_volume_le_spectral
          fixed hfixed site₀ site₁ site₂)
        actualThreeMassProjectorResidualScaleCeiling

theorem actualThreeMassAllDistinctWeightedProjectorMinorBadLevel_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N) (delta : Real) :
    actualThreeMassAllDistinctWeightedProjectorMinorBadLevel
        fixed site₀ site₁ site₂ delta ≤
      actualThreeMassProjectorResidualScaleCeiling *
        actualThreeMassSpectralPerSiteWeightCeiling := by
  exact (measure_mono (subset_univ (Iio delta))).trans
    (actualThreeMassAllDistinctWeightedProjectorMinorDistribution_univ_le
      fixed hfixed site₀ site₁ site₂)

end

end ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound
