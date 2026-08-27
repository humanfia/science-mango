import ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge

/-!
# Conditional Fubini identity for the actual child-pair measure

For a fixed finite-volume environment, integrating the exact reduced
child-repeated measure over two resampled iid masses is exactly the summed
actual two-mass conditional spectral measure.
-/

open scoped ENNReal

namespace ArchonPhysics.ActualTwoMassChildRepeatedConditionalFubini

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

/-- The measurable atom integrand appearing after evaluating one conditional
pair pushforward on a measurable target. -/
def actualTwoMassChildRepeatedAtomIntegrand
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (modes : ChildRepeatedModePair N)
    (A : Set (Real × Real)) (pair : Real × Real) : ENNReal :=
  actualTwoMassChildRepeatedPositivePairWeight
      fixed site₁ site₂ modes pair *
    A.indicator 1
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2 pair)

theorem measurable_actualTwoMassChildRepeatedAtomIntegrand
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (modes : ChildRepeatedModePair N)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    Measurable
      (actualTwoMassChildRepeatedAtomIntegrand
        fixed site₁ site₂ modes A) := by
  apply (measurable_actualTwoMassChildRepeatedPositivePairWeight
    fixed site₁ site₂ modes).mul
  exact (Measurable.indicator measurable_const hA).comp
    (continuous_actualTwoMassChildFrequencyChart
      fixed site₁ site₂ modes.1 modes.2).measurable

/-- Evaluation of one chart pushforward is the integral of its explicit atom
integrand. -/
theorem actualTwoMassChildRepeatedConditionalPairMeasure_apply_eq_lintegral_atomIntegrand
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (modes : ChildRepeatedModePair N)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    actualTwoMassChildRepeatedConditionalPairMeasure
        fixed site₁ site₂ modes
          (actualTwoMassChildRepeatedPositivePairWeight
            fixed site₁ site₂ modes) A =
      ∫⁻ pair,
        actualTwoMassChildRepeatedAtomIntegrand
          fixed site₁ site₂ modes A pair
        ∂iidMassPairLaw := by
  unfold actualTwoMassChildRepeatedConditionalPairMeasure
  rw [Measure.map_apply
      (continuous_actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2).measurable hA,
    withDensity_apply _
      ((continuous_actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2).measurable hA),
    ← lintegral_indicator
      ((continuous_actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2).measurable hA)]
  apply lintegral_congr
  intro pair
  unfold actualTwoMassChildRepeatedAtomIntegrand
  by_cases hmem :
      actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2 pair ∈ A
  · simp [hmem]
  · simp [hmem]

/-- Pointwise evaluation of the deterministic resampled reduced measure is
the normalized finite sum of the same atom integrands. -/
theorem childRepeatedReducedPerSitePairMeasure_twoSite_apply_eq_sum_atomIntegrand
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    {A : Set (Real × Real)} (hA : MeasurableSet A)
    (pair : Real × Real) :
    childRepeatedReducedPerSitePairMeasure
        (twoSiteMassConfig fixed site₁ site₂ pair) A =
      (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          actualTwoMassChildRepeatedAtomIntegrand
            fixed site₁ site₂ modes A pair := by
  classical
  unfold childRepeatedReducedPerSitePairMeasure
    actualTwoMassChildRepeatedAtomIntegrand
    actualTwoMassChildRepeatedPositivePairWeight
    childRepeatedReducedFrequencyPair
    actualTwoMassChildFrequencyChart
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, ENNReal.smul_def, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hA]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple
      (twoSiteMassConfig fixed site₁ site₂ pair)
      (childRepeatedModeTriple modes)
  · simp [hpositive, twoSiteHarmonicHermitian]
  · simp [hpositive]

/-- Exact conditional Fubini identity for the full normalized child-repeated
pair law. -/
theorem actualTwoMassChildRepeatedConditionalPerSiteMeasure_apply_eq_lintegral_pairMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    actualTwoMassChildRepeatedConditionalPerSiteMeasure
        fixed site₁ site₂
          (actualTwoMassChildRepeatedPositivePairWeight
            fixed site₁ site₂) A =
      ∫⁻ pair,
        childRepeatedReducedPerSitePairMeasure
          (twoSiteMassConfig fixed site₁ site₂ pair) A
        ∂iidMassPairLaw := by
  classical
  rw [show (∫⁻ pair,
        childRepeatedReducedPerSitePairMeasure
          (twoSiteMassConfig fixed site₁ site₂ pair) A
        ∂iidMassPairLaw) =
      ∫⁻ pair, (N : ENNReal)⁻¹ *
        (∑ modes : ChildRepeatedModePair N,
          actualTwoMassChildRepeatedAtomIntegrand
            fixed site₁ site₂ modes A pair)
        ∂iidMassPairLaw by
      apply lintegral_congr
      intro pair
      exact
        childRepeatedReducedPerSitePairMeasure_twoSite_apply_eq_sum_atomIntegrand
          fixed site₁ site₂ hA pair]
  rw [lintegral_const_mul _
      (Finset.measurable_sum _ fun modes _ ↦
        measurable_actualTwoMassChildRepeatedAtomIntegrand
          fixed site₁ site₂ modes hA),
    lintegral_finsetSum Finset.univ (fun modes _ ↦
      measurable_actualTwoMassChildRepeatedAtomIntegrand
        fixed site₁ site₂ modes hA)]
  unfold actualTwoMassChildRepeatedConditionalPerSiteMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, ENNReal.smul_def]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  exact
    actualTwoMassChildRepeatedConditionalPairMeasure_apply_eq_lintegral_atomIntegrand
      fixed site₁ site₂ modes hA

end

end ArchonPhysics.ActualTwoMassChildRepeatedConditionalFubini
