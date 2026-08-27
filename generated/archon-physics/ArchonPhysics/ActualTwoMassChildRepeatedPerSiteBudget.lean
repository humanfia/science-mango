import ArchonPhysics.ActualTwoMassChildRepeatedResonanceStripBound
import ArchonPhysics.RandomMassPositiveCollisionData
import ArchonPhysics.RepeatedParentChildMismatchSmallBall

/-!
# Per-site two-mass budget for the child-repeated sector

For the child-repeated tuple `![parent, child, child]`, this module sums the
actual two-mass coarea estimate over the genuine ordered parent/child mode
pairs, retaining the canonical `1 / N` normalization.  The regular budget is
the exact coupling-weighted reciprocal-Jacobian sum and the bad budget is the
exact weighted source mass outside the chosen regular patches.

No cardinality bound is substituted for either sum.  Consequently the two
remaining model estimates are exposed without an artificial power of `N`.
-/

namespace ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedResonanceStripBound
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The two independent mode labels of a child-repeated ordered triple. -/
abbrev ChildRepeatedModePair (N : Nat) [NeZero N] :=
  OrderedModeIndex N × OrderedModeIndex N

/-- Reconstruct the child-repeated ordered triple from its parent and common
child labels. -/
def childRepeatedModeTriple {N : Nat} [NeZero N]
    (modes : ChildRepeatedModePair N) : OrderedModeTriple N :=
  ![modes.1, modes.2, modes.2]

/-- Genuine positive collision weight of one child-repeated mode pair after
the two selected masses are resampled. -/
def actualTwoMassChildRepeatedPositivePairWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (modes : ChildRepeatedModePair N) (pair : Real × Real) : ENNReal := by
  classical
  let mass := twoSiteMassConfig fixed site₁ site₂ pair
  exact if IsPositiveOrderedTriple mass (childRepeatedModeTriple modes) then
      ENNReal.ofReal
        (harmonicOrderedNormalizedInteractionWeight mass
          (childRepeatedModeTriple modes))
    else 0

theorem measurable_actualTwoMassChildRepeatedPositivePairWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (modes : ChildRepeatedModePair N) :
    Measurable
      (actualTwoMassChildRepeatedPositivePairWeight
        fixed site₁ site₂ modes) := by
  let massSample : Real × Real → Lattice.PositiveMassConfig N :=
    twoSiteMassConfig fixed site₁ site₂
  have hmass : ∀ site, Measurable fun pair => (massSample pair).mass site :=
    fun site =>
      (continuous_twoSiteMassConfig_mass fixed site₁ site₂ site).measurable
  have hweight : Measurable fun pair =>
      harmonicOrderedNormalizedInteractionWeight
        (massSample pair) (childRepeatedModeTriple modes) :=
    measurable_harmonicOrderedNormalizedInteractionWeight
      massSample hmass (childRepeatedModeTriple modes)
  have hpositive : MeasurableSet {pair : Real × Real |
      IsPositiveOrderedTriple
        (massSample pair) (childRepeatedModeTriple modes)} := by
    rw [show {pair : Real × Real |
        IsPositiveOrderedTriple
          (massSample pair) (childRepeatedModeTriple modes)} =
        ⋂ r, {pair : Real × Real | 0 < orderedModeFrequency
          (harmonicHermitian (massSample pair))
          (childRepeatedModeTriple modes r)} by
      ext pair
      simp [IsPositiveOrderedTriple]]
    exact MeasurableSet.iInter fun r =>
      measurableSet_lt measurable_const
        ((measurable_orderedModeFrequencies_unconditional
          (fun pair => harmonicHermitian (massSample pair))
          (by
            apply Measurable.subtype_mk
            exact
              MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
                massSample hmass)).eval)
  unfold actualTwoMassChildRepeatedPositivePairWeight
  exact Measurable.ite hpositive
    (ENNReal.measurable_ofReal.comp hweight) measurable_const

/-- Conditional reduced parent/child law for one mode pair and one frozen
environment. -/
def actualTwoMassChildRepeatedConditionalPairMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (modes : ChildRepeatedModePair N)
    (weight : Real × Real → ENNReal) : Measure (Real × Real) :=
  Measure.map
    (actualTwoMassChildFrequencyChart
      fixed site₁ site₂ modes.1 modes.2)
    (iidMassPairLaw.withDensity weight)

/-- Exact `1 / N` sum of all conditional child-repeated pair laws. -/
def actualTwoMassChildRepeatedConditionalPerSiteMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (weight : ChildRepeatedModePair N → Real × Real → ENNReal) :
    Measure (Real × Real) :=
  (N : ENNReal)⁻¹ •
    ∑ modes : ChildRepeatedModePair N,
      actualTwoMassChildRepeatedConditionalPairMeasure
        fixed site₁ site₂ modes (weight modes)

/-- Exact regular coefficient after canonical per-site normalization. -/
def actualTwoMassChildRepeatedRegularPerSiteBudget
    {N : Nat} [NeZero N]
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (detLower : ChildRepeatedModePair N → Real) : ENNReal :=
  (N : ENNReal)⁻¹ *
    ∑ modes : ChildRepeatedModePair N,
      weightCeiling modes * 9 *
        (ENNReal.ofReal (detLower modes))⁻¹

/-- Exact weighted exceptional contribution after summing all parent/child
mode pairs and applying the canonical per-site scaling. -/
def actualTwoMassChildRepeatedBadPerSiteBudget
    {N : Nat} [NeZero N]
    (weight : ChildRepeatedModePair N → Real × Real → ENNReal)
    (good : ChildRepeatedModePair N → Set (Real × Real)) : ENNReal :=
  (N : ENNReal)⁻¹ *
    ∑ modes : ChildRepeatedModePair N,
      (iidMassPairLaw.withDensity (weight modes)) (good modes)ᶜ

/-- Summing the one-pair estimates preserves the exact reciprocal-Jacobian
and bad-patch budgets. -/
theorem actualTwoMassChildRepeatedConditionalPerSite_resonanceStrip_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₁ site₂ : Lattice.Site N)
    (weight : ChildRepeatedModePair N → Real × Real → ENNReal)
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (hweight : ∀ modes, ∀ᵐ point ∂iidMassPairLaw,
      weight modes point ≤ weightCeiling modes)
    (good : ChildRepeatedModePair N → Set (Real × Real))
    (hgood : ∀ modes, MeasurableSet (good modes))
    (hderivative : ∀ modes point, point ∈ good modes →
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ modes.1 modes.2)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point)
        (good modes) point)
    (hinjective : ∀ modes, InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2) (good modes))
    (detLower : ChildRepeatedModePair N → Real)
    (hdetLower : ∀ modes, 0 < detLower modes)
    (hdet : ∀ modes point, point ∈ good modes →
      detLower modes ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point).det|)
    {delta : Real} (hdelta : 0 ≤ delta) :
    actualTwoMassChildRepeatedConditionalPerSiteMeasure
        fixed site₁ site₂ weight
        (childRepeatedReducedResonanceStrip delta) ≤
      actualTwoMassChildRepeatedRegularPerSiteBudget
          weightCeiling detLower *
        ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
      actualTwoMassChildRepeatedBadPerSiteBudget weight good := by
  unfold actualTwoMassChildRepeatedConditionalPerSiteMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply]
  have hlocal : ∀ modes : ChildRepeatedModePair N,
      actualTwoMassChildRepeatedConditionalPairMeasure
          fixed site₁ site₂ modes (weight modes)
          (childRepeatedReducedResonanceStrip delta) ≤
        (weightCeiling modes * 9 *
            (ENNReal.ofReal (detLower modes))⁻¹) *
            ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
          (iidMassPairLaw.withDensity (weight modes)) (good modes)ᶜ := by
    intro modes
    exact
      actualTwoMass_boundedDensity_childRepeatedResonanceStrip_apply_le
        fixed hfixed site₁ site₂ modes.1 modes.2
        (weight modes) (weightCeiling modes) (hweight modes)
        (hgood modes) (hderivative modes) (hinjective modes)
        (hdetLower modes) (hdet modes) hdelta
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          actualTwoMassChildRepeatedConditionalPairMeasure
            fixed site₁ site₂ modes (weight modes)
            (childRepeatedReducedResonanceStrip delta) ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          ((weightCeiling modes * 9 *
              (ENNReal.ofReal (detLower modes))⁻¹) *
              ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
            (iidMassPairLaw.withDensity (weight modes)) (good modes)ᶜ) :=
      mul_le_mul_right
        (Finset.sum_le_sum fun modes _ => hlocal modes) _
    _ = actualTwoMassChildRepeatedRegularPerSiteBudget
          weightCeiling detLower *
          ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
        actualTwoMassChildRepeatedBadPerSiteBudget weight good := by
      unfold actualTwoMassChildRepeatedRegularPerSiteBudget
        actualTwoMassChildRepeatedBadPerSiteBudget
      rw [Finset.sum_add_distrib, mul_add, ← Finset.sum_mul]
      ac_rfl

/-- Uniform bounds on the two exact budgets give a finite-volume linear
small-ball estimate with an explicit exceptional error. -/
theorem actualTwoMassChildRepeatedConditionalPerSite_resonanceStrip_apply_le_of_budgets
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₁ site₂ : Lattice.Site N)
    (weight : ChildRepeatedModePair N → Real × Real → ENNReal)
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (hweight : ∀ modes, ∀ᵐ point ∂iidMassPairLaw,
      weight modes point ≤ weightCeiling modes)
    (good : ChildRepeatedModePair N → Set (Real × Real))
    (hgood : ∀ modes, MeasurableSet (good modes))
    (hderivative : ∀ modes point, point ∈ good modes →
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ modes.1 modes.2)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point)
        (good modes) point)
    (hinjective : ∀ modes, InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ modes.1 modes.2) (good modes))
    (detLower : ChildRepeatedModePair N → Real)
    (hdetLower : ∀ modes, 0 < detLower modes)
    (hdet : ∀ modes point, point ∈ good modes →
      detLower modes ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point).det|)
    (regularCeiling badCeiling : ENNReal)
    (hregular : actualTwoMassChildRepeatedRegularPerSiteBudget
      weightCeiling detLower ≤ regularCeiling)
    (hbad : actualTwoMassChildRepeatedBadPerSiteBudget
      weight good ≤ badCeiling)
    {delta : Real} (hdelta : 0 ≤ delta) :
    actualTwoMassChildRepeatedConditionalPerSiteMeasure
        fixed site₁ site₂ weight
        (childRepeatedReducedResonanceStrip delta) ≤
      regularCeiling * ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
        badCeiling := by
  calc
    _ ≤ actualTwoMassChildRepeatedRegularPerSiteBudget
          weightCeiling detLower *
          ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
        actualTwoMassChildRepeatedBadPerSiteBudget weight good :=
      actualTwoMassChildRepeatedConditionalPerSite_resonanceStrip_apply_le
        fixed hfixed site₁ site₂ weight weightCeiling hweight good hgood
        hderivative hinjective detLower hdetLower hdet hdelta
    _ ≤ regularCeiling * ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
          badCeiling :=
      add_le_add
        (mul_le_mul_left hregular
          (ENNReal.ofReal (2 * Real.sqrt 5 * delta))) hbad

/-- The scalar mismatch pushforward evaluates the absolute mismatch window
as exactly the reduced resonance strip. -/
theorem map_childRepeatedDecayMismatch_apply_absoluteMismatchSublevel
    (measure : Measure (Real × Real)) (delta : Real) :
    Measure.map childRepeatedDecayMismatch measure
        (absoluteMismatchSublevel delta) =
      measure (childRepeatedReducedResonanceStrip delta) := by
  rw [Measure.map_apply measurable_childRepeatedDecayMismatch
    (measurableSet_absoluteMismatchSublevel delta)]
  rfl

end

end ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
