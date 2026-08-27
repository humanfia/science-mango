import ArchonPhysics.ActualThreeMassLiftedWeightedSourceGoodBad
import ArchonPhysics.RandomMassPositiveCollisionData

/-!
# Per-site aggregation of actual three-mass spectral averaging

The local three-mass coarea estimate must be summed with the genuine
collision weights and the canonical `1 / N` scaling.  Bounding every one of
the `N^3` ordered mode tuples by the same constant would leave an artificial
`N^2` loss.  This module therefore keeps the exact coupling-weighted
reciprocal-Jacobian sum and the exact sinc-squared-weighted bad contribution.

The resulting budget is the model theorem that must be bounded uniformly in
volume.  No tuple-cardinality estimate is inserted.
-/

namespace ArchonPhysics.ActualThreeMassLiftedPerSiteBudget

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ActualThreeMassLiftedWeightedSourceGoodBad
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The genuine positive collision weight of one ordered mode tuple after
the three selected masses are resampled. -/
def actualThreeMassPositiveTupleWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (triple : MassTriple) : ENNReal := by
  classical
  let mass := threeMassSiteConfig fixed site₀ site₁ site₂ triple
  exact if IsPositiveOrderedTriple mass modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight mass modes)
    else 0

theorem measurable_actualThreeMassPositiveTupleWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    Measurable
      (actualThreeMassPositiveTupleWeight fixed site₀ site₁ site₂ modes) := by
  let massSample : MassTriple → Lattice.PositiveMassConfig N :=
    threeMassSiteConfig fixed site₀ site₁ site₂
  have hmass : ∀ site, Measurable fun triple => (massSample triple).mass site :=
    fun site =>
      (continuous_threeMassSiteConfig_mass
        fixed site₀ site₁ site₂ site).measurable
  have hweight : Measurable fun triple =>
      harmonicOrderedNormalizedInteractionWeight (massSample triple) modes :=
    measurable_harmonicOrderedNormalizedInteractionWeight
      massSample hmass modes
  have hpositive : MeasurableSet {triple : MassTriple |
      IsPositiveOrderedTriple (massSample triple) modes} := by
    rw [show {triple : MassTriple |
        IsPositiveOrderedTriple (massSample triple) modes} =
        ⋂ r, {triple : MassTriple | 0 < orderedModeFrequency
          (harmonicHermitian (massSample triple)) (modes r)} by
      ext triple
      simp [IsPositiveOrderedTriple]]
    exact MeasurableSet.iInter fun r =>
      measurableSet_lt measurable_const
        ((measurable_orderedModeFrequencies_unconditional
          (fun triple => harmonicHermitian (massSample triple))
          (by
            apply Measurable.subtype_mk
            exact
              MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
                massSample hmass)).eval)
  unfold actualThreeMassPositiveTupleWeight
  exact Measurable.ite hpositive
    (ENNReal.measurable_ofReal.comp hweight) measurable_const

/-- The broadened planar child law of one ordered tuple, conditionally on a
frozen environment, with an arbitrary nonnegative selected-mass weight. -/
def actualThreeMassConditionalTupleBroadenedChildMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N)
    (weight : MassTriple → ENNReal) (T : Real) : Measure (Real × Real) :=
  Measure.map Prod.fst
    ((Measure.map
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes)
      (iidMassTripleLaw.withDensity weight)).withDensity
        (liftedResonanceKernelDensity T))

/-- The exact `1 / N` sum of conditional tuple laws. -/
def actualThreeMassConditionalPerSiteBroadenedChildMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (weight : OrderedModeTriple N → MassTriple → ENNReal)
    (T : Real) : Measure (Real × Real) :=
  (N : ENNReal)⁻¹ •
    ∑ modes : OrderedModeTriple N,
      actualThreeMassConditionalTupleBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign modes (weight modes) T

/-- Exact regular-part coefficient after the canonical per-site scaling.
This is deliberately a weighted sum rather than `card tuples` times a
worst-case constant. -/
def actualThreeMassRegularPerSiteBudget
    {N : Nat} [NeZero N]
    (weightCeiling : OrderedModeTriple N → ENNReal)
    (detLower : OrderedModeTriple N → Real) : ENNReal :=
  (N : ENNReal)⁻¹ *
    ∑ modes : OrderedModeTriple N,
      weightCeiling modes * 27 *
        (ENNReal.ofReal (detLower modes))⁻¹

/-- Exact sinc-squared-weighted exceptional contribution after summing all
ordered tuples and applying the canonical per-site scaling. -/
def actualThreeMassWeightedBadPerSiteBudget
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (weight : OrderedModeTriple N → MassTriple → ENNReal)
    (good : OrderedModeTriple N → Set MassTriple)
    (T : Real) : ENNReal :=
  (N : ENNReal)⁻¹ *
    ∑ modes : OrderedModeTriple N,
      (Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        ((iidMassTripleLaw.withDensity (weight modes)).restrict
          (good modes)ᶜ)).withDensity
            (liftedResonanceKernelDensity T) Set.univ

/-- Summing the actual one-tuple coarea estimates preserves the exact
coupling/Jacobian budget and the exact kernel-weighted bad budget. -/
theorem actualThreeMassConditionalPerSiteBroadenedChild_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (weight : OrderedModeTriple N → MassTriple → ENNReal)
    (weightCeiling : OrderedModeTriple N → ENNReal)
    (hweight : ∀ modes, ∀ᵐ point ∂iidMassTripleLaw,
      weight modes point ≤ weightCeiling modes)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes))
    (hderivative : ∀ modes point, point ∈ good modes →
      HasFDerivWithinAt
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        (actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point) (good modes) point)
    (hinjective : ∀ modes, InjOn
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) (good modes))
    (detLower : OrderedModeTriple N → Real)
    (hdetLower : ∀ modes, 0 < detLower modes)
    (hdet : ∀ modes point, point ∈ good modes →
      detLower modes ≤
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point).det|)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    actualThreeMassConditionalPerSiteBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign weight T target ≤
      actualThreeMassRegularPerSiteBudget weightCeiling detLower *
          (volume : Measure (Real × Real)) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ sign weight good T := by
  unfold actualThreeMassConditionalPerSiteBroadenedChildMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply]
  have hlocal : ∀ modes : OrderedModeTriple N,
      actualThreeMassConditionalTupleBroadenedChildMeasure
          fixed site₀ site₁ site₂ sign modes (weight modes) T target ≤
        (weightCeiling modes * 27 *
            (ENNReal.ofReal (detLower modes))⁻¹) *
            (volume : Measure (Real × Real)) target +
          (Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            ((iidMassTripleLaw.withDensity (weight modes)).restrict
              (good modes)ᶜ)).withDensity
                (liftedResonanceKernelDensity T) Set.univ := by
    intro modes
    exact actualThreeMassLifted_boundedDensity_broadenedChild_apply_le
      fixed site₀ site₁ site₂ sign modes
      (weight modes) (weightCeiling modes) (hweight modes)
      (hgood modes) (hderivative modes) (hinjective modes)
      (hdetLower modes) (hdet modes) hT htarget
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassConditionalTupleBroadenedChildMeasure
            fixed site₀ site₁ site₂ sign modes (weight modes) T target ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          ((weightCeiling modes * 27 *
              (ENNReal.ofReal (detLower modes))⁻¹) *
              (volume : Measure (Real × Real)) target +
            (Measure.map
              (actualThreeMassLiftedFrequencyChart
                fixed site₀ site₁ site₂ sign modes)
              ((iidMassTripleLaw.withDensity (weight modes)).restrict
                (good modes)ᶜ)).withDensity
                  (liftedResonanceKernelDensity T) Set.univ) :=
      mul_le_mul_right
        (Finset.sum_le_sum fun modes _ => hlocal modes) _
    _ = actualThreeMassRegularPerSiteBudget weightCeiling detLower *
          (volume : Measure (Real × Real)) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ sign weight good T := by
      unfold actualThreeMassRegularPerSiteBudget
        actualThreeMassWeightedBadPerSiteBudget
      rw [Finset.sum_add_distrib, mul_add, ← Finset.sum_mul, mul_assoc]

/-- A uniform bound on the two exact budgets gives the corresponding
finite-volume child-density modulus, with no tuple-cardinality loss. -/
theorem actualThreeMassConditionalPerSiteBroadenedChild_apply_le_of_budgets
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (weight : OrderedModeTriple N → MassTriple → ENNReal)
    (weightCeiling : OrderedModeTriple N → ENNReal)
    (hweight : ∀ modes, ∀ᵐ point ∂iidMassTripleLaw,
      weight modes point ≤ weightCeiling modes)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes))
    (hderivative : ∀ modes point, point ∈ good modes →
      HasFDerivWithinAt
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        (actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point) (good modes) point)
    (hinjective : ∀ modes, InjOn
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) (good modes))
    (detLower : OrderedModeTriple N → Real)
    (hdetLower : ∀ modes, 0 < detLower modes)
    (hdet : ∀ modes point, point ∈ good modes →
      detLower modes ≤
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point).det|)
    {T : Real} (hT : 0 < T)
    (regularCeiling badCeiling : ENNReal)
    (hregular : actualThreeMassRegularPerSiteBudget
      weightCeiling detLower ≤ regularCeiling)
    (hbad : actualThreeMassWeightedBadPerSiteBudget
      fixed site₀ site₁ site₂ sign weight good T ≤ badCeiling)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    actualThreeMassConditionalPerSiteBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign weight T target ≤
      regularCeiling * (volume : Measure (Real × Real)) target +
        badCeiling := by
  calc
    _ ≤ actualThreeMassRegularPerSiteBudget weightCeiling detLower *
          (volume : Measure (Real × Real)) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ sign weight good T :=
      actualThreeMassConditionalPerSiteBroadenedChild_apply_le
        fixed site₀ site₁ site₂ sign weight weightCeiling hweight good hgood
        hderivative hinjective detLower hdetLower hdet hT htarget
    _ ≤ regularCeiling * (volume : Measure (Real × Real)) target +
          badCeiling :=
      add_le_add
        (mul_le_mul_left hregular
          ((volume : Measure (Real × Real)) target)) hbad

end

end ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
