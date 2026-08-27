import ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget

/-!
# Joint all-mode coarea overlap for the actual three-mass chart

A tuplewise IFT atlas cannot be made volume-uniform merely by summing its
cardinalities: different mode charts generally have different mass preimages
of the same frequency target.  The correct non-tuple object is the single
lifted measure obtained by summing all genuine collision-weighted actual
chart pushforwards before applying the resonance kernel.

This file constructs that measure, proves its exact good/bad decomposition,
and identifies the minimal missing thermodynamic coarea statement as one
concrete measure domination.  Such a joint domination, together with the
spectral trace estimate for the off-resonance bad sector, gives an `N`-uniform
broadened child bound.  No joint domination is asserted without proof; the
remaining model obligation is exposed as `actualThreeMassAllDistinctJointGoodCoareaBound`.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.LocalCollisionDensityTransfer
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- `withDensity` commutes with a finite family sum of source measures. -/
theorem withDensity_fintype_sum
    {Alpha Index : Type*} [MeasurableSpace Alpha] [Fintype Index]
    (source : Index → Measure Alpha) (density : Alpha → ENNReal) :
    (∑ index, source index).withDensity density =
      ∑ index, (source index).withDensity density := by
  rw [← Measure.sum_fintype source, withDensity_sum,
    Measure.sum_fintype]

/-- The full genuine all-distinct lifted pushforward, summed over mode
triples before applying the resonance kernel. -/
def actualThreeMassAllDistinctJointLiftedMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) : Measure MassTriple :=
  (N : ENNReal)⁻¹ •
    ∑ modes : OrderedModeTriple N,
      Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes))

/-- Joint actual lifted pushforward restricted to the modewise good source
before the finite mode sum. -/
def actualThreeMassAllDistinctJointGoodLiftedMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple) : Measure MassTriple :=
  (N : ENNReal)⁻¹ •
    ∑ modes : OrderedModeTriple N,
      Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        ((iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes)).restrict (good modes))

/-- Joint actual lifted pushforward of the exact modewise complement. -/
def actualThreeMassAllDistinctJointBadLiftedMeasure
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple) : Measure MassTriple :=
  (N : ENNReal)⁻¹ •
    ∑ modes : OrderedModeTriple N,
      Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        ((iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes)).restrict (good modes)ᶜ)

/-- The concrete missing joint coarea/overlap estimate.  Its constant already
includes the canonical inverse-volume normalization and the complete mode
sum; hence an `N`-independent `C` is exactly the thermodynamic scaling needed
from the good sector. -/
def actualThreeMassAllDistinctJointGoodCoareaBound
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple)
    (C : ENNReal) : Prop :=
  actualThreeMassAllDistinctJointGoodLiftedMeasure
      fixed site₀ site₁ site₂ sign good ≤
    C • (volume : Measure MassTriple)

/-- The full joint source is exactly the sum of its good and bad actual
lifted pushforwards. -/
theorem actualThreeMassAllDistinctJointLiftedMeasure_eq_good_add_bad
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes)) :
    actualThreeMassAllDistinctJointLiftedMeasure
        fixed site₀ site₁ site₂ sign =
      actualThreeMassAllDistinctJointGoodLiftedMeasure
          fixed site₀ site₁ site₂ sign good +
        actualThreeMassAllDistinctJointBadLiftedMeasure
          fixed site₀ site₁ site₂ sign good := by
  classical
  unfold actualThreeMassAllDistinctJointLiftedMeasure
    actualThreeMassAllDistinctJointGoodLiftedMeasure
    actualThreeMassAllDistinctJointBadLiftedMeasure
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  let source := iidMassTripleLaw.withDensity
    (actualThreeMassAllDistinctTupleWeight
      fixed site₀ site₁ site₂ modes)
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  change Measure.map chart source =
    Measure.map chart (source.restrict (good modes)) +
      Measure.map chart (source.restrict (good modes)ᶜ)
  rw [← Measure.map_add _ _ hchart,
    source.restrict_add_restrict_compl (hgood modes)]

/-- Applying the resonance density to the joint lifted measure and forgetting
mismatch is exactly the pre-existing conditional per-site broadened child
measure. -/
theorem actualThreeMassConditionalPerSiteBroadenedChildMeasure_eq_joint
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) (T : Real) :
    actualThreeMassConditionalPerSiteBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂) T =
      Measure.map Prod.fst
        ((actualThreeMassAllDistinctJointLiftedMeasure
          fixed site₀ site₁ site₂ sign).withDensity
            (liftedResonanceKernelDensity T)) := by
  classical
  unfold actualThreeMassConditionalPerSiteBroadenedChildMeasure
    actualThreeMassConditionalTupleBroadenedChildMeasure
    actualThreeMassAllDistinctJointLiftedMeasure
  rw [withDensity_smul_measure, Measure.map_smul,
    withDensity_fintype_sum,
    Measure.map_finset_sum' measurable_fst.aemeasurable]

/-- The exact sinc-squared bad budget is the kernel-weighted mass of the
single joint bad lifted measure. -/
theorem actualThreeMassAllDistinctJointBad_withDensity_univ_eq_budget
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple) (T : Real) :
    (actualThreeMassAllDistinctJointBadLiftedMeasure
        fixed site₀ site₁ site₂ sign good).withDensity
          (liftedResonanceKernelDensity T) univ =
      actualThreeMassWeightedBadPerSiteBudget
        fixed site₀ site₁ site₂ sign
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂) good T := by
  classical
  unfold actualThreeMassAllDistinctJointBadLiftedMeasure
    actualThreeMassWeightedBadPerSiteBudget
  rw [withDensity_smul_measure, withDensity_fintype_sum,
    Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]

/-- A single joint coarea domination gives the desired summed good bound;
the only remainder is the exact sinc-squared-weighted joint bad sector. -/
theorem actualThreeMassConditionalPerSiteBroadenedChild_apply_le_of_jointCoarea
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes))
    (C : ENNReal)
    (hjoint : actualThreeMassAllDistinctJointGoodCoareaBound
      fixed site₀ site₁ site₂ sign good C)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    actualThreeMassConditionalPerSiteBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂) T target ≤
      C * (volume : Measure (Real × Real)) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ sign
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂) good T := by
  rw [actualThreeMassConditionalPerSiteBroadenedChildMeasure_eq_joint,
    actualThreeMassAllDistinctJointLiftedMeasure_eq_good_add_bad
      fixed site₀ site₁ site₂ sign good hgood]
  have hbound := map_fst_withDensity_good_add_bad_apply_le
    (actualThreeMassAllDistinctJointGoodLiftedMeasure
      fixed site₀ site₁ site₂ sign good)
    (actualThreeMassAllDistinctJointBadLiftedMeasure
      fixed site₀ site₁ site₂ sign good)
    hT C hjoint htarget
  rw [actualThreeMassAllDistinctJointBad_withDensity_univ_eq_budget]
    at hbound
  exact hbound

/-- Joint good coarea plus a uniform source-side mismatch gap on the actual
bad charts yields a fully explicit `N`-uniform good/off-resonance estimate. -/
theorem actualThreeMassConditionalPerSiteBroadenedChild_apply_le_of_jointCoarea_offGap
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (good : OrderedModeTriple N → Set MassTriple)
    (hgood : ∀ modes, MeasurableSet (good modes))
    (C : ENNReal)
    (hjoint : actualThreeMassAllDistinctJointGoodCoareaBound
      fixed site₀ site₁ site₂ sign good C)
    {eta T : Real} (heta : 0 < eta) (hT : 0 < T)
    (hgap : ∀ modes point, point ∈ (good modes)ᶜ →
      eta ≤ |(actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes point).2|)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    actualThreeMassConditionalPerSiteBroadenedChildMeasure
        fixed site₀ site₁ site₂ sign
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂) T target ≤
      C * (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) *
          actualThreeMassSpectralPerSiteWeightCeiling := by
  calc
    _ ≤ C * (volume : Measure (Real × Real)) target +
        actualThreeMassWeightedBadPerSiteBudget
          fixed site₀ site₁ site₂ sign
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂) good T :=
      actualThreeMassConditionalPerSiteBroadenedChild_apply_le_of_jointCoarea
        fixed site₀ site₁ site₂ sign good hgood C hjoint hT htarget
    _ ≤ C * (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) *
          actualThreeMassSpectralPerSiteWeightCeiling :=
      add_le_add_right
        (actualThreeMassAllDistinctWeightedBadPerSiteBudget_le_offGap_spectral
          fixed hfixed site₀ site₁ site₂ sign good hgood heta hT hgap) _

end

end ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
