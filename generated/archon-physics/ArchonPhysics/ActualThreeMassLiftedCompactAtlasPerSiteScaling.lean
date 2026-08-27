import ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
import ArchonPhysics.ActualThreeMassLiftedCompactRegularAtlas

/-!
# Per-site scaling of the actual compact three-mass atlas

For every ordered mode triple, a compact subset of the genuine projector
regular source has a finite actual IFT atlas and a positive true-Jacobian
threshold.  This file performs the finite mode sum without replacing those
data by an abstract chart.

The exact regular coefficient retains `atlasCard modes / detLower modes`.
If one knows only a uniform ceiling for each tuple coefficient, cardinality
alone gives an `N^2` per-site loss, and the theorem below proves that exponent
explicitly.  Thus a thermodynamic bound needs additional overlap,
multiplicity, or separable spectral control of the atlas coefficient; compact
extraction at each fixed volume does not provide that scaling by itself.
-/

namespace ArchonPhysics.ActualThreeMassLiftedCompactAtlasPerSiteScaling

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
open ArchonPhysics.ActualThreeMassLiftedCompactRegularAtlas
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Exact regular coefficient after summing a finite actual IFT atlas for
each ordered mode triple and applying the canonical inverse-volume scaling. -/
def actualThreeMassAtlasRegularPerSiteBudget
    {N : Nat} [NeZero N]
    (atlasCard : OrderedModeTriple N → Nat)
    (weightCeiling : OrderedModeTriple N → ENNReal)
    (detLower : OrderedModeTriple N → Real) : ENNReal :=
  (N : ENNReal)⁻¹ *
    ∑ modes : OrderedModeTriple N,
      (atlasCard modes : ENNReal) *
        (weightCeiling modes * 27 *
          (ENNReal.ofReal (detLower modes))⁻¹)

/-- The genuine all-distinct conditional law admits an actual finite atlas
on any modewise family of compact subsets of the true regular source.  Both
the determinant thresholds and atlas cardinalities are chosen from the
actual harmonic frequency chart.  The complement remains the exact
sinc-squared-weighted source, with no ordinary-small-mass relaxation. -/
theorem exists_actualThreeMassAtlasData_conditionalPerSite_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (K : OrderedModeTriple N → Set MassTriple)
    (hKcompact : ∀ modes, IsCompact (K modes))
    (hKregular : ∀ modes, K modes ⊆
      actualThreeMassProjectorRegularSource
        fixed site₀ site₁ site₂ modes)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    ∃ detLower : OrderedModeTriple N → Real,
      ∃ atlasCard : OrderedModeTriple N → Nat,
        (∀ modes, 0 < detLower modes) ∧
        actualThreeMassConditionalPerSiteBroadenedChildMeasure
            fixed site₀ site₁ site₂ sign
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂) T target ≤
          actualThreeMassAtlasRegularPerSiteBudget atlasCard
              (fun _ => ENNReal.ofReal
                (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
              detLower *
              (volume : Measure (Real × Real)) target +
            actualThreeMassWeightedBadPerSiteBudget
              fixed site₀ site₁ site₂ sign
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂) K T := by
  classical
  have hlocal : ∀ modes : OrderedModeTriple N,
      ∃ detLower : Real, ∃ atlasCard : Nat,
        0 < detLower ∧
        actualThreeMassConditionalTupleBroadenedChildMeasure
            fixed site₀ site₁ site₂ sign modes
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes) T target ≤
          ((atlasCard : ENNReal) *
              (ENNReal.ofReal
                  (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) * 27 *
                (ENNReal.ofReal detLower)⁻¹)) *
              (volume : Measure (Real × Real)) target +
            (Measure.map
              (actualThreeMassLiftedFrequencyChart
                fixed site₀ site₁ site₂ sign modes)
              ((iidMassTripleLaw.withDensity
                (actualThreeMassAllDistinctTupleWeight
                  fixed site₀ site₁ site₂ modes)).restrict
                    (K modes)ᶜ)).withDensity
                (liftedResonanceKernelDensity T) univ := by
    intro modes
    exact
      exists_detLower_atlasCard_actualThreeMassLifted_boundedDensity_broadenedChild_apply_le
        fixed h₁₀ h₂₀ h₂₁ sign modes
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂ modes)
        (ENNReal.ofReal
          (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
        (ae_of_all _ fun triple =>
          actualThreeMassAllDistinctTupleWeight_le_acousticCeiling
            fixed hfixed site₀ site₁ site₂ modes triple)
        (K modes) (hKcompact modes) (hKregular modes) hT htarget
  choose detLower atlasCard hdetLower hlocalBound using hlocal
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  unfold actualThreeMassConditionalPerSiteBroadenedChildMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply]
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualThreeMassConditionalTupleBroadenedChildMeasure
            fixed site₀ site₁ site₂ sign modes
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes) T target ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (((atlasCard modes : ENNReal) *
              (ENNReal.ofReal
                  (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) * 27 *
                (ENNReal.ofReal (detLower modes))⁻¹)) *
              (volume : Measure (Real × Real)) target +
            (Measure.map
              (actualThreeMassLiftedFrequencyChart
                fixed site₀ site₁ site₂ sign modes)
              ((iidMassTripleLaw.withDensity
                (actualThreeMassAllDistinctTupleWeight
                  fixed site₀ site₁ site₂ modes)).restrict
                    (K modes)ᶜ)).withDensity
                (liftedResonanceKernelDensity T) univ) := by
        exact mul_le_mul_right
          (Finset.sum_le_sum fun modes _hmodes => hlocalBound modes) _
    _ = actualThreeMassAtlasRegularPerSiteBudget atlasCard
            (fun _ => ENNReal.ofReal
              (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
            detLower *
            (volume : Measure (Real × Real)) target +
          actualThreeMassWeightedBadPerSiteBudget
            fixed site₀ site₁ site₂ sign
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂) K T := by
        unfold actualThreeMassAtlasRegularPerSiteBudget
          actualThreeMassWeightedBadPerSiteBudget
        rw [Finset.sum_add_distrib, mul_add, ← Finset.sum_mul]
        ring

/-- With no information beyond a common ceiling for every tuple's full
atlas/Jacobian/source coefficient, the finite mode count gives an explicit
quadratic per-site loss.  This is the strongest cardinality-only estimate:
the `N^3` ordered tuples are divided by the single canonical factor `N`. -/
theorem actualThreeMassAtlasRegularPerSiteBudget_le_quadratic_of_term_le
    {N : Nat} [NeZero N]
    (atlasCard : OrderedModeTriple N → Nat)
    (weightCeiling : OrderedModeTriple N → ENNReal)
    (detLower : OrderedModeTriple N → Real)
    (termCeiling : ENNReal)
    (hterm : ∀ modes,
      (atlasCard modes : ENNReal) *
          (weightCeiling modes * 27 *
            (ENNReal.ofReal (detLower modes))⁻¹) ≤ termCeiling) :
    actualThreeMassAtlasRegularPerSiteBudget
        atlasCard weightCeiling detLower ≤
      (N : ENNReal) ^ 2 * termCeiling := by
  classical
  unfold actualThreeMassAtlasRegularPerSiteBudget
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (atlasCard modes : ENNReal) *
            (weightCeiling modes * 27 *
              (ENNReal.ofReal (detLower modes))⁻¹) ≤
      (N : ENNReal)⁻¹ *
        ∑ _modes : OrderedModeTriple N, termCeiling := by
          exact mul_le_mul_right
            (Finset.sum_le_sum fun modes _hmodes => hterm modes) _
    _ = (N : ENNReal) ^ 2 * termCeiling := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul,
        card_orderedModeTriple_eq_cube, Nat.cast_pow]
      have hNzero : (N : ENNReal) ≠ 0 := by
        exact_mod_cast NeZero.ne N
      have hNtop : (N : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
      calc
        (N : ENNReal)⁻¹ * ((N : ENNReal) ^ 3 * termCeiling) =
            ((N : ENNReal)⁻¹ * (N : ENNReal)) *
              (N : ENNReal) ^ 2 * termCeiling := by ring
        _ = (N : ENNReal) ^ 2 * termCeiling := by
          rw [ENNReal.inv_mul_cancel hNzero hNtop, one_mul]

end

end ArchonPhysics.ActualThreeMassLiftedCompactAtlasPerSiteScaling
