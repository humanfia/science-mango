import ArchonPhysics.ActualTwoMassChildRepeatedCompactAtlasGoodBad
import ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget

/-!
# Per-site child-repeated bounds from finite compact atlases

The local inverse-function theorem produces a finite atlas on every compact
regular set.  This module chooses those atlases simultaneously over the
finite parent/child mode pairs and retains their exact cardinalities in the
canonical `1 / N` budget.
-/

namespace ArchonPhysics.ActualTwoMassChildRepeatedCompactAtlasPerSiteBudget

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedCompactAtlasGoodBad
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassChildRepeatedResonanceStripBound
open ArchonPhysics.ActualTwoMassCountableSpectralAtlas
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Exact regular coefficient of a finite compact atlas after the canonical
per-site normalization.  No cardinality estimate is hidden. -/
def actualTwoMassChildRepeatedCompactAtlasRegularPerSiteBudget
    {N : Nat} [NeZero N]
    (atlasCard : ChildRepeatedModePair N → Nat)
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (detLower : ChildRepeatedModePair N → Real) : ENNReal :=
  (N : ENNReal)⁻¹ *
    ∑ modes : ChildRepeatedModePair N,
      (atlasCard modes : ENNReal) *
        (weightCeiling modes * 9 *
          (ENNReal.ofReal (detLower modes))⁻¹)

/-- There are exactly `N²` ordered parent/child mode pairs at volume `N`. -/
theorem card_childRepeatedModePair_eq_square
    (N : Nat) [NeZero N] :
    Fintype.card (ChildRepeatedModePair N) = N ^ 2 := by
  simp [ChildRepeatedModePair, OrderedModeIndex, Lattice.Site, pow_two]

/-- Cardinality-only control leaves a linear-in-volume loss: the `N²` mode
pairs are divided by only the canonical factor `N`.  Any thermodynamic bound
therefore needs a summed spectral estimate, overlap control, or a compensating
modewise scale; fixed-volume compact extraction alone is insufficient. -/
theorem actualTwoMassChildRepeatedCompactAtlasRegularPerSiteBudget_le_linear_of_term_le
    {N : Nat} [NeZero N]
    (atlasCard : ChildRepeatedModePair N → Nat)
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (detLower : ChildRepeatedModePair N → Real)
    (termCeiling : ENNReal)
    (hterm : ∀ modes,
      (atlasCard modes : ENNReal) *
          (weightCeiling modes * 9 *
            (ENNReal.ofReal (detLower modes))⁻¹) ≤ termCeiling) :
    actualTwoMassChildRepeatedCompactAtlasRegularPerSiteBudget
        atlasCard weightCeiling detLower ≤
      (N : ENNReal) * termCeiling := by
  classical
  unfold actualTwoMassChildRepeatedCompactAtlasRegularPerSiteBudget
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          (atlasCard modes : ENNReal) *
            (weightCeiling modes * 9 *
              (ENNReal.ofReal (detLower modes))⁻¹) ≤
      (N : ENNReal)⁻¹ *
        ∑ _modes : ChildRepeatedModePair N, termCeiling := by
      exact mul_le_mul_right
        (Finset.sum_le_sum fun modes _hmodes ↦ hterm modes) _
    _ = (N : ENNReal) * termCeiling := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul,
        card_childRepeatedModePair_eq_square, Nat.cast_pow]
      have hNzero : (N : ENNReal) ≠ 0 := by
        exact_mod_cast NeZero.ne N
      have hNtop : (N : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
      calc
        (N : ENNReal)⁻¹ * ((N : ENNReal) ^ 2 * termCeiling) =
            ((N : ENNReal)⁻¹ * (N : ENNReal)) *
              (N : ENNReal) * termCeiling := by ring
        _ = (N : ENNReal) * termCeiling := by
          rw [ENNReal.inv_mul_cancel hNzero hNtop, one_mul]

/-- Compact regular sets automatically have simultaneous finite atlases for
all parent/child mode pairs.  Their exact atlas-cardinality budget gives the
linear resonance-strip estimate, while the complement is retained exactly. -/
theorem exists_atlasCard_actualTwoMassChildRepeatedConditionalPerSite_resonanceStrip_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (weight : ChildRepeatedModePair N → Real × Real → ENNReal)
    (weightCeiling : ChildRepeatedModePair N → ENNReal)
    (hweight : ∀ modes, ∀ᵐ point ∂iidMassPairLaw,
      weight modes point ≤ weightCeiling modes)
    (K : ChildRepeatedModePair N → Set (Real × Real))
    (hK : ∀ modes, IsCompact (K modes))
    (hKregular : ∀ modes, K modes ⊆ actualTwoMassRegularSource
      fixed site₁ site₂ modes.1 modes.2)
    (detLower : ChildRepeatedModePair N → Real)
    (hdetLower : ∀ modes, 0 < detLower modes)
    (hdet : ∀ modes point, point ∈ K modes →
      detLower modes ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ modes.1 modes.2 point).det|) :
    ∃ atlasCard : ChildRepeatedModePair N → Nat,
      ∀ {delta : Real}, 0 ≤ delta →
        actualTwoMassChildRepeatedConditionalPerSiteMeasure
            fixed site₁ site₂ weight
            (childRepeatedReducedResonanceStrip delta) ≤
          actualTwoMassChildRepeatedCompactAtlasRegularPerSiteBudget
              atlasCard weightCeiling detLower *
              ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
            actualTwoMassChildRepeatedBadPerSiteBudget weight K := by
  classical
  have hlocalExists : ∀ modes : ChildRepeatedModePair N,
      ∃ atlasCard : Nat, ∀ {target : Set (Real × Real)},
        MeasurableSet target →
          actualTwoMassChildRepeatedConditionalPairMeasure
              fixed site₁ site₂ modes (weight modes) target ≤
            ((atlasCard : ENNReal) *
                (weightCeiling modes * 9 *
                  (ENNReal.ofReal (detLower modes))⁻¹)) *
                (volume : Measure (Real × Real)) target +
              (iidMassPairLaw.withDensity (weight modes)) (K modes)ᶜ := by
    intro modes
    exact exists_atlasCard_actualTwoMass_boundedDensity_frequencyPair_apply_le
      fixed hsite modes.1 modes.2 (weight modes) (weightCeiling modes)
      (hweight modes) (K modes) (hK modes) (hKregular modes)
      (hdetLower modes) (hdet modes)
  choose atlasCard hlocal using hlocalExists
  refine ⟨atlasCard, ?_⟩
  intro delta hdelta
  unfold actualTwoMassChildRepeatedConditionalPerSiteMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply]
  have hmode : ∀ modes : ChildRepeatedModePair N,
      actualTwoMassChildRepeatedConditionalPairMeasure
          fixed site₁ site₂ modes (weight modes)
          (childRepeatedReducedResonanceStrip delta) ≤
        ((atlasCard modes : ENNReal) *
            (weightCeiling modes * 9 *
              (ENNReal.ofReal (detLower modes))⁻¹)) *
              ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
          (iidMassPairLaw.withDensity (weight modes)) (K modes)ᶜ := by
    intro modes
    let target := childRepeatedReducedResonanceStrip delta ∩
      childRepeatedFrequencySquare (Real.sqrt 5)
    have htarget : MeasurableSet target :=
      (childRepeatedReducedResonanceStrip_isClosed delta).measurableSet.inter
        (childRepeatedFrequencySquare_isClosed (Real.sqrt 5)).measurableSet
    unfold actualTwoMassChildRepeatedConditionalPairMeasure
    rw [map_actualTwoMassChildFrequencyChart_resonanceStrip_eq_inter_square
      fixed hfixed site₁ site₂ modes.1 modes.2
      (iidMassPairLaw.withDensity (weight modes)) delta]
    calc
      Measure.map
          (actualTwoMassChildFrequencyChart
            fixed site₁ site₂ modes.1 modes.2)
          (iidMassPairLaw.withDensity (weight modes)) target ≤
        ((atlasCard modes : ENNReal) *
            (weightCeiling modes * 9 *
              (ENNReal.ofReal (detLower modes))⁻¹)) *
              (volume : Measure (Real × Real)) target +
          (iidMassPairLaw.withDensity (weight modes)) (K modes)ᶜ :=
        hlocal modes htarget
      _ ≤ ((atlasCard modes : ENNReal) *
            (weightCeiling modes * 9 *
              (ENNReal.ofReal (detLower modes))⁻¹)) *
              ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
          (iidMassPairLaw.withDensity (weight modes)) (K modes)ᶜ := by
        gcongr
        exact
          volume_childRepeatedReducedResonanceStrip_inter_frequencySquare_le
            (Real.sqrt_nonneg 5) hdelta
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          actualTwoMassChildRepeatedConditionalPairMeasure
            fixed site₁ site₂ modes (weight modes)
            (childRepeatedReducedResonanceStrip delta) ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : ChildRepeatedModePair N,
          (((atlasCard modes : ENNReal) *
              (weightCeiling modes * 9 *
                (ENNReal.ofReal (detLower modes))⁻¹)) *
                ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
            (iidMassPairLaw.withDensity (weight modes)) (K modes)ᶜ) :=
      mul_le_mul_right (Finset.sum_le_sum fun modes _ ↦ hmode modes) _
    _ = actualTwoMassChildRepeatedCompactAtlasRegularPerSiteBudget
          atlasCard weightCeiling detLower *
            ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
        actualTwoMassChildRepeatedBadPerSiteBudget weight K := by
      unfold actualTwoMassChildRepeatedCompactAtlasRegularPerSiteBudget
        actualTwoMassChildRepeatedBadPerSiteBudget
      rw [Finset.sum_add_distrib, mul_add, ← Finset.sum_mul]
      ac_rfl

end

end ArchonPhysics.ActualTwoMassChildRepeatedCompactAtlasPerSiteBudget
