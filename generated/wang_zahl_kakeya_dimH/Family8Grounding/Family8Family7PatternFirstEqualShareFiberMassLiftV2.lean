import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7PatternFirstEqualShareFiberMassLiftV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u v

/-!
# Equal-share pattern-first mass lifts to one literal weighted tube ball

V1 proved the results but failed only the strict unused-section-variable
linter and is not imported.  This successor keeps the fully universe-generic
statement and disables that cosmetic linter locally.

A finite measurable pairwise-disjoint family of pattern-preserving events is
given a nonempty finite tube fibre.  Each event's area is divided equally
among its fibre occurrences.  A pointwise fibre floor then lifts the weight
selected by any tube ball to the three-dimensional shading mass carried by
exactly that ball.
-/

variable {iota : Type u} [DecidableEq iota]
variable {label : Type v} [DecidableEq label]
variable {F : ConvexFamily iota}

noncomputable def patternFirstEqualShareTubeWeight
    (labels : Finset label) (event : label → Set (Real × Real))
    (fiber : label → Finset iota) (i : iota) : ENNReal :=
  ∑ r ∈ labels,
    if i ∈ fiber r then volume (event r) / ((fiber r).card : ENNReal)
    else 0

theorem fibreFloor_mul_eventVolume_le_restrictedMass
    (Y : Shading F) (f : Real → Real) (hf : Measurable f)
    (i : iota) (event : Set (Real × Real))
    (hevent : MeasurableSet event) (fibreFloor : ENNReal)
    (hfloor : ∀ u, u ∈ event →
      fibreFloor ≤ shadingFiberMass Y f i u) :
    fibreFloor * volume event ≤
      restrictedMass Y (twistedProjection f ⁻¹' event) i := by
  classical
  have hintegral :
      (∫⁻ u in event, shadingFiberMass Y f i u
          ∂(volume : Measure (Real × Real))) =
        restrictedMass Y (twistedProjection f ⁻¹' event) i := by
    calc
      (∫⁻ u in event, shadingFiberMass Y f i u
          ∂(volume : Measure (Real × Real))) =
          ∫⁻ u in event,
            projectedActiveMultiplicity Y ({i} : Finset iota) f u
              ∂(volume : Measure (Real × Real)) := by
        congr 1
        funext u
        rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
          Y ({i} : Finset iota) f hf u]
        simp
      _ = ∑ j ∈ ({i} : Finset iota),
          restrictedMass Y (twistedProjection f ⁻¹' event) j := by
        exact lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
          Y ({i} : Finset iota) f hf event
      _ = restrictedMass Y (twistedProjection f ⁻¹' event) i := by simp
  calc
    fibreFloor * volume event =
        ∫⁻ _u in event, fibreFloor
          ∂(volume : Measure (Real × Real)) := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ u in event, shadingFiberMass Y f i u
        ∂(volume : Measure (Real × Real)) := by
      exact setLIntegral_mono' hevent hfloor
    _ = restrictedMass Y (twistedProjection f ⁻¹' event) i := hintegral

theorem fibreFloor_mul_equalShareWeight_le_ballShadingMass
    (labels : Finset label) (event : label → Set (Real × Real))
    (fiber : label → Finset iota)
    (hfiber : ∀ r, r ∈ labels → (fiber r).Nonempty)
    (hmeasurable : ∀ r, r ∈ labels → MeasurableSet (event r))
    (hdisjoint : Set.PairwiseDisjoint (labels : Set label) event)
    (Y : Shading F) (f : Real → Real) (hf : Measurable f)
    (fibreFloor : ENNReal)
    (hfloor : ∀ r, r ∈ labels → ∀ i, i ∈ fiber r → ∀ u,
      u ∈ event r → fibreFloor ≤ shadingFiberMass Y f i u)
    (ball : Finset iota) :
    fibreFloor *
        (∑ i ∈ ball,
          patternFirstEqualShareTubeWeight labels event fiber i) ≤
      ∑ i ∈ ball, volume (Y.carrier i) := by
  classical
  unfold patternFirstEqualShareTubeWeight
  have hexpand :
      fibreFloor *
          (∑ i ∈ ball, ∑ r ∈ labels,
            if i ∈ fiber r then
              volume (event r) / ((fiber r).card : ENNReal) else 0) =
        ∑ i ∈ ball, ∑ r ∈ labels,
          if i ∈ fiber r then
            fibreFloor *
              (volume (event r) / ((fiber r).card : ENNReal)) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases hir : i ∈ fiber r <;> simp [hir]
  rw [hexpand]
  calc
    (∑ i ∈ ball, ∑ r ∈ labels,
        if i ∈ fiber r then
          fibreFloor *
            (volume (event r) / ((fiber r).card : ENNReal)) else 0) ≤
        ∑ i ∈ ball, ∑ r ∈ labels,
          if i ∈ fiber r then
            restrictedMass Y (twistedProjection f ⁻¹' event r) i else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro r hr
      by_cases hir : i ∈ fiber r
      · simp only [hir, if_true]
        have hcard0 : ((fiber r).card : ENNReal) ≠ 0 := by
          exact_mod_cast Finset.card_ne_zero.mpr (hfiber r hr)
        have hcardTop : ((fiber r).card : ENNReal) ≠ ∞ :=
          ENNReal.natCast_ne_top _
        have hcardOne : (1 : ENNReal) ≤ ((fiber r).card : ENNReal) := by
          exact_mod_cast Finset.one_le_card.mpr (hfiber r hr)
        have hdiv :
            volume (event r) / ((fiber r).card : ENNReal) ≤
              volume (event r) := by
          apply (ENNReal.div_le_iff_le_mul
            (Or.inl hcard0) (Or.inl hcardTop)).2
          calc
            volume (event r) = volume (event r) * 1 := by simp
            _ ≤ volume (event r) * ((fiber r).card : ENNReal) := by
              exact mul_le_mul' le_rfl hcardOne
        exact (mul_le_mul' le_rfl hdiv).trans
          (fibreFloor_mul_eventVolume_le_restrictedMass
            Y f hf i (event r) (hmeasurable r hr) fibreFloor
              (hfloor r hr i hir))
      · simp [hir]
    _ ≤ ∑ i ∈ ball, volume (Y.carrier i) := by
      apply Finset.sum_le_sum
      intro i _hi
      let selected : Finset label := labels.filter fun r => i ∈ fiber r
      let piece : label → Set Space := fun r =>
        Y.carrier i ∩ twistedProjection f ⁻¹' event r
      have hselected : selected ⊆ labels := Finset.filter_subset _ _
      have hpieceMeasurable : ∀ r, r ∈ selected → MeasurableSet (piece r) := by
        intro r hr
        exact (Y.measurable_carrier i).inter
          ((twistedProjection_measurable f hf)
            (hmeasurable r (hselected hr)))
      have hpieceDisjoint : Set.PairwiseDisjoint
          (selected : Set label) piece := by
        intro r hr s hs hrs
        apply Set.disjoint_left.mpr
        intro p hpr hps
        have heventDisjoint := hdisjoint
          (hselected hr) (hselected hs) hrs
        exact Set.disjoint_left.mp heventDisjoint hpr.2 hps.2
      have hmeasure :
          volume (⋃ r ∈ (selected : Set label), piece r) =
            ∑ r ∈ selected, volume (piece r) :=
        measure_biUnion_finset hpieceDisjoint hpieceMeasurable
      calc
        (∑ r ∈ labels,
            if i ∈ fiber r then
              restrictedMass Y (twistedProjection f ⁻¹' event r) i else 0) =
            ∑ r ∈ selected, volume (piece r) := by
          rw [← Finset.sum_filter]
          rfl
        _ = volume (⋃ r ∈ (selected : Set label), piece r) := hmeasure.symm
        _ ≤ volume (Y.carrier i) := by
          apply measure_mono
          intro p hp
          simp only [Set.mem_iUnion] at hp
          obtain ⟨r, _hr, hpr⟩ := hp
          exact hpr.1

#print axioms patternFirstEqualShareTubeWeight
#print axioms fibreFloor_mul_eventVolume_le_restrictedMass
#print axioms fibreFloor_mul_equalShareWeight_le_ballShadingMass

end
end Family8Family7PatternFirstEqualShareFiberMassLiftV2
