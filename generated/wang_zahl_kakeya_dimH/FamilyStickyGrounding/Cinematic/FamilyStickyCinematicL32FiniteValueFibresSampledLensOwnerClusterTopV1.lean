import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresOwnerClusterAggregationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteValueFibresSampledLensOwnerClusterTopV1

open FamilyStickyCinematicL32FiniteValueFibresOwnerClusterAggregationV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1

noncomputable section

universe u v w

/-!
# Package-free all-fibre sampled-lens / owner-cluster aggregation

This is the algebraic top of the C-normalized route.  Each occupied value
fibre may run its own two-stage selector, with its own owner map and selected
subfamily.  Exact finite partition, the two-stage raw-mass estimate, an
owner-cluster cap, and the sampled-lens endpoint then aggregate without a
loss by the number of occupied values, provided the curve fibres are
disjoint (or an application supplies the corresponding summed curve budget).

No fixed-C, exact-C, sampling-package, or rectangle definition occurs here.
-/

/-- Total owner-cluster mass retained by the selected pivots in one value
fibre. -/
noncomputable def selectedOwnerClusterMass
    {item : Type u} {value : Type v} [DecidableEq item]
    (fiber : value -> Finset item)
    (owner : value -> item -> item)
    (weight : value -> item -> ENNReal)
    (selected : value -> Finset item) (c : value) : ENNReal :=
  ∑ b ∈ selected c,
    ownerClusterMass (fiber c) (owner c) (weight c) b

/-- The precise package-free top after the two-stage selectors have been
chosen.  A uniform cap for every selected owner fibre converts their mass
into the sum of the selected cardinalities. -/
theorem card_le_packing_mul_sum_selectedCard_mul_cap_of_twoStageFibres
    {item : Type u} {value : Type v} [DecidableEq item]
    (items : Finset item) (values : Finset value)
    (fiber : value -> Finset item)
    (packingBound cap : ENNReal)
    (owner : value -> item -> item)
    (weight : value -> item -> ENNReal)
    (selected : value -> Finset item)
    (hpartition : items.card =
      ∑ c ∈ values, (fiber c).card)
    (hraw : forall c, c ∈ values ->
      ((fiber c).card : ENNReal) <= packingBound *
        selectedOwnerClusterMass fiber owner weight selected c)
    (hcap : forall c, c ∈ values -> forall b, b ∈ selected c ->
      ownerClusterMass (fiber c) (owner c) (weight c) b <= cap) :
    (items.card : ENNReal) <=
      packingBound *
        (∑ c ∈ values, ((selected c).card : ENNReal)) * cap := by
  have htotalCap : forall c, c ∈ values ->
      selectedOwnerClusterMass fiber owner weight selected c <=
        ((selected c).card : ENNReal) * cap := by
    intro c hc
    calc
      selectedOwnerClusterMass fiber owner weight selected c <=
          ∑ _b ∈ selected c, cap := by
        exact Finset.sum_le_sum fun b hb => hcap c hc b hb
      _ = ((selected c).card : ENNReal) * cap := by
        simp [nsmul_eq_mul]
  exact card_le_packing_mul_sum_selectedCard_mul_cap_of_fibres
    items values fiber packingBound cap
      (fun c => (selected c).card)
      (selectedOwnerClusterMass fiber owner weight selected)
      hpartition hraw htotalCap

/-- Superadditivity estimate for the `n^(3/2)` term, stated independently
of any exact-C carrier. -/
theorem sum_mul_sqrt_le_total_mul_sqrt_of_finite_values
    {value : Type v} (values : Finset value) (n : value -> Real)
    (N : Real)
    (hn : forall c, c ∈ values -> 0 <= n c)
    (hsum : (∑ c ∈ values, n c) <= N) :
    (∑ c ∈ values, n c * Real.sqrt (n c)) <= N * Real.sqrt N := by
  have hsumNonneg : 0 <= ∑ c ∈ values, n c :=
    Finset.sum_nonneg fun c hc => hn c hc
  have hN : 0 <= N := hsumNonneg.trans hsum
  have hpoint : forall c, c ∈ values ->
      n c * Real.sqrt (n c) <= n c * Real.sqrt N := by
    intro c hc
    have hcnSum : n c <= ∑ d ∈ values, n d :=
      Finset.single_le_sum (fun d hd => hn d hd) hc
    have hcnN : n c <= N := hcnSum.trans hsum
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcnN) (hn c hc)
  calc
    (∑ c ∈ values, n c * Real.sqrt (n c)) <=
        ∑ c ∈ values, n c * Real.sqrt N :=
      Finset.sum_le_sum fun c hc => hpoint c hc
    _ = (∑ c ∈ values, n c) * Real.sqrt N := by
      rw [Finset.sum_mul]
    _ <= N * Real.sqrt N :=
      mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg N)

/-- The sampled-lens bound aggregates over arbitrary finite disjoint curve
fibres.  This is the package-free version of the earlier exact-C numerical
lemma. -/
theorem sum_sampledLensBound_le_sampledLensBound_total_of_finite_values
    {value : Type v} (values : Finset value) (n : value -> Real)
    (depth N : Real)
    (hdepth : 0 <= depth)
    (hn : forall c, c ∈ values -> 0 <= n c)
    (hsum : (∑ c ∈ values, n c) <= N) :
    (∑ c ∈ values, sampledLensBound depth (n c)) <=
      sampledLensBound depth N := by
  have hsumNonneg : 0 <= ∑ c ∈ values, n c :=
    Finset.sum_nonneg fun c hc => hn c hc
  have hN : 0 <= N := hsumNonneg.trans hsum
  have hp := sum_mul_sqrt_le_total_mul_sqrt_of_finite_values
    values n N hn hsum
  have hcoefficient : 0 <= 48 * depth + 315 := by
    nlinarith
  calc
    (∑ c ∈ values, sampledLensBound depth (n c)) =
        (∑ c ∈ values, n c) +
          (48 * depth + 315) *
            ∑ c ∈ values, n c * Real.sqrt (n c) := by
      calc
        (∑ c ∈ values, sampledLensBound depth (n c)) =
            ∑ c ∈ values,
              (n c + (48 * depth + 315) *
                (n c * Real.sqrt (n c))) := by
          apply Finset.sum_congr rfl
          intro c _hc
          unfold sampledLensBound
          ring
        _ = (∑ c ∈ values, n c) +
            ∑ c ∈ values,
              (48 * depth + 315) * (n c * Real.sqrt (n c)) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ c ∈ values, n c) +
            (48 * depth + 315) *
              ∑ c ∈ values, n c * Real.sqrt (n c) := by
          rw [Finset.mul_sum]
    _ <= N + (48 * depth + 315) * (N * Real.sqrt N) :=
      add_le_add hsum (mul_le_mul_of_nonneg_left hp hcoefficient)
    _ = sampledLensBound depth N := by
      unfold sampledLensBound
      ring

/-- Final package-free all-occupied-fibres conclusion.  The disjoint curve
fibres remove the otherwise artificial `values.card` loss. -/
theorem card_le_packing_mul_sampledLensBound_mul_cap_of_twoStageFibres
    {item : Type u} {value : Type v} {curve : Type w}
    [DecidableEq item] [DecidableEq curve]
    (items : Finset item) (values : Finset value)
    (fiber : value -> Finset item)
    (curveFiber : value -> Finset curve) (globalCurves : Finset curve)
    (packingBound cap : ENNReal) (depth : Real)
    (owner : value -> item -> item)
    (weight : value -> item -> ENNReal)
    (selected : value -> Finset item)
    (hdepth : 0 <= depth)
    (hpartition : items.card =
      ∑ c ∈ values, (fiber c).card)
    (hraw : forall c, c ∈ values ->
      ((fiber c).card : ENNReal) <= packingBound *
        selectedOwnerClusterMass fiber owner weight selected c)
    (hcap : forall c, c ∈ values -> forall b, b ∈ selected c ->
      ownerClusterMass (fiber c) (owner c) (weight c) b <= cap)
    (hcurveDisjoint : (values : Set value).PairwiseDisjoint curveFiber)
    (hcurveSubset : values.biUnion curveFiber ⊆ globalCurves)
    (hselected : forall c, c ∈ values ->
      ((selected c).card : Real) <=
        sampledLensBound depth ((curveFiber c).card : Real)) :
    (items.card : ENNReal) <=
      packingBound *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := by
  let n : value -> Real := fun c => ((curveFiber c).card : Real)
  have hcurveSum : (∑ c ∈ values, n c) <=
      (globalCurves.card : Real) := by
    have hunionCard : (values.biUnion curveFiber).card =
        ∑ c ∈ values, (curveFiber c).card :=
      Finset.card_biUnion hcurveDisjoint
    have hcardNat : (values.biUnion curveFiber).card <= globalCurves.card :=
      Finset.card_le_card hcurveSubset
    have hsumNat : ∑ c ∈ values, (curveFiber c).card <=
        globalCurves.card := by
      rw [← hunionCard]
      exact hcardNat
    dsimp only [n]
    exact_mod_cast hsumNat
  have hn : forall c, c ∈ values -> 0 <= n c := by
    intro c _hc
    exact Nat.cast_nonneg _
  have hselectedReal :
      (∑ c ∈ values, ((selected c).card : Real)) <=
        sampledLensBound depth (globalCurves.card : Real) := by
    calc
      (∑ c ∈ values, ((selected c).card : Real)) <=
          ∑ c ∈ values, sampledLensBound depth (n c) := by
        exact Finset.sum_le_sum fun c hc => hselected c hc
      _ <= sampledLensBound depth (globalCurves.card : Real) :=
        sum_sampledLensBound_le_sampledLensBound_total_of_finite_values
          values n depth (globalCurves.card : Real) hdepth hn hcurveSum
  have hselectedENN :
      (∑ c ∈ values, ((selected c).card : ENNReal)) <=
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) := by
    calc
      (∑ c ∈ values, ((selected c).card : ENNReal)) =
          ENNReal.ofReal
            (∑ c ∈ values, ((selected c).card : Real)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · simp
        · intro c _hc
          exact Nat.cast_nonneg _
      _ <= ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) :=
        ENNReal.ofReal_le_ofReal hselectedReal
  calc
    (items.card : ENNReal) <=
        packingBound *
          (∑ c ∈ values, ((selected c).card : ENNReal)) * cap :=
      card_le_packing_mul_sum_selectedCard_mul_cap_of_twoStageFibres
        items values fiber packingBound cap owner weight selected
          hpartition hraw hcap
    _ <= packingBound *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := by
      gcongr

#print axioms selectedOwnerClusterMass
#print axioms card_le_packing_mul_sum_selectedCard_mul_cap_of_twoStageFibres
#print axioms sum_mul_sqrt_le_total_mul_sqrt_of_finite_values
#print axioms sum_sampledLensBound_le_sampledLensBound_total_of_finite_values
#print axioms card_le_packing_mul_sampledLensBound_mul_cap_of_twoStageFibres

end

end FamilyStickyCinematicL32FiniteValueFibresSampledLensOwnerClusterTopV1
