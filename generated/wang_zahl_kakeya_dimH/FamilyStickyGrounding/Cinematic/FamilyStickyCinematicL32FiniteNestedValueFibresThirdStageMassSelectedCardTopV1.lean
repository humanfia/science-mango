import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassTopV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardTopV1

open FamilyStickyCinematicL32FiniteValueFibresSampledLensOwnerClusterTopV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1

noncomputable section

universe u v

/-!
# Outer mass aggregation from per-value selected cardinalities

When occupied local-code sets are represented by subtypes, the third-stage
candidate type genuinely depends on the outer common-`C` value.  Therefore
one must not force all per-`C` outcomes into a single non-dependent
`candidate` type.  This module performs the outer algebra only after each
dependent outcome has been reduced to its selected cardinality.
-/

/-- Sum arbitrary per-value mass estimates which have already passed through
both local and third-stage packing factors. -/
theorem mass_le_local_mul_third_mul_sum_selectedCard_mul_cap_of_values
    {value : Type u}
    (totalMass : ENNReal) (values : Finset value)
    (massAt : value -> ENNReal) (selectedCard : value -> Nat)
    (localPacking thirdPacking cap : ENNReal)
    (hpartition : totalMass <= ∑ c ∈ values, massAt c)
    (hfibre : forall c, c ∈ values ->
      massAt c <= localPacking * thirdPacking *
        (selectedCard c : ENNReal) * cap) :
    totalMass <= localPacking * thirdPacking *
      (∑ c ∈ values, (selectedCard c : ENNReal)) * cap := by
  calc
    totalMass <= ∑ c ∈ values, massAt c := hpartition
    _ <= ∑ c ∈ values,
        localPacking * thirdPacking * (selectedCard c : ENNReal) * cap := by
      exact Finset.sum_le_sum fun c hc => hfibre c hc
    _ = localPacking * thirdPacking *
        (∑ c ∈ values, (selectedCard c : ENNReal)) * cap := by
      rw [← Finset.sum_mul, Finset.mul_sum]

/-- Final outer sampled-lens mass top for genuinely dependent per-value
candidate types.  Only the numerical selected cardinality crosses the outer
value boundary. -/
theorem mass_le_local_mul_third_mul_sampledLensBound_mul_cap_of_selectedCard
    {value : Type u} {curve : Type v} [DecidableEq curve]
    (totalMass : ENNReal) (values : Finset value)
    (massAt : value -> ENNReal) (selectedCard : value -> Nat)
    (localPacking thirdPacking cap : ENNReal)
    (curveFiber : value -> Finset curve) (globalCurves : Finset curve)
    (depth : Real) (hdepth : 0 <= depth)
    (hpartition : totalMass <= ∑ c ∈ values, massAt c)
    (hfibre : forall c, c ∈ values ->
      massAt c <= localPacking * thirdPacking *
        (selectedCard c : ENNReal) * cap)
    (hcurveDisjoint : (values : Set value).PairwiseDisjoint curveFiber)
    (hcurveSubset : values.biUnion curveFiber ⊆ globalCurves)
    (hselected : forall c, c ∈ values ->
      ((selectedCard c : Nat) : Real) <=
        sampledLensBound depth ((curveFiber c).card : Real)) :
    totalMass <= localPacking * thirdPacking *
      ENNReal.ofReal
        (sampledLensBound depth (globalCurves.card : Real)) * cap := by
  have hmassTop : totalMass <= localPacking * thirdPacking *
      (∑ c ∈ values, (selectedCard c : ENNReal)) * cap :=
    mass_le_local_mul_third_mul_sum_selectedCard_mul_cap_of_values
      totalMass values massAt selectedCard localPacking thirdPacking cap
        hpartition hfibre
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
      (∑ c ∈ values, ((selectedCard c : Nat) : Real)) <=
        sampledLensBound depth (globalCurves.card : Real) := by
    calc
      (∑ c ∈ values, ((selectedCard c : Nat) : Real)) <=
          ∑ c ∈ values, sampledLensBound depth (n c) := by
        exact Finset.sum_le_sum fun c hc => hselected c hc
      _ <= sampledLensBound depth (globalCurves.card : Real) :=
        sum_sampledLensBound_le_sampledLensBound_total_of_finite_values
          values n depth (globalCurves.card : Real) hdepth hn hcurveSum
  have hselectedENN :
      (∑ c ∈ values, (selectedCard c : ENNReal)) <=
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) := by
    calc
      (∑ c ∈ values, (selectedCard c : ENNReal)) =
          ENNReal.ofReal
            (∑ c ∈ values, ((selectedCard c : Nat) : Real)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · simp
        · intro c _hc
          exact Nat.cast_nonneg _
      _ <= ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) :=
        ENNReal.ofReal_le_ofReal hselectedReal
  calc
    totalMass <= localPacking * thirdPacking *
        (∑ c ∈ values, (selectedCard c : ENNReal)) * cap := hmassTop
    _ <= localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := by
      gcongr

#print axioms mass_le_local_mul_third_mul_sum_selectedCard_mul_cap_of_values
#print axioms mass_le_local_mul_third_mul_sampledLensBound_mul_cap_of_selectedCard

end

end FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardTopV1
