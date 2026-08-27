import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassTopV1

open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteValueFibresSampledLensOwnerClusterTopV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1

noncomputable section

universe u v w

/-!
# ENNReal-mass top for nested local-code / common-value selections

The cardinality top in `FiniteNestedValueFibresThirdStageAtScalesV1` is
appropriate for counting raw survivors.  The actual `E2` chain instead
starts from a measure which is partitioned among outer common-`C` values.
This module supplies the same honest two-level aggregation directly for an
arbitrary `ENNReal` mass.  It does not identify code fibres with curve
fibres and does not count the same shading piece once per local code.
-/

/-! ## One outer value -/

/-- A local weighted estimate, the third-stage mass estimate, and a uniform
cap on the finally selected weights give the exact
`B_local * B_third * selected.card * cap` mass bound. -/
theorem mass_le_local_mul_third_mul_selectedCard_mul_cap
    {candidate : Type u} [DecidableEq candidate]
    (sourceMass : ENNReal) (vertices : Finset candidate)
    (comparable : candidate -> candidate -> Prop)
    (weight : candidate -> ENNReal)
    (localPacking thirdPacking cap : ENNReal)
    (Q : FiniteThirdStageGreedyOutcome vertices comparable weight
      thirdPacking)
    (hlocal : sourceMass <=
      localPacking * ∑ a ∈ vertices, weight a)
    (hcap : forall a, a ∈ Q.selected -> weight a <= cap) :
    sourceMass <=
      localPacking * thirdPacking * (Q.selected.card : ENNReal) * cap := by
  have hselectedMass : (∑ a ∈ Q.selected, weight a) <=
      (Q.selected.card : ENNReal) * cap := by
    calc
      (∑ a ∈ Q.selected, weight a) <= ∑ _a ∈ Q.selected, cap := by
        exact Finset.sum_le_sum fun a ha => hcap a ha
      _ = (Q.selected.card : ENNReal) * cap := by
        simp [nsmul_eq_mul]
  calc
    sourceMass <= localPacking * ∑ a ∈ vertices, weight a := hlocal
    _ <= localPacking *
        (thirdPacking * ∑ a ∈ Q.selected, weight a) := by
      gcongr
      exact Q.mass_le
    _ <= localPacking *
        (thirdPacking * ((Q.selected.card : ENNReal) * cap)) := by
      gcongr
    _ = localPacking * thirdPacking *
        (Q.selected.card : ENNReal) * cap := by
      ac_rfl

/-! ## Finite outer-value aggregation -/

/-- Before applying sampled lenses, an `ENNReal` mass which is covered by
the outer value masses is controlled by the total third-stage selected
cardinality.  The hypothesis is an inequality, so it applies both to exact
first-hit partitions and to a merely dominating outer cover. -/
theorem mass_le_local_mul_third_mul_sum_selectedCard_mul_cap
    {value : Type v} {candidate : Type u}
    [DecidableEq candidate]
    (totalMass : ENNReal) (values : Finset value)
    (massAt : value -> ENNReal)
    (vertices : value -> Finset candidate)
    (comparable : value -> candidate -> candidate -> Prop)
    (weight : value -> candidate -> ENNReal)
    (localPacking thirdPacking cap : ENNReal)
    (Q : forall c, FiniteThirdStageGreedyOutcome (vertices c)
      (comparable c) (weight c) thirdPacking)
    (hpartition : totalMass <= ∑ c ∈ values, massAt c)
    (hlocal : forall c, c ∈ values ->
      massAt c <= localPacking * ∑ a ∈ vertices c, weight c a)
    (hcap : forall c, c ∈ values -> forall a, a ∈ (Q c).selected ->
      weight c a <= cap) :
    totalMass <= localPacking * thirdPacking *
      (∑ c ∈ values, ((Q c).selected.card : ENNReal)) * cap := by
  let selectedMass : value -> ENNReal := fun c =>
    ∑ a ∈ (Q c).selected, weight c a
  have hfibre : forall c, c ∈ values ->
      massAt c <= (localPacking * thirdPacking) * selectedMass c := by
    intro c hc
    calc
      massAt c <= localPacking * ∑ a ∈ vertices c, weight c a :=
        hlocal c hc
      _ <= localPacking *
          (thirdPacking * ∑ a ∈ (Q c).selected, weight c a) := by
        gcongr
        exact (Q c).mass_le
      _ = (localPacking * thirdPacking) * selectedMass c := by
        simp only [selectedMass]
        ac_rfl
  have hselectedCap : forall c, c ∈ values ->
      selectedMass c <= ((Q c).selected.card : ENNReal) * cap := by
    intro c hc
    calc
      selectedMass c <= ∑ _a ∈ (Q c).selected, cap := by
        exact Finset.sum_le_sum fun a ha => hcap c hc a ha
      _ = ((Q c).selected.card : ENNReal) * cap := by
        simp [nsmul_eq_mul]
  calc
    totalMass <= ∑ c ∈ values, massAt c := hpartition
    _ <= ∑ c ∈ values,
        (localPacking * thirdPacking) * selectedMass c := by
      exact Finset.sum_le_sum fun c hc => hfibre c hc
    _ = (localPacking * thirdPacking) *
        ∑ c ∈ values, selectedMass c := by
      rw [Finset.mul_sum]
    _ <= (localPacking * thirdPacking) *
        ∑ c ∈ values,
          (((Q c).selected.card : ENNReal) * cap) := by
      gcongr with c hc
      exact hselectedCap c hc
    _ = localPacking * thirdPacking *
        (∑ c ∈ values, ((Q c).selected.card : ENNReal)) * cap := by
      rw [← Finset.sum_mul]
      ac_rfl

/-- Final package-free mass top.  Sampled-lens aggregation is performed
only over the outer values whose curve fibres are pairwise disjoint; local
cover-code tags occur solely inside `vertices c`. -/
theorem mass_le_local_mul_third_mul_sampledLensBound_mul_cap
    {value : Type v} {candidate : Type u} {curve : Type w}
    [DecidableEq candidate] [DecidableEq curve]
    (totalMass : ENNReal) (values : Finset value)
    (massAt : value -> ENNReal)
    (vertices : value -> Finset candidate)
    (comparable : value -> candidate -> candidate -> Prop)
    (weight : value -> candidate -> ENNReal)
    (localPacking thirdPacking cap : ENNReal)
    (Q : forall c, FiniteThirdStageGreedyOutcome (vertices c)
      (comparable c) (weight c) thirdPacking)
    (curveFiber : value -> Finset curve) (globalCurves : Finset curve)
    (depth : Real) (hdepth : 0 <= depth)
    (hpartition : totalMass <= ∑ c ∈ values, massAt c)
    (hlocal : forall c, c ∈ values ->
      massAt c <= localPacking * ∑ a ∈ vertices c, weight c a)
    (hcap : forall c, c ∈ values -> forall a, a ∈ (Q c).selected ->
      weight c a <= cap)
    (hcurveDisjoint : (values : Set value).PairwiseDisjoint curveFiber)
    (hcurveSubset : values.biUnion curveFiber ⊆ globalCurves)
    (hselected : forall c, c ∈ values ->
      (((Q c).selected.card : Nat) : Real) <=
        sampledLensBound depth ((curveFiber c).card : Real)) :
    totalMass <= localPacking * thirdPacking *
      ENNReal.ofReal
        (sampledLensBound depth (globalCurves.card : Real)) * cap := by
  have hmassTop : totalMass <= localPacking * thirdPacking *
      (∑ c ∈ values, ((Q c).selected.card : ENNReal)) * cap :=
    mass_le_local_mul_third_mul_sum_selectedCard_mul_cap
      totalMass values massAt vertices comparable weight
      localPacking thirdPacking cap Q hpartition hlocal hcap
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
      (∑ c ∈ values, (((Q c).selected.card : Nat) : Real)) <=
        sampledLensBound depth (globalCurves.card : Real) := by
    calc
      (∑ c ∈ values, (((Q c).selected.card : Nat) : Real)) <=
          ∑ c ∈ values, sampledLensBound depth (n c) := by
        exact Finset.sum_le_sum fun c hc => hselected c hc
      _ <= sampledLensBound depth (globalCurves.card : Real) :=
        sum_sampledLensBound_le_sampledLensBound_total_of_finite_values
          values n depth (globalCurves.card : Real) hdepth hn hcurveSum
  have hselectedENN :
      (∑ c ∈ values, ((Q c).selected.card : ENNReal)) <=
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) := by
    calc
      (∑ c ∈ values, ((Q c).selected.card : ENNReal)) =
          ENNReal.ofReal
            (∑ c ∈ values,
              (((Q c).selected.card : Nat) : Real)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · simp
        · intro c _hc
          exact Nat.cast_nonneg _
      _ <= ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) :=
        ENNReal.ofReal_le_ofReal hselectedReal
  calc
    totalMass <= localPacking * thirdPacking *
        (∑ c ∈ values, ((Q c).selected.card : ENNReal)) * cap :=
      hmassTop
    _ <= localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := by
      gcongr

#print axioms mass_le_local_mul_third_mul_selectedCard_mul_cap
#print axioms mass_le_local_mul_third_mul_sum_selectedCard_mul_cap
#print axioms mass_le_local_mul_third_mul_sampledLensBound_mul_cap

end

end FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassTopV1
