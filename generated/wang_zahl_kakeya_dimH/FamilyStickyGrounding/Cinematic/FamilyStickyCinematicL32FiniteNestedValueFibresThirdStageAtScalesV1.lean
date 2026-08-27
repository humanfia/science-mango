import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresOwnerClusterAggregationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresSampledLensOwnerClusterTopV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1

open FamilyStickyCinematicL32FiniteValueFibresOwnerClusterAggregationV1
open FamilyStickyCinematicL32FiniteValueFibresSampledLensOwnerClusterTopV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1

noncomputable section

universe u v w z

/-!
# Honest third-stage aggregation from local cover codes to common-C fibres

The local-cover selector may be run independently in every `(C, code)`
fibre, but those fibres must not be treated as disjoint curve families:
different codes at the same `C` can have the same transformed endpoint.

This module keeps the two levels separate.  Code-local selected pivots are
tagged by their code, then one weighted greedy selection is run on their
union inside a fixed `C` fibre.  Its only non-algebraic input is the literal
closed-neighbour bound for the cross-code comparison graph.  The resulting
family is genuinely pairwise incomparable.  Sampled-lens aggregation is
then performed only over the outer `C` values.
-/

/-! ## Code-tagged local candidates -/

/-- A code tag is retained through the third-stage weighted selection, so
the owner-cluster weight has an unambiguous source even before one proves
that the underlying code fibres are disjoint. -/
abbrev CodeSelectedCandidate (code : Type v) (item : Type u) :=
  Sigma fun _ : code => item

/-- The disjoint tagged union of the locally selected sets. -/
noncomputable def codeSelectedCandidates
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item) :
    Finset (CodeSelectedCandidate code item) :=
  codes.sigma selectedAt

@[simp]
theorem mem_codeSelectedCandidates_iff
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item)
    (q : CodeSelectedCandidate code item) :
    q ∈ codeSelectedCandidates codes selectedAt <->
      q.1 ∈ codes ∧ q.2 ∈ selectedAt q.1 := by
  classical
  simp [codeSelectedCandidates]

/-- The local owner-cluster mass, transported to a code-tagged candidate. -/
def codeSelectedCandidateWeight
    {code : Type v} {item : Type u}
    (weightAt : code -> item -> ENNReal) :
    CodeSelectedCandidate code item -> ENNReal :=
  fun q => weightAt q.1 q.2

/-- Total selected owner mass before the cross-code greedy stage. -/
noncomputable def codeSelectedCandidateMass
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item)
    (weightAt : code -> item -> ENNReal) : ENNReal :=
  ∑ q ∈ codeSelectedCandidates codes selectedAt,
    codeSelectedCandidateWeight weightAt q

theorem codeSelectedCandidateMass_eq_sum
    {code : Type v} {item : Type u}
    (codes : Finset code) (selectedAt : code -> Finset item)
    (weightAt : code -> item -> ENNReal) :
    codeSelectedCandidateMass codes selectedAt weightAt =
      ∑ k ∈ codes, ∑ a ∈ selectedAt k, weightAt k a := by
  classical
  simpa only [codeSelectedCandidateMass, codeSelectedCandidates,
    codeSelectedCandidateWeight] using
      (Finset.sum_sigma codes selectedAt
        (fun q => weightAt q.1 q.2))

/-- Lossless inner partition plus the local two-stage estimates aggregate
to the mass of the code-tagged candidate family. -/
theorem card_le_localPacking_mul_codeSelectedCandidateMass
    {code : Type v} {item : Type u}
    (items : Finset item) (codes : Finset code)
    (fiber : code -> Finset item) (localPacking : ENNReal)
    (selectedAt : code -> Finset item)
    (weightAt : code -> item -> ENNReal)
    (hpartition : items.card =
      ∑ k ∈ codes, (fiber k).card)
    (hlocal : forall k, k ∈ codes ->
      ((fiber k).card : ENNReal) <= localPacking *
        ∑ a ∈ selectedAt k, weightAt k a) :
    (items.card : ENNReal) <= localPacking *
      codeSelectedCandidateMass codes selectedAt weightAt := by
  have hraw := card_le_packing_mul_sum_clusterMass_of_fibres
    items codes fiber localPacking
      (fun k => ∑ a ∈ selectedAt k, weightAt k a)
      hpartition hlocal
  rw [codeSelectedCandidateMass_eq_sum] at ⊢
  exact hraw

/-! ## Generic weighted third-stage greedy selection -/

/-- The literal closed comparison neighbourhood, with classical
decidability kept inside the definition instead of leaked through APIs. -/
noncomputable def finiteClosedComparableNeighbour
    {candidate : Type u} (vertices : Finset candidate)
    (comparable : candidate -> candidate -> Prop) (a : candidate) :
    Finset candidate := by
  classical
  exact vertices.filter fun b => b = a ∨ comparable a b

/-- The complete output of the cross-code greedy stage. -/
structure FiniteThirdStageGreedyOutcome
    {candidate : Type u} [DecidableEq candidate]
    (vertices : Finset candidate)
    (comparable : candidate -> candidate -> Prop)
    (weight : candidate -> ENNReal) (packingBound : ENNReal) where
  selected : Finset candidate
  selected_subset : selected ⊆ vertices
  selected_nonempty : vertices.Nonempty -> selected.Nonempty
  selected_pairwise : Set.Pairwise (selected : Set candidate)
    (fun a b => Not (comparable a b))
  card_le : (vertices.card : ENNReal) <=
    packingBound * (selected.card : ENNReal)
  mass_le : (∑ a ∈ vertices, weight a) <=
    packingBound * ∑ a ∈ selected, weight a

/-- The relation-generic weighted greedy theorem, packaged for later
dependent choice over all occupied common-C values. -/
theorem exists_finiteThirdStageGreedyOutcome
    {candidate : Type u} [DecidableEq candidate]
    (vertices : Finset candidate)
    (comparable : candidate -> candidate -> Prop) [DecidableRel comparable]
    (hsymm : Std.Symm comparable)
    (weight : candidate -> ENNReal) (packingBound : ENNReal)
    (hneighbour : forall a, a ∈ vertices ->
      ((finiteClosedComparableNeighbour vertices comparable a).card : ENNReal) <=
        packingBound) :
    Nonempty (FiniteThirdStageGreedyOutcome vertices comparable weight
      packingBound) := by
  obtain ⟨selected, hsubset, hnonempty, hpairwise, hcard, hmass⟩ :=
    exists_greedy_pairwise_not_relation vertices comparable hsymm weight
      packingBound (by
        intro a ha
        have hEq : (vertices.filter fun b => b = a ∨ comparable a b) =
            finiteClosedComparableNeighbour vertices comparable a := by
          ext b
          simp only [Finset.mem_filter, finiteClosedComparableNeighbour]
        rw [hEq]
        exact hneighbour a ha)
  exact ⟨{
    selected := selected
    selected_subset := hsubset
    selected_nonempty := hnonempty
    selected_pairwise := hpairwise
    card_le := hcard
    mass_le := hmass }⟩

/-- The third-stage outcome specialised to the global two-scale compact-C2
comparison graph of one common-C fibre. -/
abbrev CompactC2AtScalesThirdStageOutcome
    {candidate : Type u} [DecidableEq candidate]
    (vertices : Finset candidate)
    (rectangleAt : candidate -> C2GraphRectangle)
    (domain : Set Real) (globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda : Real)
    (weight : candidate -> ENNReal) (packingBound : ENNReal) :=
  FiniteThirdStageGreedyOutcome vertices
    (compactC2ComparableAtScales rectangleAt domain globalCenter delta
      localScale referenceScale comparisonLambda)
    weight packingBound

/-- Once the honest cross-code closed-neighbour bound is available, the
single common-C AtScales Pairwise family is automatic. -/
theorem exists_compactC2AtScalesThirdStageOutcome_of_closedNeighbourBound
    {candidate : Type u} [DecidableEq candidate]
    (vertices : Finset candidate)
    (rectangleAt : candidate -> C2GraphRectangle)
    (domain : Set Real) (globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda : Real)
    (weight : candidate -> ENNReal) (packingBound : ENNReal)
    (hneighbour : forall a, a ∈ vertices ->
      ((finiteClosedComparableNeighbour vertices
        (compactC2ComparableAtScales rectangleAt domain globalCenter delta
          localScale referenceScale comparisonLambda) a).card : ENNReal) <=
        packingBound) :
    Nonempty (CompactC2AtScalesThirdStageOutcome vertices rectangleAt domain
      globalCenter delta localScale referenceScale comparisonLambda weight
        packingBound) := by
  classical
  exact exists_finiteThirdStageGreedyOutcome vertices
    (compactC2ComparableAtScales rectangleAt domain globalCenter delta
      localScale referenceScale comparisonLambda)
    compactC2ComparableAtScales_symm weight packingBound hneighbour

/-! ## Exact `B_local * B_third` mass algebra -/

/-- One common-C fibre after both the code-local selector and the global
cross-code weighted greedy selector. -/
theorem card_le_local_mul_third_mul_selectedCard_mul_cap
    {candidate : Type u} [DecidableEq candidate]
    {item : Type v}
    (items : Finset item) (vertices : Finset candidate)
    (comparable : candidate -> candidate -> Prop)
    (weight : candidate -> ENNReal)
    (localPacking thirdPacking cap : ENNReal)
    (Q : FiniteThirdStageGreedyOutcome vertices comparable weight
      thirdPacking)
    (hlocal : (items.card : ENNReal) <=
      localPacking * ∑ a ∈ vertices, weight a)
    (hcap : forall a, a ∈ Q.selected -> weight a <= cap) :
    (items.card : ENNReal) <=
      localPacking * thirdPacking * (Q.selected.card : ENNReal) * cap := by
  have hselectedMass : (∑ a ∈ Q.selected, weight a) <=
      (Q.selected.card : ENNReal) * cap := by
    calc
      (∑ a ∈ Q.selected, weight a) <= ∑ _a ∈ Q.selected, cap := by
        exact Finset.sum_le_sum fun a ha => hcap a ha
      _ = (Q.selected.card : ENNReal) * cap := by
        simp [nsmul_eq_mul]
  calc
    (items.card : ENNReal) <=
        localPacking * ∑ a ∈ vertices, weight a := hlocal
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

/-! ## Sampled-lens aggregation only over outer common-C values -/

/-- Final algebraic top for the honest nesting:

* `values` are the outer literal common-C values;
* `vertices c` are all code-tagged local selected pivots inside `c`;
* `Q c` is the single third-stage AtScales selection for that `c`;
* curve disjointness and sampled-lens are required only across `values`.
-/
theorem card_le_local_mul_third_mul_sampledLensBound_mul_cap
    {item : Type u} {value : Type v} {candidate : Type w}
    {curve : Type z}
    [DecidableEq item] [DecidableEq candidate] [DecidableEq curve]
    (items : Finset item) (values : Finset value)
    (fiber : value -> Finset item)
    (vertices : value -> Finset candidate)
    (comparable : value -> candidate -> candidate -> Prop)
    (weight : value -> candidate -> ENNReal)
    (localPacking thirdPacking cap : ENNReal)
    (Q : forall c, FiniteThirdStageGreedyOutcome (vertices c)
      (comparable c) (weight c) thirdPacking)
    (curveFiber : value -> Finset curve) (globalCurves : Finset curve)
    (depth : Real) (hdepth : 0 <= depth)
    (hpartition : items.card =
      ∑ c ∈ values, (fiber c).card)
    (hlocal : forall c, c ∈ values ->
      ((fiber c).card : ENNReal) <=
        localPacking * ∑ a ∈ vertices c, weight c a)
    (hcap : forall c, c ∈ values -> forall a, a ∈ (Q c).selected ->
      weight c a <= cap)
    (hcurveDisjoint : (values : Set value).PairwiseDisjoint curveFiber)
    (hcurveSubset : values.biUnion curveFiber ⊆ globalCurves)
    (hselected : forall c, c ∈ values ->
      (((Q c).selected.card : Nat) : Real) <=
        sampledLensBound depth ((curveFiber c).card : Real)) :
    (items.card : ENNReal) <=
      localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := by
  let selectedMass : value -> ENNReal := fun c =>
    ∑ a ∈ (Q c).selected, weight c a
  have hraw : forall c, c ∈ values ->
      ((fiber c).card : ENNReal) <=
        (localPacking * thirdPacking) * selectedMass c := by
    intro c hc
    calc
      ((fiber c).card : ENNReal) <=
          localPacking * ∑ a ∈ vertices c, weight c a := hlocal c hc
      _ <= localPacking *
          (thirdPacking * ∑ a ∈ (Q c).selected, weight c a) := by
        gcongr
        exact (Q c).mass_le
      _ = (localPacking * thirdPacking) * selectedMass c := by
        simp only [selectedMass]
        ac_rfl
  have hselectedCap : forall c, c ∈ values ->
      selectedMass c <= (((Q c).selected.card : Nat) : ENNReal) * cap := by
    intro c hc
    calc
      selectedMass c <= ∑ _a ∈ (Q c).selected, cap := by
        exact Finset.sum_le_sum fun a ha => hcap c hc a ha
      _ = (((Q c).selected.card : Nat) : ENNReal) * cap := by
        simp [nsmul_eq_mul]
  have hownerTop : (items.card : ENNReal) <=
      (localPacking * thirdPacking) *
        (∑ c ∈ values, (((Q c).selected.card : Nat) : ENNReal)) * cap :=
    card_le_packing_mul_sum_selectedCard_mul_cap_of_fibres
      items values fiber (localPacking * thirdPacking) cap
        (fun c => (Q c).selected.card) selectedMass
        hpartition hraw hselectedCap
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
      (∑ c ∈ values, (((Q c).selected.card : Nat) : ENNReal)) <=
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) := by
    calc
      (∑ c ∈ values, (((Q c).selected.card : Nat) : ENNReal)) =
          ENNReal.ofReal
            (∑ c ∈ values, (((Q c).selected.card : Nat) : Real)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · simp
        · intro c _hc
          exact Nat.cast_nonneg _
      _ <= ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) :=
        ENNReal.ofReal_le_ofReal hselectedReal
  calc
    (items.card : ENNReal) <=
        (localPacking * thirdPacking) *
          (∑ c ∈ values, (((Q c).selected.card : Nat) : ENNReal)) * cap :=
      hownerTop
    _ <= (localPacking * thirdPacking) *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := by
      gcongr
    _ = localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := by
      ac_rfl

#print axioms codeSelectedCandidateMass_eq_sum
#print axioms card_le_localPacking_mul_codeSelectedCandidateMass
#print axioms exists_finiteThirdStageGreedyOutcome
#print axioms exists_compactC2AtScalesThirdStageOutcome_of_closedNeighbourBound
#print axioms card_le_local_mul_third_mul_selectedCard_mul_cap
#print axioms card_le_local_mul_third_mul_sampledLensBound_mul_cap

end

end FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
