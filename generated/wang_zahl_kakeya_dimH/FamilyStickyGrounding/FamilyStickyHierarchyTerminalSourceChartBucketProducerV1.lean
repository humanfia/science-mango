import FamilyStickyGrounding.FamilyStickyHierarchyTerminalSameScaleCoverProducerV1
import FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
import FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
import FamilyStickyCinematicL32FiniteWeightedBucketV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set
open scoped NNReal BigOperators

namespace FamilyStickyHierarchyTerminalSourceChartBucketProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyCinematicL32PyzActualUnitBallVerticalCoefficientCeilingV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyTerminalSameScaleCoverProducerV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# A genuine source chart / graph-c bucket producer for the terminal hierarchy

`TerminalSourceChartBucketGeometry` is a condition on the *whole* original
level-zero refinement.  A chart choice and a finite floor-bucket argument do
not normally preserve that whole refinement: both operations select a
subfamily.  This file keeps the selected indices visible, proves the exact
cardinality and weighted-mass losses, and exposes the only sound bridge back
to the old whole-source structure: an explicit proof that the selection was
the whole source.

The first stage below also records the genuine three-coordinate direction
chart pigeonhole.  It selects some coordinate with loss three.  The current
projected graph coordinates, however, are hard-coded to coordinate `2`; in
the absence of a coordinate-permutation transport for `Tube` and the
hierarchy, only a fixed-`2` source certificate can feed the graph-`c` stage.
-/

universe u

/-! ## The honest three-coordinate chart selection -/

/-- A unit vector in three dimensions has a coordinate of absolute value at
least `1/2`.  The weaker constant `1/2` is convenient for the existing graph
chart and avoids introducing square roots into the finite selection layer. -/
theorem exists_coordinate_abs_half (v : Space) (hv : ‖v‖ = 1) :
    ∃ k : Fin 3, (1 / 2 : Real) ≤ |v k| := by
  by_contra h
  push Not at h
  have h0 := h (0 : Fin 3)
  have h1 := h (1 : Fin 3)
  have h2 := h (2 : Fin 3)
  have h0sq : (v 0) ^ 2 < (1 / 4 : Real) := by
    nlinarith [abs_nonneg (v 0), sq_abs (v 0)]
  have h1sq : (v 1) ^ 2 < (1 / 4 : Real) := by
    nlinarith [abs_nonneg (v 1), sq_abs (v 1)]
  have h2sq : (v 2) ^ 2 < (1 / 4 : Real) := by
    nlinarith [abs_nonneg (v 2), sq_abs (v 2)]
  have hnorm := congrArg (fun x : Real => x ^ 2) hv
  rw [EuclideanSpace.norm_eq] at hnorm
  rw [Real.sq_sqrt (by positivity)] at hnorm
  norm_num [Fin.sum_univ_succ] at hnorm
  change (v 0) ^ 2 + ((v 1) ^ 2 + (v 2) ^ 2) = 1 at hnorm
  nlinarith

/-- Choose one qualifying coordinate for each tube direction.  The choice is
made before the finite pigeonhole, so the resulting fibers form a genuine
partition rather than three overlapping chart filters. -/
noncomputable def preferredDirectionChart
    {radius : NNReal} (T : Tube radius) : Fin 3 :=
  Classical.choose (exists_coordinate_abs_half T.axis.direction
    T.axis.norm_direction)

theorem preferredDirectionChart_abs_half
    {radius : NNReal} (T : Tube radius) :
    (1 / 2 : Real) ≤ |T.axis.direction (preferredDirectionChart T)| :=
  Classical.choose_spec (exists_coordinate_abs_half T.axis.direction
    T.axis.norm_direction)

/-- The literal source fiber assigned to one of the three direction charts. -/
def directionChartFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    (k : Fin 3) : Finset iota :=
  dyadicFiber source (fun i => preferredDirectionChart (fine.tubes i)) k

@[simp]
theorem mem_directionChartFiber_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    (k : Fin 3) (i : iota) :
    i ∈ directionChartFiber fine source k ↔
      i ∈ source ∧ preferredDirectionChart (fine.tubes i) = k := by
  simp [directionChartFiber]

/-- A selected coordinate chart carries the advertised denominator bound in
that coordinate. -/
theorem direction_abs_half_of_mem_directionChartFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    (k : Fin 3) {i : iota} (hi : i ∈ directionChartFiber fine source k) :
    (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction k| := by
  have hk := (mem_directionChartFiber_iff fine source k i).mp hi |>.2
  simpa only [hk] using preferredDirectionChart_abs_half (fine.tubes i)

/-- Finite-label cardinal pigeonholing, stated for the literal fiber used by
the direction chart selection. -/
theorem exists_fintype_card_fiber
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    [Fintype beta] [Nonempty beta]
    (items : Finset alpha) (bucket : alpha → beta)
    (hitems : items.Nonempty) :
    ∃ label : beta,
      (dyadicFiber items bucket label).Nonempty ∧
        items.card ≤ Fintype.card beta *
          (dyadicFiber items bucket label).card := by
  classical
  let fiberCard : beta → Nat := fun label =>
    (dyadicFiber items bucket label).card
  obtain ⟨label, _hlabel, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset beta) fiberCard
      Finset.univ_nonempty
  have hcard : items.card ≤ Fintype.card beta * fiberCard label := by
    calc
      items.card = ∑ b ∈ (Finset.univ : Finset beta), fiberCard b := by
        change items.card = ∑ b ∈ (Finset.univ : Finset beta),
          (items.filter fun i => bucket i = b).card
        exact Finset.card_eq_sum_card_fiberwise
          (fun i hi => Finset.mem_univ (bucket i))
      _ ≤ ∑ _b ∈ (Finset.univ : Finset beta), fiberCard label := by
        apply Finset.sum_le_sum
        intro b hb
        exact hmax b hb
      _ = Fintype.card beta * fiberCard label := by simp
  have hnonempty : (dyadicFiber items bucket label).Nonempty := by
    by_contra hempty
    have hzero : fiberCard label = 0 := by
      simp only [fiberCard, Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hzero, mul_zero] at hcard
    exact hitems.ne_empty (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  exact ⟨label, hnonempty, hcard⟩

/-- Some honest direction chart retains at least one third of the source.
The selected coordinate is data; it is not silently identified with the
project's hard-coded vertical coordinate `2`. -/
theorem exists_directionChart_card_retention
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    (hsource : source.Nonempty) :
    ∃ k : Fin 3,
      (directionChartFiber fine source k).Nonempty ∧
        source.card ≤ 3 * (directionChartFiber fine source k).card ∧
        ∀ i, i ∈ directionChartFiber fine source k →
          (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction k| := by
  obtain ⟨k, hk, hcard⟩ := exists_fintype_card_fiber source
    (fun i => preferredDirectionChart (fine.tubes i)) hsource
  refine ⟨k, hk, ?_, ?_⟩
  · simpa only [directionChartFiber, Fintype.card_fin] using hcard
  · intro i hi
    exact direction_abs_half_of_mem_directionChartFiber fine source k hi
/-- Weighted/density analogue of the three-chart selection.  Its maximizing
bucket is intentionally independent of the cardinal maximizer. -/
theorem exists_directionChart_weight_retention
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (source : Finset iota)
    (weight : iota → NNReal) :
    ∃ k : Fin 3,
      (∑ i ∈ source, weight i) ≤
          3 • ∑ i ∈ directionChartFiber fine source k, weight i ∧
        ∀ i, i ∈ directionChartFiber fine source k →
          (1 / 2 : Real) ≤ |(fine.tubes i).axis.direction k| := by
  obtain ⟨k, hweight⟩ := exists_large_weighted_fiber source
    (fun i => preferredDirectionChart (fine.tubes i)) weight
  refine ⟨k, ?_, ?_⟩
  · simpa only [directionChartFiber, Fintype.card_fin] using hweight
  · intro i hi
    exact direction_abs_half_of_mem_directionChartFiber fine source k hi


/-! ## The level-zero fixed chart and graph-c buckets -/

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- The original level-zero refinement used by every current final-index
type. -/
def levelZeroSource : Finset (Index 0) :=
  (H.family 0).refinement.refined

/-- The literal fixed-coordinate-`2` subfamily of the level-zero source. -/
def levelZeroFixedVerticalChart : Finset (Index 0) :=
  fixedVerticalChartIndices (H.effectiveFamily 0) (levelZeroSource (H := H))

theorem levelZeroFixedVerticalChart_subset_source :
    levelZeroFixedVerticalChart (H := H) ⊆ levelZeroSource (H := H) :=
  fixedVerticalChartIndices_subset_source
    (H.effectiveFamily 0) (levelZeroSource (H := H))

/-- If the upstream source really came from the Wang--Zahl fixed `L_3`
chart, the literal chart filter loses nothing. -/
theorem levelZeroFixedVerticalChart_eq_source_of_vertical_half
    (hvertical : ∀ i, i ∈ levelZeroSource (H := H) →
      (1 / 2 : Real) ≤
        |((H.effectiveFamily 0).tubes i).axis.direction 2|) :
    levelZeroFixedVerticalChart (H := H) = levelZeroSource (H := H) := by
  apply Finset.Subset.antisymm levelZeroFixedVerticalChart_subset_source
  intro i hi
  exact (mem_fixedVerticalChartIndices_iff
    (H.effectiveFamily 0) (levelZeroSource (H := H))).mpr
      ⟨hi, hvertical i hi⟩

/-- A Grounding-local name for the same literal floor bucket used by the PYZ
norm-first chain.  It is repeated here because importing that downstream
module together with the hierarchy currently creates a duplicate root /
`FamilyStickyGrounding` module-name collision. -/
def sourceProjectedTubeCBucket {radius : NNReal}
    (eta : Real) (T : Tube radius) : Int :=
  Int.floor (projectedTubeGraphC T / eta)

/-- Equality of positive-width floor buckets gives a graph-`c` diameter at
most one bucket width. -/
theorem abs_projectedTubeGraphC_sub_le_of_sourceBucket_eq
    {radius : NNReal} {eta : Real} (heta : 0 < eta)
    {T U : Tube radius}
    (hbucket : sourceProjectedTubeCBucket eta T =
      sourceProjectedTubeCBucket eta U) :
    |projectedTubeGraphC T - projectedTubeGraphC U| ≤ eta := by
  have hscaled :
      |projectedTubeGraphC T / eta - projectedTubeGraphC U / eta| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor hbucket
  rw [← sub_div, abs_div, abs_of_pos heta] at hscaled
  exact ((div_lt_one heta).mp hscaled).le

/-- The level-zero graph-`c` bucket at the half-radius mesh. -/
def levelZeroGraphCBucket (i : Index 0) : Int :=
  sourceProjectedTubeCBucket
    (((H.effectiveRadius 0 : NNReal) : Real) / 2)
    ((H.effectiveFamily 0).tubes i)

/-- Labels actually occupied by the fixed vertical chart. -/
def levelZeroOccupiedGraphCBuckets : Finset Int :=
  occupiedWeightBuckets (levelZeroFixedVerticalChart (H := H))
    (levelZeroGraphCBucket (H := H))

/-- The literal selected fixed-chart / graph-`c` bucket fiber. -/
def levelZeroChartBucketFiber (label : Int) : Finset (Index 0) :=
  (levelZeroFixedVerticalChart (H := H)).filter fun i =>
    levelZeroGraphCBucket (H := H) i = label

@[simp]
theorem mem_levelZeroChartBucketFiber_iff
    (label : Int) (i : Index 0) :
    i ∈ levelZeroChartBucketFiber (H := H) label ↔
      i ∈ levelZeroFixedVerticalChart (H := H) ∧
        levelZeroGraphCBucket (H := H) i = label := by
  simp [levelZeroChartBucketFiber]

theorem levelZeroChartBucketFiber_subset_source (label : Int) :
    levelZeroChartBucketFiber (H := H) label ⊆
      levelZeroSource (H := H) := by
  exact Finset.Subset.trans (Finset.filter_subset _ _)
    levelZeroFixedVerticalChart_subset_source

theorem levelZeroChartBucketFiber_nonempty_of_mem_occupied
    {label : Int}
    (hlabel : label ∈ levelZeroOccupiedGraphCBuckets (H := H)) :
    (levelZeroChartBucketFiber (H := H) label).Nonempty := by
  obtain ⟨i, hi, hilabel⟩ :=
    (mem_occupiedWeightBuckets_iff).mp hlabel
  exact ⟨i, (mem_levelZeroChartBucketFiber_iff label i).mpr
    ⟨hi, hilabel⟩⟩

/-! ## A finite explicit graph-c candidate interval -/

/-- All graph-`c` labels compatible with `|c| ≤ 2` and mesh `eta`. -/
def graphCBucketCandidateLabels (eta : Real) : Finset Int :=
  Finset.Icc (Int.floor ((-2 : Real) / eta))
    (Int.floor ((2 : Real) / eta))

/-- The exact number of labels in the explicit interval. -/
def graphCBucketLoss (eta : Real) : Nat :=
  (graphCBucketCandidateLabels eta).card

theorem graphCBucketLoss_eq (eta : Real) :
    graphCBucketLoss eta =
      (Int.floor ((2 : Real) / eta) + 1 -
        Int.floor ((-2 : Real) / eta)).toNat := by
  simp [graphCBucketLoss, graphCBucketCandidateLabels, Int.card_Icc]

theorem sourceProjectedTubeCBucket_mem_candidates_of_vertical_half
    {radius : NNReal} {eta : Real} (heta : 0 < eta)
    {T : Tube radius}
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    sourceProjectedTubeCBucket eta T ∈ graphCBucketCandidateLabels eta := by
  have hc := abs_projectedTubeGraphC_le_two_of_vertical_half hvertical
  have hlower : (-2 : Real) ≤ projectedTubeGraphC T :=
    (abs_le.mp hc).1
  have hupper : projectedTubeGraphC T ≤ (2 : Real) :=
    (abs_le.mp hc).2
  rw [graphCBucketCandidateLabels, Finset.mem_Icc]
  constructor
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right heta).2 hlower)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right heta).2 hupper)

/-- Every actually occupied level-zero label lies in the explicit finite
interval. -/
theorem levelZeroOccupiedGraphCBuckets_subset_candidates
    (hdelta : 0 < H.effectiveRadius 0) :
    levelZeroOccupiedGraphCBuckets (H := H) ⊆
      graphCBucketCandidateLabels
        (((H.effectiveRadius 0 : NNReal) : Real) / 2) := by
  intro label hlabel
  obtain ⟨i, hi, rfl⟩ := (mem_occupiedWeightBuckets_iff).mp hlabel
  have hvertical := vertical_half_of_mem_fixedVerticalChartIndices
    (H.effectiveFamily 0) (levelZeroSource (H := H)) hi
  apply sourceProjectedTubeCBucket_mem_candidates_of_vertical_half
  · exact div_pos (by exact_mod_cast hdelta) (by norm_num)
  · exact hvertical

theorem levelZeroOccupiedGraphCBuckets_card_le_loss
    (hdelta : 0 < H.effectiveRadius 0) :
    (levelZeroOccupiedGraphCBuckets (H := H)).card ≤
      graphCBucketLoss (((H.effectiveRadius 0 : NNReal) : Real) / 2) := by
  exact Finset.card_le_card
    (levelZeroOccupiedGraphCBuckets_subset_candidates (H := H) hdelta)

/-! ## Selected-family geometry and its only whole-source bridge -/

/-- The minimal honest replacement for `TerminalSourceChartBucketGeometry`
after chart/bucket pigeonholing. -/
structure SelectedTerminalSourceChartBucketGeometry where
  selected : Finset (Index 0)
  selected_nonempty : selected.Nonempty
  selected_subset_source : selected ⊆ levelZeroSource (H := H)
  direction_two_ne_zero : ∀ i, i ∈ selected →
    ((H.effectiveFamily 0).tubes i).axis.direction 2 ≠ 0
  graphC_halfBucket : ∀ i, i ∈ selected → ∀ j, j ∈ selected →
    |projectedTubeGraphC ((H.effectiveFamily 0).tubes i) -
      projectedTubeGraphC ((H.effectiveFamily 0).tubes j)| ≤
        ((H.effectiveRadius 0 : NNReal) : Real) / 2

namespace SelectedTerminalSourceChartBucketGeometry

/-- The selected family as a standard occurrence-preserving uniform tube
family.  Its subtype refinement is `univ`; quantitative retention remains
in the producer theorems below. -/
def family (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    UniformTubeFamily (H.effectiveRadius 0) {i // i ∈ S.selected} :=
  (H.effectiveFamily 0).restrictTo S.selected

@[simp]
theorem family_tubes
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (i : {i // i ∈ S.selected}) :
    (S.family).tubes i = (H.effectiveFamily 0).tubes i.1 :=
  rfl

@[simp]
theorem family_refined
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    S.family.refinement.refined = Finset.univ :=
  rfl

theorem family_direction_two_ne_zero
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (i : {i // i ∈ S.selected}) :
    (S.family.tubes i).axis.direction 2 ≠ 0 := by
  simpa using S.direction_two_ne_zero i.1 i.2

theorem family_graphC_halfBucket
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (i j : {i // i ∈ S.selected}) :
    |projectedTubeGraphC (S.family.tubes i) -
      projectedTubeGraphC (S.family.tubes j)| ≤
        ((H.effectiveRadius 0 : NNReal) : Real) / 2 := by
  simpa using S.graphC_halfBucket i.1 i.2 j.1 j.2

/-- A selected-source certificate implies the old whole-source certificate
only when the selected indices are explicitly proved to equal the source. -/
theorem toTerminalSourceChartBucketGeometry
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (hfull : S.selected = levelZeroSource (H := H)) :
    TerminalSourceChartBucketGeometry (H := H) where
  direction_two_ne_zero := by
    intro i hi
    exact S.direction_two_ne_zero i (by simpa only [hfull, levelZeroSource] using hi)
  graphC_halfBucket := by
    intro i hi j hj
    exact S.graphC_halfBucket i (by simpa only [hfull, levelZeroSource] using hi)
      j (by simpa only [hfull, levelZeroSource] using hj)

end SelectedTerminalSourceChartBucketGeometry

/-- Build selected terminal geometry from any actually occupied fixed-chart
bucket. -/
def selectedGeometryOfOccupiedBucket
    (hdelta : 0 < H.effectiveRadius 0) {label : Int}
    (hlabel : label ∈ levelZeroOccupiedGraphCBuckets (H := H)) :
    SelectedTerminalSourceChartBucketGeometry (H := H) where
  selected := levelZeroChartBucketFiber (H := H) label
  selected_nonempty :=
    levelZeroChartBucketFiber_nonempty_of_mem_occupied hlabel
  selected_subset_source := levelZeroChartBucketFiber_subset_source label
  direction_two_ne_zero := by
    intro i hi
    have hchart := (mem_levelZeroChartBucketFiber_iff label i).mp hi |>.1
    have hhalf := vertical_half_of_mem_fixedVerticalChartIndices
      (H.effectiveFamily 0) (levelZeroSource (H := H)) hchart
    intro hzero
    rw [hzero, abs_zero] at hhalf
    norm_num at hhalf
  graphC_halfBucket := by
    intro i hi j hj
    have hiBucket := (mem_levelZeroChartBucketFiber_iff label i).mp hi |>.2
    have hjBucket := (mem_levelZeroChartBucketFiber_iff label j).mp hj |>.2
    apply abs_projectedTubeGraphC_sub_le_of_sourceBucket_eq
    · exact div_pos (by exact_mod_cast hdelta) (by norm_num)
    · exact hiBucket.trans hjBucket.symm

/-! ## Exact cardinal and weighted-density retention -/

/-- Some occupied graph-`c` bucket retains the exact reciprocal of the
number of labels actually occupied by the fixed chart. -/
theorem exists_cardinalRetaining_levelZeroChartBucket
    (hdelta : 0 < H.effectiveRadius 0)
    (hchart : (levelZeroFixedVerticalChart (H := H)).Nonempty) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      (levelZeroFixedVerticalChart (H := H)).card ≤
        (levelZeroOccupiedGraphCBuckets (H := H)).card * S.selected.card ∧
      (levelZeroOccupiedGraphCBuckets (H := H)).card ≤
        graphCBucketLoss (((H.effectiveRadius 0 : NNReal) : Real) / 2) ∧
      (levelZeroFixedVerticalChart (H := H)).card ≤
        graphCBucketLoss (((H.effectiveRadius 0 : NNReal) : Real) / 2) *
          S.selected.card := by
  classical
  let labels := levelZeroOccupiedGraphCBuckets (H := H)
  let fiberCard : Int → Nat := fun label =>
    (levelZeroChartBucketFiber (H := H) label).card
  have hlabels : labels.Nonempty := occupiedWeightBuckets_nonempty hchart
  obtain ⟨label, hlabel, hmax⟩ :=
    Finset.exists_max_image labels fiberCard hlabels
  have hcard : (levelZeroFixedVerticalChart (H := H)).card ≤
      labels.card * fiberCard label := by
    calc
      (levelZeroFixedVerticalChart (H := H)).card =
          ∑ b ∈ labels, fiberCard b := by
        change (levelZeroFixedVerticalChart (H := H)).card =
          ∑ b ∈ labels,
            ((levelZeroFixedVerticalChart (H := H)).filter fun i =>
              levelZeroGraphCBucket (H := H) i = b).card
        exact Finset.card_eq_sum_card_fiberwise (fun i hi => by
          exact (mem_occupiedWeightBuckets_iff).mpr ⟨i, hi, rfl⟩)
      _ ≤ ∑ _b ∈ labels, fiberCard label := by
        apply Finset.sum_le_sum
        intro b hb
        exact hmax b hb
      _ = labels.card * fiberCard label := by simp
  let S := selectedGeometryOfOccupiedBucket (H := H) hdelta hlabel
  have hoccupied := levelZeroOccupiedGraphCBuckets_card_le_loss
    (H := H) hdelta
  refine ⟨S, ?_, hoccupied, ?_⟩
  · simpa [S, selectedGeometryOfOccupiedBucket, labels, fiberCard] using hcard
  · calc
      (levelZeroFixedVerticalChart (H := H)).card ≤
          (levelZeroOccupiedGraphCBuckets (H := H)).card * S.selected.card := by
        simpa [S, selectedGeometryOfOccupiedBucket, labels, fiberCard] using hcard
      _ ≤ graphCBucketLoss
            (((H.effectiveRadius 0 : NNReal) : Real) / 2) * S.selected.card :=
        Nat.mul_le_mul_right S.selected.card hoccupied

/-- If the whole source has genuine fixed-chart provenance, the preceding
producer gives a selected family with a complete two-stage cardinal bound;
the chart loss is exactly one and the only loss is the explicit graph-`c`
bucket count. -/
theorem exists_cardinalRetaining_levelZeroSourceBucket_of_vertical_half
    (hdelta : 0 < H.effectiveRadius 0)
    (hsource : (levelZeroSource (H := H)).Nonempty)
    (hvertical : ∀ i, i ∈ levelZeroSource (H := H) →
      (1 / 2 : Real) ≤
        |((H.effectiveFamily 0).tubes i).axis.direction 2|) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      (levelZeroSource (H := H)).card ≤
        (levelZeroOccupiedGraphCBuckets (H := H)).card * S.selected.card ∧
      (levelZeroSource (H := H)).card ≤
        graphCBucketLoss (((H.effectiveRadius 0 : NNReal) : Real) / 2) *
          S.selected.card := by
  have hchartEq :=
    levelZeroFixedVerticalChart_eq_source_of_vertical_half
      (H := H) hvertical
  have hchart : (levelZeroFixedVerticalChart (H := H)).Nonempty := by
    simpa only [hchartEq] using hsource
  obtain ⟨S, hactual, _hcount, hexplicit⟩ :=
    exists_cardinalRetaining_levelZeroChartBucket (H := H) hdelta hchart
  exact ⟨S, by simpa only [hchartEq] using hactual,
    by simpa only [hchartEq] using hexplicit⟩

/-- Weighted pigeonholing over the actually occupied labels.  This is the
precise density/mass analogue of the cardinal producer; it returns its own
bucket because cardinal mass and a general weight need not have the same
maximizer. -/
theorem exists_weightRetaining_levelZeroChartBucket
    (hdelta : 0 < H.effectiveRadius 0)
    (hchart : (levelZeroFixedVerticalChart (H := H)).Nonempty)
    (weight : Index 0 → NNReal) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      (∑ i ∈ levelZeroFixedVerticalChart (H := H), weight i) ≤
        (levelZeroOccupiedGraphCBuckets (H := H)).card •
          ∑ i ∈ S.selected, weight i ∧
      (∑ i ∈ levelZeroFixedVerticalChart (H := H), weight i) ≤
        graphCBucketLoss (((H.effectiveRadius 0 : NNReal) : Real) / 2) •
          ∑ i ∈ S.selected, weight i := by
  classical
  let labels := levelZeroOccupiedGraphCBuckets (H := H)
  let fiberWeight : Int → NNReal := fun label =>
    ∑ i ∈ levelZeroChartBucketFiber (H := H) label, weight i
  have hlabels : labels.Nonempty := occupiedWeightBuckets_nonempty hchart
  obtain ⟨label, hlabel, hmax⟩ :=
    Finset.exists_max_image labels fiberWeight hlabels
  have hweight : (∑ i ∈ levelZeroFixedVerticalChart (H := H), weight i) ≤
      labels.card • fiberWeight label := by
    calc
      (∑ i ∈ levelZeroFixedVerticalChart (H := H), weight i) =
          ∑ b ∈ labels, fiberWeight b := by
        apply (Finset.sum_fiberwise_of_maps_to
          (s := levelZeroFixedVerticalChart (H := H))
          (t := labels) (g := levelZeroGraphCBucket (H := H))
          (fun i hi =>
            (mem_occupiedWeightBuckets_iff).mpr ⟨i, hi, rfl⟩)
          weight).symm
      _ ≤ labels.card • fiberWeight label :=
        Finset.sum_le_card_nsmul labels fiberWeight (fiberWeight label)
          (fun b hb => hmax b hb)
  let S := selectedGeometryOfOccupiedBucket (H := H) hdelta hlabel
  have hoccupied := levelZeroOccupiedGraphCBuckets_card_le_loss
    (H := H) hdelta
  refine ⟨S, ?_, ?_⟩
  · simpa [S, selectedGeometryOfOccupiedBucket, labels, fiberWeight] using hweight
  · calc
      (∑ i ∈ levelZeroFixedVerticalChart (H := H), weight i) ≤
          (levelZeroOccupiedGraphCBuckets (H := H)).card •
            ∑ i ∈ S.selected, weight i := by
        simpa [S, selectedGeometryOfOccupiedBucket, labels, fiberWeight] using hweight
      _ ≤ graphCBucketLoss
            (((H.effectiveRadius 0 : NNReal) : Real) / 2) •
              ∑ i ∈ S.selected, weight i :=
        nsmul_le_nsmul_left bot_le hoccupied

/-- Fixed-chart provenance again makes the chart loss exactly one for every
nonnegative source weight. -/
theorem exists_weightRetaining_levelZeroSourceBucket_of_vertical_half
    (hdelta : 0 < H.effectiveRadius 0)
    (hsource : (levelZeroSource (H := H)).Nonempty)
    (hvertical : ∀ i, i ∈ levelZeroSource (H := H) →
      (1 / 2 : Real) ≤
        |((H.effectiveFamily 0).tubes i).axis.direction 2|)
    (weight : Index 0 → NNReal) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      (∑ i ∈ levelZeroSource (H := H), weight i) ≤
        (levelZeroOccupiedGraphCBuckets (H := H)).card •
          ∑ i ∈ S.selected, weight i ∧
      (∑ i ∈ levelZeroSource (H := H), weight i) ≤
        graphCBucketLoss (((H.effectiveRadius 0 : NNReal) : Real) / 2) •
          ∑ i ∈ S.selected, weight i := by
  have hchartEq := levelZeroFixedVerticalChart_eq_source_of_vertical_half
    (H := H) hvertical
  have hchart : (levelZeroFixedVerticalChart (H := H)).Nonempty := by
    simpa only [hchartEq] using hsource
  obtain ⟨S, hactual, hexplicit⟩ :=
    exists_weightRetaining_levelZeroChartBucket
      (H := H) hdelta hchart weight
  exact ⟨S, by simpa only [hchartEq] using hactual,
    by simpa only [hchartEq] using hexplicit⟩

/-! ## Sharp finite obstructions to silent promotion -/

/-- A two-point source with two different bucket labels. -/
def twoPointBucketLabel (i : Fin 2) : Bool := i = 1

theorem twoPointBucketLabel_not_constant :
    ¬ ∃ label : Bool, ∀ i : Fin 2, twoPointBucketLabel i = label := by
  rintro ⟨label, hlabel⟩
  have h01 := (hlabel 0).trans (hlabel 1).symm
  norm_num [twoPointBucketLabel] at h01

/-- Every one-bucket refinement of the two-point obstruction is proper. -/
theorem twoPoint_singleBucketFiber_ne_source (label : Bool) :
    dyadicFiber (Finset.univ : Finset (Fin 2))
      twoPointBucketLabel label ≠ Finset.univ := by
  intro hfull
  have hmem0 : (0 : Fin 2) ∈ dyadicFiber (Finset.univ : Finset (Fin 2))
      twoPointBucketLabel label := by rw [hfull]; simp
  have hmem1 : (1 : Fin 2) ∈ dyadicFiber (Finset.univ : Finset (Fin 2))
      twoPointBucketLabel label := by rw [hfull]; simp
  have h0 : twoPointBucketLabel 0 = label :=
    (mem_dyadicFiber _ _ _ _).mp hmem0 |>.2
  have h1 : twoPointBucketLabel 1 = label :=
    (mem_dyadicFiber _ _ _ _).mp hmem1 |>.2
  exact twoPointBucketLabel_not_constant ⟨label, fun i => by
    fin_cases i
    · exact h0
    · exact h1⟩

/-- Thus no API may promote a generic one-bucket selected subfamily to the
whole source without an additional bucket-constancy proof. -/
theorem no_full_singleBucket_refinement_for_twoPointSource :
    ¬ ∃ label : Bool,
      dyadicFiber (Finset.univ : Finset (Fin 2))
        twoPointBucketLabel label = Finset.univ := by
  rintro ⟨label, hfull⟩
  exact twoPoint_singleBucketFiber_ne_source label hfull

#print axioms exists_coordinate_abs_half
#print axioms preferredDirectionChart_abs_half
#print axioms exists_fintype_card_fiber
#print axioms exists_directionChart_card_retention
#print axioms exists_directionChart_weight_retention
#print axioms abs_projectedTubeGraphC_sub_le_of_sourceBucket_eq
#print axioms sourceProjectedTubeCBucket_mem_candidates_of_vertical_half
#print axioms levelZeroOccupiedGraphCBuckets_card_le_loss
#print axioms selectedGeometryOfOccupiedBucket
#print axioms exists_cardinalRetaining_levelZeroChartBucket
#print axioms exists_cardinalRetaining_levelZeroSourceBucket_of_vertical_half
#print axioms exists_weightRetaining_levelZeroChartBucket
#print axioms exists_weightRetaining_levelZeroSourceBucket_of_vertical_half
#print axioms no_full_singleBucket_refinement_for_twoPointSource

end

end FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
