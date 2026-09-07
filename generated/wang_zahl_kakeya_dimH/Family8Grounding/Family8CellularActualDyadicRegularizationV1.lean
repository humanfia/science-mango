import Family8Grounding.Family8CellularJointFactoringRegularizationV1
import CubeWeightUniformization
import Family8Grounding.Family8ComparableMultiplicityBucketsV1
import Mathlib.Tactic

/-!
# Numeric REG1/R2 for a finite positive cellular edge graph

Unlike the abstract regularization API, this file constructs both labels.
REG1 applies the weighted finite-cube theorem to the finite edge subtype with
`mass = loc = omega.toNNReal` and `K = 1`.  REG2 uses the genuine dyadic
`comparableLabel` of the right degree, hence its final edge set is saturated
over every selected right cell.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal NNReal

namespace Family8CellularActualDyadicRegularizationV1

open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family8ComparableMultiplicityBucketsV1
open Submission.Kakeya.Uniformity
open Family8CellularJointFactoringFiniteCoreV1
open Family8CellularJointFactoringRegularizationV1

noncomputable section

variable {parent cell : Type*}
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]

/-- Edges of a finite source graph, as a finite type suitable for the
weighted-cube theorem. -/
abbrev SourceEdge (source : Finset (parent × cell)) :=
  {e : parent × cell // e ∈ source}

/-- The finite REG1 logarithmic exponent. -/
def weightExponent (source : Finset (parent × cell)) : Nat :=
  cubeExponent (a := SourceEdge source) 1

/-- The explicit REG1 loss from cutoff plus weighted dyadic pigeonholing. -/
def weightLoss (source : Finset (parent × cell)) : Nat :=
  2 * (weightExponent source + 1)

/-- The explicit number of right-degree labels. -/
def degreeLoss : Nat :=
  Nat.log 2 (Fintype.card parent) + 2

/-- Concrete output of numeric REG1 followed by right-saturated numeric REG2. -/
structure ActualDyadicRegularization
    (source : Finset (parent × cell)) (omega : parent × cell -> ENNReal) where
  firstEdges : Finset (parent × cell)
  finalEdges : Finset (parent × cell)
  w : ENNReal
  d : Nat
  w_pos : 0 < w
  d_pos : 0 < d
  first_subset_source : firstEdges ⊆ source
  final_rightSaturated : IsRightSaturatedSubedge firstEdges finalEdges
  first_weightBand : InHalfOpenWeightBand firstEdges omega w
  final_degreeBand : HasRightDegreeBand finalEdges (rightCells finalEdges) d
  sourceWeight_le_first : edgeWeight source omega <=
    weightLoss source • edgeWeight firstEdges omega
  firstWeight_le_final : edgeWeight firstEdges omega <=
    degreeLoss (parent := parent) • edgeWeight finalEdges omega
  sourceWeight_le_final : edgeWeight source omega <=
    (weightLoss source * degreeLoss (parent := parent)) •
      edgeWeight finalEdges omega

namespace ActualDyadicRegularization

theorem final_subset_source
    {source : Finset (parent × cell)} {omega : parent × cell -> ENNReal}
    (R : ActualDyadicRegularization source omega) :
    R.finalEdges ⊆ source :=
  R.final_rightSaturated.1.trans R.first_subset_source

end ActualDyadicRegularization

/-- Every edge weight is bounded by the total source weight. -/
theorem omega_le_edgeWeight
    (source : Finset (parent × cell)) (omega : parent × cell -> ENNReal)
    {e : parent × cell} (he : e ∈ source) :
    omega e <= edgeWeight source omega := by
  unfold edgeWeight
  exact Finset.single_le_sum (fun _ _ => bot_le) he

/-- Numeric two-stage regularization.  The only analytic assumptions are the
ones genuinely needed to pass REG1 through `ENNReal.toNNReal`: every source
edge has positive finite weight. -/
theorem exists_actualDyadicRegularization
    (source : Finset (parent × cell)) (omega : parent × cell -> ENNReal)
    (hsource : source.Nonempty)
    (hpos : ∀ e ∈ source, 0 < omega e)
    (hfinite : ∀ e ∈ source, omega e ≠ ∞) :
    Nonempty (ActualDyadicRegularization source omega) := by
  classical
  let mass : SourceEdge source -> NNReal := fun e => (omega e.1).toNNReal
  have hmass_pos : ∀ e : SourceEdge source, 0 < mass e := by
    intro e
    exact ENNReal.toNNReal_pos (ne_of_gt (hpos e.1 e.2)) (hfinite e.1 e.2)
  have htotal : 0 < ∑ e, mass e := by
    obtain ⟨e, he⟩ := hsource
    let e' : SourceEdge source := ⟨e, he⟩
    exact lt_of_lt_of_le (hmass_pos e')
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ e'))
  have hloc : ∀ e : SourceEdge source, mass e <= ∑ f, mass f := by
    intro e
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ e)
  obtain ⟨n, hn, hselectedMass, hselectedBand⟩ :=
    exists_weightedCubeLevel mass mass 1 (by omega)
      (fun e => by simp) htotal hloc
  let selected : Finset (SourceEdge source) :=
    (highCells mass mass 1).filter fun e =>
      cubeBucket (dominanceCutoff mass 1)
        (cubeExponent (a := SourceEdge source) 1) (mass e) = n
  let first : Finset (parent × cell) :=
    selected.map ⟨Subtype.val, Subtype.val_injective⟩
  let wNN : NNReal :=
    2 ^ n * dominanceCutoff mass 1
  have hwNN : 0 < wNN := by
    have hcard : 0 < Fintype.card (SourceEdge source) := by
      exact Fintype.card_pos_iff.mpr ⟨⟨hsource.choose, hsource.choose_spec⟩⟩
    exact mul_pos (by positivity)
      (div_pos htotal (by simp only [Nat.cast_one]; positivity))
  have hfirstSub : first ⊆ source := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    exact e'.2
  have hfirstBandNN : ∀ e ∈ first,
      wNN <= (omega e).toNNReal ∧ (omega e).toNNReal < 2 * wNN := by
    intro e he
    obtain ⟨e', he', heq⟩ := Finset.mem_map.mp he
    subst e
    have hb := hselectedBand e' he'
    simpa [selected, wNN,
      Submission.Kakeya.ConvexFactoring.CubeWeightUniformization.inDyadicBand,
      mass, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hb
  have hfirstBand : InHalfOpenWeightBand first omega (wNN : ENNReal) := by
    intro e he
    have hf := hfinite e (hfirstSub he)
    constructor
    · rw [← ENNReal.coe_toNNReal hf]
      exact ENNReal.coe_le_coe.mpr (hfirstBandNN e he).1
    · rw [← ENNReal.coe_toNNReal hf]
      simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat] using
        ENNReal.coe_lt_coe.mpr (hfirstBandNN e he).2
  have hsumCoe :
      (↑(∑ e : SourceEdge source, mass e) : ENNReal) =
        edgeWeight source omega := by
    unfold edgeWeight mass
    calc
      (↑(∑ e : SourceEdge source, (omega e.1).toNNReal) : ENNReal) =
          ∑ e : SourceEdge source, ↑(omega e.1).toNNReal := by norm_cast
      _ =
          ∑ e : SourceEdge source, omega e.1 := by
        apply Finset.sum_congr rfl
        intro e he
        exact ENNReal.coe_toNNReal (hfinite e.1 e.2)
      _ = ∑ e ∈ source, omega e := by
        simpa only [Finset.attach_eq_univ] using
          (Finset.sum_attach source fun e => omega e)
  have hselectedCoe :
      (↑(∑ e ∈ selected, mass e) : ENNReal) = edgeWeight first omega := by
    unfold edgeWeight first mass
    calc
      (↑(∑ e ∈ selected, (omega e.1).toNNReal) : ENNReal) =
          ∑ e ∈ selected, ↑(omega e.1).toNNReal := by norm_cast
      _ = ∑ e ∈ selected, omega e.1 := by
        apply Finset.sum_congr rfl
        intro e he
        exact ENNReal.coe_toNNReal (hfinite e.1 e.2)
      _ = ∑ e ∈ selected.map ⟨Subtype.val, Subtype.val_injective⟩, omega e := by
        rw [Finset.sum_map]
        rfl
  have hsourceFirst : edgeWeight source omega <=
      weightLoss source • edgeWeight first omega := by
    rw [← hsumCoe, ← hselectedCoe]
    exact_mod_cast hselectedMass
  let degreeBucket : cell -> Fin (degreeLoss (parent := parent)) := fun q =>
    ⟨comparableLabel (rightDegree first q), by
      have hdeg : rightDegree first q <= Fintype.card parent := by
        unfold rightDegree activeParentsAt
        exact Finset.card_le_univ _
      exact Nat.lt_succ_of_le
        (comparableLabel_le_of_le hdeg)⟩
  let _ : Nonempty (Fin (degreeLoss (parent := parent))) :=
    ⟨⟨0, by unfold degreeLoss; omega⟩⟩
  obtain ⟨b, hb⟩ := exists_large_weighted_fiber_ennreal first
    (fun e => degreeBucket e.2) omega
  let final := dyadicFiber first (fun e => degreeBucket e.2) b
  have hsaturated : IsRightSaturatedSubedge first final := by
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro p q hpq hq
    obtain ⟨p', hp'q⟩ := (mem_rightCells_iff final q).1 hq
    have hlabel : degreeBucket q = b :=
      (mem_dyadicFiber first (fun e => degreeBucket e.2) b (p', q)).1 hp'q |>.2
    exact (mem_dyadicFiber first (fun e => degreeBucket e.2) b (p, q)).2
      ⟨hpq, hlabel⟩
  have hfirstFinal : edgeWeight first omega <=
      degreeLoss (parent := parent) • edgeWeight final omega := by
    simpa only [edgeWeight, Fintype.card_fin, final] using hb
  have hsourceFinal : edgeWeight source omega <=
      (weightLoss source * degreeLoss (parent := parent)) •
        edgeWeight final omega := by
    calc
      edgeWeight source omega <=
          weightLoss source • edgeWeight first omega := hsourceFirst
      _ <= weightLoss source •
          (degreeLoss (parent := parent) • edgeWeight final omega) :=
        nsmul_le_nsmul_right hfirstFinal _
      _ = (weightLoss source * degreeLoss (parent := parent)) •
          edgeWeight final omega := by
        simp only [nsmul_eq_mul, Nat.cast_mul]
        ring
  have hfinalWeightPos : 0 < edgeWeight final omega := by
    have hsourceWeightPos : 0 < edgeWeight source omega := by
      obtain ⟨e, he⟩ := hsource
      exact lt_of_lt_of_le (hpos e he) (omega_le_edgeWeight source omega he)
    by_contra hnot
    have hzero : edgeWeight final omega = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hzero] at hsourceFinal
    simp only [nsmul_zero] at hsourceFinal
    exact (not_le_of_gt hsourceWeightPos) hsourceFinal
  have hfinalNonempty : final.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hfinalWeightPos
    simp [edgeWeight] at hfinalWeightPos
  obtain ⟨e, hefinal⟩ := hfinalNonempty
  have hefirst : e ∈ first := hsaturated.1 hefinal
  have hrightPos : 0 < rightDegree first e.2 := by
    unfold rightDegree activeParentsAt
    exact Finset.card_pos.mpr ⟨e.1, by simp [hefirst]⟩
  have hbLabel : comparableLabel (rightDegree first e.2) = b.1 := by
    have := (mem_dyadicFiber first (fun x => degreeBucket x.2) b e).1 hefinal |>.2
    exact congrArg Fin.val this
  let d := comparableBase b.1
  have hdBand0 := zeroOrComparable_of_comparableLabel_eq hbLabel
  have hdBand : 0 < d ∧ d <= rightDegree first e.2 ∧
      rightDegree first e.2 < 2 * d := by
    rcases hdBand0 with hz | hp
    · omega
    · exact hp
  have hdegreeBand : HasRightDegreeBand final (rightCells final) d := by
    apply hsaturated.hasRightDegreeBand d
    intro q hq
    obtain ⟨p, hpq⟩ := (mem_rightCells_iff final q).1 hq
    have hqLabelFin :=
      (mem_dyadicFiber first (fun x => degreeBucket x.2) b (p, q)).1 hpq |>.2
    have hqLabel : comparableLabel (rightDegree first q) = b.1 :=
      congrArg Fin.val hqLabelFin
    have hcomp := zeroOrComparable_of_comparableLabel_eq hqLabel
    rcases hcomp with hz | hp
    · have hqpos : 0 < rightDegree first q := by
        unfold rightDegree activeParentsAt
        exact Finset.card_pos.mpr ⟨p, by simp [hsaturated.1 hpq]⟩
      omega
    · exact hp.2
  exact ⟨{
    firstEdges := first
    finalEdges := final
    w := wNN
    d := d
    w_pos := by exact_mod_cast hwNN
    d_pos := hdBand.1
    first_subset_source := hfirstSub
    final_rightSaturated := hsaturated
    first_weightBand := hfirstBand
    final_degreeBand := hdegreeBand
    sourceWeight_le_first := hsourceFirst
    firstWeight_le_final := hfirstFinal
    sourceWeight_le_final := hsourceFinal }⟩

#print axioms omega_le_edgeWeight
#print axioms exists_actualDyadicRegularization

end
end Family8CellularActualDyadicRegularizationV1
