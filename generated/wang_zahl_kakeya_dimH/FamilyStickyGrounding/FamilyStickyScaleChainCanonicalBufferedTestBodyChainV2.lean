import FamilyStickyGrounding.FamilyStickyScaleChainBufferedTelescopeV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy

noncomputable section

/-!
# Canonical buffered test-body chains

This module constructs the algebraic and geometric fields of an actual
`BufferedTestBodyChain` instead of accepting a second chain-shaped
certificate.

* The test body starts at a supplied positive-volume convex body and is
  recursively enlarged by the literal closed `4 * effectiveRadius`
  thickening used by the buffered adjacent theorem.
* At every hierarchy level, the tube normalization is the attained minimum
  of the volumes of the finitely many active effective tubes.
* The dimensional loss is the exact body-volume/tube-volume quotient.  This
  makes the envelope honest and automatic, but supplies no quantitative
  upper bound for that loss; such a bound remains a separate analytic task.

Positive depth forces every active effective level, including the terminal
one, to be nonempty.  Positive effective radii make the finite minimum
strictly positive, while compactness makes it finite.  The genuinely
analytic terminal estimate `top_le_one` remains an explicit input.
-/

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {card : Nat -> Nat}
  (H : MultiscaleTubeHierarchy depth nominalRadius
    (fun l => Fin (card l)))

/-! ## Nonempty active levels and their actual finite tube-volume minima -/

/-- Every effective active level is nonempty when the hierarchy has positive
depth.  A nonterminal level is the fine side of its outgoing partition; a
positive level is the coarse side of its incoming partition. -/
theorem effectiveRefined_nonempty
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) :
    (H.effectiveFamily l).refinement.refined.Nonempty := by
  cases l with
  | zero =>
      let P := H.effectivePartition 0 hdepth
      rw [<- P.fineIndices_eq_refined]
      exact P.fineIndices_nonempty
  | succ l =>
      have hlstep : l < depth := by omega
      let P := H.effectivePartition l hlstep
      rw [<- P.coarseIndices_eq_refined]
      exact P.coarseIndices_nonempty

/-- The subtype indexing the effective active family is inhabited at every
certified level. -/
theorem effectiveActiveIndex_nonempty
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) :
    Nonempty {i // i ∈ (H.effectiveFamily l).refinement.refined} := by
  obtain ⟨i, hi⟩ := effectiveRefined_nonempty H hdepth l hl
  exact ⟨⟨i, hi⟩⟩

/-- Finset form of active-index nonemptiness, used as the proof argument of
the genuine finite infimum. -/
theorem effectiveActiveUniv_nonempty
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) :
    (Finset.univ : Finset {i // i ∈
      (H.effectiveFamily l).refinement.refined}).Nonempty := by
  let i : {i // i ∈ (H.effectiveFamily l).refinement.refined} :=
    Classical.choice (effectiveActiveIndex_nonempty H hdepth l hl)
  exact ⟨i, Finset.mem_univ i⟩

/-- The literal minimum of the volumes of all active effective tubes at one
certified hierarchy level. -/
def activeTubeVolumeFloorAt
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) : ENNReal :=
  (Finset.univ : Finset {i // i ∈
      (H.effectiveFamily l).refinement.refined}).inf'
    (effectiveActiveUniv_nonempty H hdepth l hl)
    (fun i => volume ((H.effectiveFamily l).tubes i.1).carrier)

/-- The finite minimum is a lower bound for every active effective tube. -/
theorem activeTubeVolumeFloorAt_le
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth)
    (i : {i // i ∈ (H.effectiveFamily l).refinement.refined}) :
    activeTubeVolumeFloorAt H hdepth l hl <=
      volume ((H.effectiveFamily l).tubes i.1).carrier := by
  exact Finset.inf'_le
    (fun j : {j // j ∈ (H.effectiveFamily l).refinement.refined} =>
      volume ((H.effectiveFamily l).tubes j.1).carrier)
    (Finset.mem_univ i)

/-- The floor is attained by an actual active effective tube. -/
theorem exists_activeTubeVolume_eq_floorAt
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) :
    ∃ i : {i // i ∈ (H.effectiveFamily l).refinement.refined},
      activeTubeVolumeFloorAt H hdepth l hl =
        volume ((H.effectiveFamily l).tubes i.1).carrier := by
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_mem_eq_inf'
    (effectiveActiveUniv_nonempty H hdepth l hl)
    (fun i => volume ((H.effectiveFamily l).tubes i.1).carrier)
  exact ⟨i, hmin⟩

/-- Positive radius makes the attained active-tube minimum positive. -/
theorem activeTubeVolumeFloorAt_pos
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth)
    (hradius : 0 < H.effectiveRadius l) :
    0 < activeTubeVolumeFloorAt H hdepth l hl := by
  rw [activeTubeVolumeFloorAt, Finset.lt_inf'_iff]
  intro i _hi
  exact Tube.volume_pos ((H.effectiveFamily l).tubes i.1) hradius

/-- The attained active-tube minimum is finite by compactness of one actual
minimizing tube. -/
theorem activeTubeVolumeFloorAt_ne_top
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) :
    activeTubeVolumeFloorAt H hdepth l hl ≠ ∞ := by
  let i : {i // i ∈ (H.effectiveFamily l).refinement.refined} :=
    Classical.choice (effectiveActiveIndex_nonempty H hdepth l hl)
  exact ne_of_lt ((activeTubeVolumeFloorAt_le H hdepth l hl i).trans_lt
    ((H.effectiveFamily l).tubes i.1).volume_lt_top)

/-- Total Nat-indexed normalization used by `BufferedTestBodyChain`.  Beyond
the certified hierarchy range it is set to one; no chain field observes those
values. -/
def canonicalTubeVolume (hdepth : 0 < depth) (l : Nat) : ENNReal :=
  if hl : l <= depth then activeTubeVolumeFloorAt H hdepth l hl else 1

@[simp] theorem canonicalTubeVolume_of_le
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) :
    canonicalTubeVolume H hdepth l =
      activeTubeVolumeFloorAt H hdepth l hl := by
  simp only [canonicalTubeVolume, dif_pos hl]

theorem canonicalTubeVolume_pos
    (hdepth : 0 < depth)
    (effectiveRadius_pos : forall l, l <= depth ->
      0 < H.effectiveRadius l)
    (l : Nat) (hl : l <= depth) :
    0 < canonicalTubeVolume H hdepth l := by
  rw [canonicalTubeVolume_of_le H hdepth l hl]
  exact activeTubeVolumeFloorAt_pos H hdepth l hl
    (effectiveRadius_pos l hl)

theorem canonicalTubeVolume_ne_top
    (hdepth : 0 < depth) (l : Nat) (hl : l <= depth) :
    canonicalTubeVolume H hdepth l ≠ ∞ := by
  rw [canonicalTubeVolume_of_le H hdepth l hl]
  exact activeTubeVolumeFloorAt_ne_top H hdepth l hl

/-! ## Recursive closed-thickening bodies -/

/-- The canonical test-body recursion used by the normalized adjacent
hierarchy theorem. -/
def canonicalTestBody (K : ConvexBody Space) : Nat -> ConvexBody Space
  | 0 => K
  | l + 1 => closedThickeningBody (canonicalTestBody K l)
      (4 * H.effectiveRadius (l + 1))

@[simp] theorem canonicalTestBody_zero (K : ConvexBody Space) :
    canonicalTestBody H K 0 = K :=
  rfl

@[simp] theorem canonicalTestBody_succ (K : ConvexBody Space) (l : Nat) :
    canonicalTestBody H K (l + 1) =
      closedThickeningBody (canonicalTestBody H K l)
        (4 * H.effectiveRadius (l + 1)) :=
  rfl

/-- Every canonical test body contains the initial body. -/
theorem initial_subset_canonicalTestBody (K : ConvexBody Space) (l : Nat) :
    (K : Set Space) ⊆ (canonicalTestBody H K l : Set Space) := by
  induction l with
  | zero => exact Subset.rfl
  | succ l ih =>
      exact ih.trans (subset_closedThickening
        (canonicalTestBody H K l) (4 * H.effectiveRadius (l + 1)))

/-- Positive initial volume propagates through all closed thickenings. -/
theorem canonicalTestBody_volume_pos
    (K : ConvexBody Space) (hK : 0 < volume (K : Set Space)) (l : Nat) :
    0 < volume (canonicalTestBody H K l : Set Space) :=
  hK.trans_le (measure_mono (initial_subset_canonicalTestBody H K l))

/-! ## Exact envelope normalization and the complete producer -/

/-- The exact loss needed to compare a canonical test body with the attained
minimum active-tube volume.  Quantitatively bounding this quotient is not
claimed here. -/
def exactDimensionalLoss
    (hdepth : 0 < depth) (K : ConvexBody Space) (l : Nat) : ENNReal :=
  volume (canonicalTestBody H K l : Set Space) /
    canonicalTubeVolume H hdepth l

/-- On the certified range, the exact loss times the true finite tube floor
is literally the body volume. -/
theorem exactDimensionalLoss_mul_canonicalTubeVolume
    (hdepth : 0 < depth)
    (effectiveRadius_pos : forall l, l <= depth ->
      0 < H.effectiveRadius l)
    (K : ConvexBody Space) (l : Nat) (hl : l <= depth) :
    exactDimensionalLoss H hdepth K l *
        canonicalTubeVolume H hdepth l =
      volume (canonicalTestBody H K l : Set Space) := by
  unfold exactDimensionalLoss
  exact ENNReal.div_mul_cancel
    (canonicalTubeVolume_pos H hdepth effectiveRadius_pos l hl).ne'
    (canonicalTubeVolume_ne_top H hdepth l hl)

/-- The canonical complete `BufferedTestBodyChain`.  Apart from positive
scale/body nondegeneracy, its sole analytic premise is the terminal
concentration bound required by the downstream telescope. -/
def canonicalBufferedTestBodyChain
    (hdepth : 0 < depth)
    (effectiveRadius_pos : forall l, l <= depth ->
      0 < H.effectiveRadius l)
    (K : ConvexBody Space)
    (initialVolume_pos : 0 < volume (K : Set Space))
    (top_le_one :
      concentration (effectiveActiveFamily H depth)
          (canonicalTestBody H K depth) <= 1) :
    BufferedTestBodyChain H where
  testBody := canonicalTestBody H K
  tubeVolume := canonicalTubeVolume H hdepth
  dimensionalLoss := exactDimensionalLoss H hdepth K
  bodyVolume_ne_zero := by
    intro l _hl
    exact (canonicalTestBody_volume_pos H K initialVolume_pos l).ne'
  tubeVolume_ne_zero := by
    intro l hl
    exact (canonicalTubeVolume_pos H hdepth effectiveRadius_pos l hl).ne'
  tubeVolume_ne_top := canonicalTubeVolume_ne_top H hdepth
  loss_mul_tube_ne_zero := by
    intro l hl
    rw [exactDimensionalLoss_mul_canonicalTubeVolume H hdepth
      effectiveRadius_pos K l (Nat.le_of_lt hl)]
    exact (canonicalTestBody_volume_pos H K initialVolume_pos l).ne'
  loss_mul_tube_ne_top := by
    intro l hl
    rw [exactDimensionalLoss_mul_canonicalTubeVolume H hdepth
      effectiveRadius_pos K l (Nat.le_of_lt hl)]
    exact (canonicalTestBody H K l).isCompact.measure_lt_top.ne
  bodyVolume_envelope := by
    intro l hl
    rw [exactDimensionalLoss_mul_canonicalTubeVolume H hdepth
      effectiveRadius_pos K l (Nat.le_of_lt hl)]
  nextTubeFloor := by
    intro l hl k _hk
    rw [canonicalTubeVolume_of_le H hdepth (l + 1)
      (Nat.succ_le_of_lt hl)]
    exact activeTubeVolumeFloorAt_le H hdepth (l + 1)
      (Nat.succ_le_of_lt hl) k
  testBody_succ := by
    intro l _hl
    rfl
  top_le_one := top_le_one

/-- Positive nominal radii are a convenient source of the effective-radius
positivity input; accumulated buffers can only enlarge them. -/
theorem effectiveRadius_pos_of_nominalRadius_pos
    (nominalRadius_pos : forall l, l <= depth -> 0 < nominalRadius l)
    (l : Nat) (hl : l <= depth) :
    0 < H.effectiveRadius l :=
  (nominalRadius_pos l hl).trans_le (H.nominalRadius_le_effectiveRadius l)

/-- Convenience producer phrased using the raw hierarchy's nominal scale
positivity. -/
def canonicalBufferedTestBodyChainOfNominalRadiusPos
    (hdepth : 0 < depth)
    (nominalRadius_pos : forall l, l <= depth -> 0 < nominalRadius l)
    (K : ConvexBody Space)
    (initialVolume_pos : 0 < volume (K : Set Space))
    (top_le_one :
      concentration (effectiveActiveFamily H depth)
          (canonicalTestBody H K depth) <= 1) :
    BufferedTestBodyChain H :=
  canonicalBufferedTestBodyChain H hdepth
    (effectiveRadius_pos_of_nominalRadius_pos H nominalRadius_pos)
    K initialVolume_pos top_le_one

end MultiscaleTubeHierarchy

#print axioms MultiscaleTubeHierarchy.effectiveRefined_nonempty
#print axioms MultiscaleTubeHierarchy.exists_activeTubeVolume_eq_floorAt
#print axioms MultiscaleTubeHierarchy.activeTubeVolumeFloorAt_pos
#print axioms MultiscaleTubeHierarchy.canonicalTestBody_volume_pos
#print axioms MultiscaleTubeHierarchy.exactDimensionalLoss_mul_canonicalTubeVolume
#print axioms MultiscaleTubeHierarchy.canonicalBufferedTestBodyChain
#print axioms MultiscaleTubeHierarchy.canonicalBufferedTestBodyChainOfNominalRadiusPos

end
end FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2
