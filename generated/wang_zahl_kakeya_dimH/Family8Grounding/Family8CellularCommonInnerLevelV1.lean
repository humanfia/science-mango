import Family8Grounding.Family8ComparableMultiplicityBucketsV1

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family8CellularCommonInnerLevelV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
open Family8ComparableMultiplicityBucketsV1

noncomputable section

local instance family8CellularCommonInnerPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {child parent : Type*} [Fintype child] [Fintype parent]
  {F : ConvexFamily child}

/-!
# The common inner multiplicity level (repair J1)

The statistic below counts, at a point `x`, precisely the shaded children
having a prescribed parent.  Restricting every child by the dyadic label of
the statistic at its parent makes the decision depend only on `(parent, x)`.
Consequently all incidences above that pair are retained or deleted together.
This is the whole-incidence feature needed before cellular edge
regularization; no child-by-child thinning occurs here.
-/

/-- Number of shaded children over one parent at one point. -/
def parentLocalFiberMultiplicity (Y : Shading F) (parentOf : child → parent)
    (p : parent) (x : Space) : Nat := by
  classical
  exact (Finset.univ.filter fun i ↦ parentOf i = p ∧ x ∈ Y.carrier i).card

theorem parentLocalFiberMultiplicity_cast_eq_sum_indicator
    (Y : Shading F) (parentOf : child → parent) (p : parent) (x : Space) :
    (parentLocalFiberMultiplicity Y parentOf p x : ℝ≥0∞) =
      ∑ i, if parentOf i = p then
        (Y.carrier i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x else 0 := by
  classical
  rw [show parentLocalFiberMultiplicity Y parentOf p x =
      ∑ i, if parentOf i = p ∧ x ∈ Y.carrier i then 1 else 0 by
    simp [parentLocalFiberMultiplicity]]
  push_cast
  simp only [Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hip : parentOf i = p <;>
    by_cases hxi : x ∈ Y.carrier i <;> simp [hip, hxi]

theorem measurable_parentLocalFiberMultiplicity_cast
    (Y : Shading F) (parentOf : child → parent) (p : parent) :
    Measurable fun x ↦
      (parentLocalFiberMultiplicity Y parentOf p x : ℝ≥0∞) := by
  simp_rw [parentLocalFiberMultiplicity_cast_eq_sum_indicator Y parentOf p]
  apply Finset.measurable_fun_sum
  intro i hi
  by_cases hip : parentOf i = p
  · simp only [hip, if_true]
    exact measurable_const.indicator (Y.measurable_carrier i)
  · simp only [hip, if_false]
    exact measurable_const

theorem measurableSet_parentLocalFiberMultiplicity_eq
    (Y : Shading F) (parentOf : child → parent) (p : parent) (n : Nat) :
    MeasurableSet {x | parentLocalFiberMultiplicity Y parentOf p x = n} := by
  have heq :
      {x | parentLocalFiberMultiplicity Y parentOf p x = n} =
        (fun x ↦ (parentLocalFiberMultiplicity Y parentOf p x : ℝ≥0∞)) ⁻¹'
          {(n : ℝ≥0∞)} := by
    ext x
    simp
  rw [heq]
  exact (measurable_parentLocalFiberMultiplicity_cast Y parentOf p)
    (measurableSet_singleton _)

theorem parentLocalFiberMultiplicity_le_card
    (Y : Shading F) (parentOf : child → parent) (p : parent) (x : Space) :
    parentLocalFiberMultiplicity Y parentOf p x ≤ Fintype.card child := by
  classical
  unfold parentLocalFiberMultiplicity
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The parent-local statistic attached to a child.  It is constant among
children with the same parent. -/
def parentLocalPointStatistic (Y : Shading F) (parentOf : child → parent)
    (i : child) (x : Space) : Nat :=
  parentLocalFiberMultiplicity Y parentOf (parentOf i) x

theorem measurableSet_parentLocalPointStatistic_eq
    (Y : Shading F) (parentOf : child → parent) (i : child) (n : Nat) :
    MeasurableSet {x | parentLocalPointStatistic Y parentOf i x = n} :=
  measurableSet_parentLocalFiberMultiplicity_eq Y parentOf (parentOf i) n

/-- J1 restriction at one common dyadic inner label. -/
def commonInnerRestriction (Y : Shading F) (parentOf : child → parent)
    (b : Nat) : Shading F :=
  restrictComparableCarrierStatisticBucket Y
    (parentLocalPointStatistic Y parentOf)
    (measurableSet_parentLocalPointStatistic_eq Y parentOf) b

@[simp] theorem mem_commonInnerRestriction_carrier_iff
    (Y : Shading F) (parentOf : child → parent) (b : Nat)
    (i : child) (x : Space) :
    x ∈ (commonInnerRestriction Y parentOf b).carrier i ↔
      x ∈ Y.carrier i ∧
        comparableLabel
          (parentLocalFiberMultiplicity Y parentOf (parentOf i) x) = b := by
  rfl

/-- Whole-incidence retention: for two original incidences over the same
`(parent, x)`, J1 either retains both or deletes both. -/
theorem commonInnerRestriction_wholeIncidence
    (Y : Shading F) (parentOf : child → parent) (b : Nat)
    {i j : child} {x : Space} (hparent : parentOf i = parentOf j)
    (hxi : x ∈ Y.carrier i) (hxj : x ∈ Y.carrier j) :
    x ∈ (commonInnerRestriction Y parentOf b).carrier i ↔
      x ∈ (commonInnerRestriction Y parentOf b).carrier j := by
  simp only [mem_commonInnerRestriction_carrier_iff, hxi, hxj, true_and]
  rw [hparent]

/-- At every retained incidence, recomputing multiplicity after restriction
does not lose any sibling incidence: the entire parent-point fiber survived. -/
theorem parentLocalFiberMultiplicity_commonInnerRestriction_eq
    (Y : Shading F) (parentOf : child → parent) (b : Nat)
    (i : child) (x : Space)
    (hx : x ∈ (commonInnerRestriction Y parentOf b).carrier i) :
    parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
        parentOf (parentOf i) x =
      parentLocalFiberMultiplicity Y parentOf (parentOf i) x := by
  classical
  unfold parentLocalFiberMultiplicity
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hparent, hxj⟩
    exact ⟨hparent, (mem_commonInnerRestriction_carrier_iff
      Y parentOf b j x).1 hxj |>.1⟩
  · rintro ⟨hparent, hxj⟩
    refine ⟨hparent, (mem_commonInnerRestriction_carrier_iff
      Y parentOf b j x).2 ⟨hxj, ?_⟩⟩
    have hlabel :
        comparableLabel
          (parentLocalFiberMultiplicity Y parentOf (parentOf i) x) = b :=
      (mem_commonInnerRestriction_carrier_iff Y parentOf b i x).1 hx |>.2
    simpa [hparent] using hlabel

theorem recomputed_parentLocalFiberMultiplicity_zeroOrComparable
    (Y : Shading F) (parentOf : child → parent) (b : Nat)
    (i : child) (x : Space)
    (hx : x ∈ (commonInnerRestriction Y parentOf b).carrier i) :
    ZeroOrComparable (comparableBase b)
      (parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
        parentOf (parentOf i) x) := by
  rw [parentLocalFiberMultiplicity_commonInnerRestriction_eq
    Y parentOf b i x hx]
  apply zeroOrComparable_of_comparableLabel_eq
  exact (mem_commonInnerRestriction_carrier_iff Y parentOf b i x).1 hx |>.2

theorem recomputed_parentLocalFiberMultiplicity_pos
    (Y : Shading F) (parentOf : child → parent) (b : Nat)
    (i : child) (x : Space)
    (hx : x ∈ (commonInnerRestriction Y parentOf b).carrier i) :
    0 < parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
      parentOf (parentOf i) x := by
  classical
  unfold parentLocalFiberMultiplicity
  rw [Finset.card_pos]
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl, ?_⟩⟩
  exact hx

/-- The zero bucket cannot contain a retained incidence.  Thus its dyadic
base `mu` is positive and the recomputed multiplicity lies in `[mu,2*mu)`. -/
theorem recomputed_parentLocalFiberMultiplicity_positiveBand
    (Y : Shading F) (parentOf : child → parent) (b : Nat)
    (i : child) (x : Space)
    (hx : x ∈ (commonInnerRestriction Y parentOf b).carrier i) :
    0 < comparableBase b ∧
      comparableBase b ≤
        parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
          parentOf (parentOf i) x ∧
      parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
          parentOf (parentOf i) x < 2 * comparableBase b := by
  have hcomp := recomputed_parentLocalFiberMultiplicity_zeroOrComparable
    Y parentOf b i x hx
  rcases hcomp with hzero | hpos
  · have hmulpos := recomputed_parentLocalFiberMultiplicity_pos
      Y parentOf b i x hx
    omega
  · exact hpos

/-- The repair-J1 common inner label.  Its loss is
`log₂(card child)+2`, and all retained incidences satisfy the recomputed
positive dyadic band. -/
theorem exists_commonInnerRestriction_with_large_mass
    (Y : Shading F) (parentOf : child → parent) :
    ∃ b ∈ Finset.range (Nat.log 2 (Fintype.card child) + 2),
      Y.shadingMass ≤
        (Nat.log 2 (Fintype.card child) + 2) •
          (commonInnerRestriction Y parentOf b).shadingMass ∧
      ∀ i x, x ∈ (commonInnerRestriction Y parentOf b).carrier i →
        parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
            parentOf (parentOf i) x =
          parentLocalFiberMultiplicity Y parentOf (parentOf i) x ∧
        0 < comparableBase b ∧
        comparableBase b ≤
          parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
            parentOf (parentOf i) x ∧
        parentLocalFiberMultiplicity (commonInnerRestriction Y parentOf b)
            parentOf (parentOf i) x < 2 * comparableBase b := by
  obtain ⟨b, hb, hmass, hcomp⟩ :=
    exists_restrictComparableCarrierStatisticBucket_with_large_mass
      Y (parentLocalPointStatistic Y parentOf) (Fintype.card child)
      (measurableSet_parentLocalPointStatistic_eq Y parentOf)
      (fun i x hx ↦ parentLocalFiberMultiplicity_le_card
        Y parentOf (parentOf i) x)
  refine ⟨b, hb, ?_, ?_⟩
  · simpa [commonInnerRestriction] using hmass
  · intro i x hx
    refine ⟨parentLocalFiberMultiplicity_commonInnerRestriction_eq
      Y parentOf b i x hx, ?_⟩
    exact recomputed_parentLocalFiberMultiplicity_positiveBand
      Y parentOf b i x hx

#print axioms parentLocalFiberMultiplicity_commonInnerRestriction_eq
#print axioms recomputed_parentLocalFiberMultiplicity_positiveBand
#print axioms exists_commonInnerRestriction_with_large_mass

end

end Family8CellularCommonInnerLevelV1
