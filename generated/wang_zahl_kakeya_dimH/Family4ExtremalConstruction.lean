import «Family4PublishedInputs»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4ExtremalConstruction

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly
open Family4MinimalJoint
open Family4FinalMaster
open Family4PublishedInputs

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

/-- The actual two outputs used from the WZ extremal/self-similar fiber step.

`normalized_covering` is the scale-normalized lower bound for the number of
fine tubes in one rescaled extremal fiber.  `pointwise_fiber_le` is the
pointwise multiplicity output for that fiber family.  Neither field is the
desired joint normalization, nor either half of an artificially inserted
intermediate inequality.

The witness point records the non-emptiness which is automatic for the
dense rescaled shading in the paper.  It is genuinely needed to compare the
selected dyadic bucket base with the pointwise multiplicity scale. -/
structure ExtremalTubeFamily {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r) where
  multiplicityScale : ℕ
  coveringLoss : ℝ≥0∞
  parent : κ
  parent_mem : parent ∈ P.coarseIndices
  witness : Space
  witness_mem : witness ∈
    P.asConvexFactorization.fiberShadedUnion A.refinement.shading parent
  pointwise_fiber_le : ∀ k ∈ P.coarseIndices, ∀ x ∈
      P.asConvexFactorization.fiberShadedUnion A.refinement.shading k,
    P.asConvexFactorization.fiberMultiplicity A.refinement.shading k x ≤
      multiplicityScale
  normalized_covering :
    (rho : ℝ≥0∞) ^ 2 ≤ coveringLoss *
      ((P.asConvexFactorization.index.fiber parent).card : ℝ≥0∞) *
        (delta : ℝ≥0∞) ^ 2

namespace ExtremalTubeFamily

/-- The dimensionful intermediate weight is derived from the WZ pointwise
multiplicity scale, rather than stored as an unexplained scalar. -/
def extremalWeight {r : ℝ} {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) : ℝ≥0∞ :=
  ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2

/-- The explicit loss obtained by composing the extremal covering loss with
the coarse partition's cardinal-uniformity loss. -/
def jointLoss {r : ℝ} {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) : ℝ≥0∞ :=
  ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) * E.coveringLoss *
    (P.branchingLoss : ℝ≥0∞)

private theorem witness_multiplicity_pos {r : ℝ}
    {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) :
    0 < P.asConvexFactorization.fiberMultiplicity A.refinement.shading
      E.parent E.witness := by
  apply (P.asConvexFactorization.mem_inducedShading_iff_fiberMultiplicity_pos
    A.refinement.shading E.parent E.witness).1
  rw [P.asConvexFactorization.inducedShading_carrier_eq_fiberShadedUnion]
  exact E.witness_mem

/-- Actual bucket-to-WZ adapter: nonempty bucket comparability and the WZ
pointwise bound imply that the formal assembly's `2 * base` fiber bound is
at most twice the published multiplicity scale. -/
theorem fiberBound_le_twice_multiplicityScale {r : ℝ}
    {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) :
    2 * comparableBase A.fiberLabel ≤ 2 * E.multiplicityScale := by
  have hcomp := A.fiber_comparable E.parent
    (by
      change E.parent ∈ P.index.coarse
      simpa only [CoarseTubePartition.coarseIndices] using E.parent_mem)
    E.witness E.witness_mem
  have hupper := E.pointwise_fiber_le E.parent E.parent_mem
    E.witness E.witness_mem
  rcases hcomp with hzero | hpositive
  · exfalso
    exact (Nat.ne_of_gt E.witness_multiplicity_pos) hzero.2
  · exact Nat.mul_le_mul_left 2 (hpositive.2.1.trans hupper)

/-- First half of the intermediate-weight factorization, now a theorem from
the WZ pointwise multiplicity output. -/
theorem fiber_scale_le_extremalWeight {r : ℝ}
    {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) :
    (rho : ℝ≥0∞) ^ 2 *
        ((2 * comparableBase A.fiberLabel : ℕ) : ℝ≥0∞) ≤
      E.extremalWeight := by
  unfold extremalWeight
  have hcast :
      ((2 * comparableBase A.fiberLabel : ℕ) : ℝ≥0∞) ≤
        ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) := by
    exact_mod_cast E.fiberBound_le_twice_multiplicityScale
  calc
    (rho : ℝ≥0∞) ^ 2 *
        ((2 * comparableBase A.fiberLabel : ℕ) : ℝ≥0∞) ≤
      (rho : ℝ≥0∞) ^ 2 *
        ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) :=
          mul_le_mul_of_nonneg_left hcast bot_le
    _ = ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) *
        (rho : ℝ≥0∞) ^ 2 := by ac_rfl

/-- Second half follows from the rescaled covering-number lower bound and
the existing upper comparability between the chosen fiber cardinality and
the partition branching number. -/
theorem extremalWeight_le_branching_scale {r : ℝ}
    {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) :
    E.extremalWeight ≤ E.jointLoss * (P.branching : ℝ≥0∞) *
      (delta : ℝ≥0∞) ^ 2 := by
  have hcardNat := P.fiber_card_le_loss_mul_branching
    E.parent
    (by
      simpa only [CoarseTubePartition.coarseIndices] using E.parent_mem)
  have hcard :
      ((P.asConvexFactorization.index.fiber E.parent).card : ℝ≥0∞) ≤
        (P.branchingLoss : ℝ≥0∞) * (P.branching : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold extremalWeight jointLoss
  calc
    ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) *
        (rho : ℝ≥0∞) ^ 2 ≤
      ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) *
        (E.coveringLoss *
          ((P.asConvexFactorization.index.fiber E.parent).card : ℝ≥0∞) *
            (delta : ℝ≥0∞) ^ 2) :=
      mul_le_mul_of_nonneg_left E.normalized_covering bot_le
    _ ≤ ((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) *
        (E.coveringLoss *
          ((P.branchingLoss : ℝ≥0∞) * (P.branching : ℝ≥0∞)) *
            (delta : ℝ≥0∞) ^ 2) := by
      gcongr
    _ = (((2 * E.multiplicityScale : ℕ) : ℝ≥0∞) * E.coveringLoss *
          (P.branchingLoss : ℝ≥0∞)) *
        (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 := by ring

/-- The old two-inequality carrier is constructible, rather than assumed. -/
def toScaleBranchingData {r : ℝ}
    {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) :
    ExtremalScaleBranchingData A E.jointLoss where
  extremalWeight := E.extremalWeight
  fiber_scale_le := E.fiber_scale_le_extremalWeight
  extremal_le_branching_scale := E.extremalWeight_le_branching_scale

/-- In particular the unique algebraic input of the old Family-4 master is
fully derived from covering number plus pointwise multiplicity. -/
theorem wzJointNormalization {r : ℝ}
    {A : Assembly P.asConvexFactorization Y r}
    (E : ExtremalTubeFamily A) : WZJointNormalization A E.jointLoss :=
  E.fiber_scale_le_extremalWeight.trans
    E.extremalWeight_le_branching_scale

/-- Final published-data wrapper with no naked joint inequality and no
recorded halves of that inequality. -/
theorem family4_from_extremalTubeFamily {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r)
    (S : ActiveShadingBucketData P Y)
    (E : ExtremalTubeFamily A)
    (hdeltaPos : 0 < delta) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    Conclusion A (fineFamily.refinement.loss * S.massLoss) E.jointLoss := by
  exact family4_items_one_to_six_same_object A
    (fineFamily.refinement.loss * S.massLoss) S.withinFactor_active
      E.jointLoss hdeltaPos hrhoHalf E.wzJointNormalization

end ExtremalTubeFamily
end
end Family4ExtremalConstruction

#print axioms Family4ExtremalConstruction.ExtremalTubeFamily.fiberBound_le_twice_multiplicityScale
#print axioms Family4ExtremalConstruction.ExtremalTubeFamily.fiber_scale_le_extremalWeight
#print axioms Family4ExtremalConstruction.ExtremalTubeFamily.extremalWeight_le_branching_scale
#print axioms Family4ExtremalConstruction.ExtremalTubeFamily.wzJointNormalization
#print axioms Family4ExtremalConstruction.ExtremalTubeFamily.family4_from_extremalTubeFamily
