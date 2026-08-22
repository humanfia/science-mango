import Family6Grounding.Family6FaithfulPlankSlabIncidenceCoreV9

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace Family6FineFiberCanonicalAngleSchemeCoreV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6FaithfulPlankSlabIncidenceCoreV9

noncomputable section

universe u v

/-- The nonnegative sine between the fixed faithful short normals of two
fine-fiber analytic planks.  This uses the data-bearing V9 frames directly;
no coarse occurrence reindexing is involved. -/
def faithfulFinePairSine
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (i j : index) : NNReal :=
  Real.toNNReal <| Real.sin <|
    InnerProductGeometry.angle
      ((R.plank i).box.frame 0) ((R.plank j).box.frame 0)

/-- The canonical scale-dependent fine-fiber angle row about `i`.  It is a
row of the actual analytic index type, not a support-aware coarse shading
row; hence it is suitable for arbitrary faithful test slabs. -/
def faithfulFineAngleRow
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant theta : NNReal) (i : index) : Finset index := by
  classical
  exact Finset.univ.filter fun j =>
    faithfulFinePairSine R i j ≤ angleComparisonConstant * theta

@[simp] theorem mem_faithfulFineAngleRow
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant theta : NNReal) (i j : index) :
    j ∈ faithfulFineAngleRow R angleComparisonConstant theta i ↔
      faithfulFinePairSine R i j ≤ angleComparisonConstant * theta := by
  classical
  simp [faithfulFineAngleRow]

/-- Exact maximum row occupancy at scale `theta`, with no ambient-card
replacement. -/
def faithfulFineAngleOccupancy
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant theta : NNReal) : Nat :=
  Finset.univ.sup fun i =>
    (faithfulFineAngleRow R angleComparisonConstant theta i).card

theorem faithfulFineAngleRow_card_le_occupancy
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant theta : NNReal) (i : index) :
    (faithfulFineAngleRow R angleComparisonConstant theta i).card ≤
      faithfulFineAngleOccupancy R angleComparisonConstant theta := by
  exact Finset.le_sup
    (f := fun i =>
      (faithfulFineAngleRow R angleComparisonConstant theta i).card)
    (Finset.mem_univ i)

/-- The geometric coherence gate for the fine-index scheme.  Membership is
for the same legacy slab body `S` and scale `theta`, but the two members may
come from different existential certificate frames in V9.  This explicit
property bridges those possibly distinct certificates; it is not inferred
from legacy incidence membership alone. -/
def FaithfulCommonTangentFineAngleCoverage
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant : NNReal) : Prop :=
  ∀ (theta : NNReal) (S : ConvexBody Space) (i : index),
    i ∈ R.members theta S →
      ∀ j : index, j ∈ R.members theta S →
        faithfulFinePairSine R i j ≤ angleComparisonConstant * theta

/-- The explicit cross-certificate coherence gate bounds each member set for
one legacy slab body/scale by a canonical fine-fiber row, hence by its exact
occupancy. -/
theorem faithful_members_card_le_fineAngleOccupancy
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant : NNReal)
    (hcoverage : FaithfulCommonTangentFineAngleCoverage R
      angleComparisonConstant)
    (theta : NNReal) (S : ConvexBody Space) :
    (R.members theta S).card ≤
      faithfulFineAngleOccupancy R angleComparisonConstant theta := by
  classical
  by_cases hne : (R.members theta S).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hsubset : R.members theta S ⊆
        faithfulFineAngleRow R angleComparisonConstant theta i := by
      intro j hj
      exact (mem_faithfulFineAngleRow
        R angleComparisonConstant theta i j).2
          (hcoverage theta S i hi j hj)
    exact (Finset.card_le_card hsubset).trans
      (faithfulFineAngleRow_card_le_occupancy
        R angleComparisonConstant theta i)
  · have hempty : R.members theta S = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- The exact scale-dependent numerical row estimate needed for the
manuscript `gamma = 1` control.  This is the remaining packing theorem, not
an ambient-card fallback. -/
def FaithfulFineAngleOccupancyControl
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant : NNReal) (eta : Real) : Prop :=
  ∀ theta : NNReal, a / b ≤ theta → theta ≤ 1 →
    (faithfulFineAngleOccupancy R angleComparisonConstant theta : ENNReal) ≤
      (a : ENNReal) ^ (-eta) * (theta : ENNReal) ^ (1 : Real) *
        (Fintype.card index : ENNReal)

/-- The fine-fiber angle scheme discharges the exact faithful count once
the geometric cross-certificate coherence and scale-dependent occupancy
bound are supplied. -/
theorem faithful_count_gamma_one_of_fineAngleOccupancy
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant : NNReal) (eta : Real)
    (hcoverage : FaithfulCommonTangentFineAngleCoverage R
      angleComparisonConstant)
    (hoccupancy : FaithfulFineAngleOccupancyControl R
      angleComparisonConstant eta) :
    ∀ theta : NNReal, a / b ≤ theta → theta ≤ 1 →
      ∀ S : ConvexBody Space, IsSlab slabComparisonConstant theta S →
        ((R.members theta S).card : ENNReal) ≤
          (a : ENNReal) ^ (-eta) * (theta : ENNReal) ^ (1 : Real) *
            (Fintype.card index : ENNReal) := by
  intro theta hthetaLower hthetaUpper S _hS
  have hcardNat := faithful_members_card_le_fineAngleOccupancy
    R angleComparisonConstant hcoverage theta S
  have hcard : ((R.members theta S).card : ENNReal) ≤
      (faithfulFineAngleOccupancy R angleComparisonConstant theta :
        ENNReal) := by
    exact_mod_cast hcardNat
  exact hcard.trans (hoccupancy theta hthetaLower hthetaUpper)

/-- Direct faithful-to-analytic endpoint at `gamma = 1`; no legacy empty
incidence and no conclusion callback occur. -/
theorem faithful_katzTaoControl_gamma_one_of_fineAngleOccupancy
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : FaithfulPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant : NNReal) (eta : Real)
    (hcoverage : FaithfulCommonTangentFineAngleCoverage R
      angleComparisonConstant)
    (hoccupancy : FaithfulFineAngleOccupancyControl R
      angleComparisonConstant eta) :
    KatzTaoSlabIncidenceControl D R.toPlankSlabIncidence
      slabComparisonConstant eta 1 := by
  apply FaithfulPlankSlabIncidence.katzTaoControl R eta 1
    (by norm_num) (by norm_num)
  exact faithful_count_gamma_one_of_fineAngleOccupancy
    R angleComparisonConstant eta hcoverage hoccupancy

#print axioms mem_faithfulFineAngleRow
#print axioms faithfulFineAngleRow_card_le_occupancy
#print axioms faithful_members_card_le_fineAngleOccupancy
#print axioms faithful_count_gamma_one_of_fineAngleOccupancy
#print axioms faithful_katzTaoControl_gamma_one_of_fineAngleOccupancy

end
end Family6FineFiberCanonicalAngleSchemeCoreV2
