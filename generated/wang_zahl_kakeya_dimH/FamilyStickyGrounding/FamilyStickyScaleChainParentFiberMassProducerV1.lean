import FamilyStickyGrounding.FamilyStickyScaleChainCoherentTreeLocalizationV1

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainParentFiberMassProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyParentFiberMassDecompositionV6.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainCoherentTreeLocalizationV1

noncomputable section

/-!
# Sticky Kakeya: actual parent-fiber mass producer

For an actual `StickyScaleCover` with positive parent radius, every parent
tube has positive finite volume.  We therefore compute the exact finite
fiber-to-parent mass ratios and take their supremum.  Division cancellation
then proves `ParentFiberMassMonotonicity`; no mass inequality is supplied as
data.

This is the measure-theoretic normalization underlying the per-parent term
in equation (50) of GWZ Lemma 7.4.  The paper later bounds these actual ratios
using uniform branching and tube-volume comparability, absorbing the resulting
dimension constant into `C(n)^M`.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (S : StickyScaleCover fine rho)

/-- The literal mass ratio of one active fine fiber to its actual parent. -/
def parentFiberMassRatio (k : {k // k ∈ S.activeCoarse}) : ENNReal :=
  familyVolume (S.fiberFamily k.1) /
    MeasureTheory.volume (S.activeCoarseFamily k : Set Space)

/-- The exact worst parent-fiber mass ratio in this finite cover. -/
def actualParentFiberMassLoss : ENNReal :=
  ⨆ k : {k // k ∈ S.activeCoarse}, parentFiberMassRatio S k

/-- Every actual fiber ratio is below the computed supremum. -/
theorem parentFiberMassRatio_le_actualParentFiberMassLoss
    (k : {k // k ∈ S.activeCoarse}) :
    parentFiberMassRatio S k <= actualParentFiberMassLoss S :=
  le_iSup (parentFiberMassRatio S) k

/-- Positivity of the parent radius makes the ratio normalization exact. -/
theorem familyVolume_eq_parentFiberMassRatio_mul_parentVolume
    (hrho : 0 < rho) (k : {k // k ∈ S.activeCoarse}) :
    familyVolume (S.fiberFamily k.1) =
      parentFiberMassRatio S k *
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space) := by
  unfold parentFiberMassRatio
  rw [ENNReal.div_mul_cancel]
  · change MeasureTheory.volume (S.coarse.tubes k.1).carrier ≠ 0
    exact (S.coarse.tubes k.1).volume_pos hrho |>.ne'
  · change MeasureTheory.volume (S.coarse.tubes k.1).carrier ≠ ∞
    exact (S.coarse.tubes k.1).volume_lt_top.ne

/-- The computed loss automatically satisfies the earliest parent-fiber
mass monotonicity required by nested-cover localization. -/
theorem actualParentFiberMassMonotonicity (hrho : 0 < rho) :
    ParentFiberMassMonotonicity S (actualParentFiberMassLoss S) := by
  constructor
  intro k
  rw [familyVolume_eq_parentFiberMassRatio_mul_parentVolume S hrho k]
  gcongr
  exact parentFiberMassRatio_le_actualParentFiberMassLoss S k

end StickyScaleCover

#print axioms StickyScaleCover.familyVolume_eq_parentFiberMassRatio_mul_parentVolume
#print axioms StickyScaleCover.actualParentFiberMassMonotonicity

end
end FamilyStickyScaleChainParentFiberMassProducerV1
