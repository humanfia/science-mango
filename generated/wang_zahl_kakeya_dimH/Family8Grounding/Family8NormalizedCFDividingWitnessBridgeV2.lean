import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerV3
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import FamilyStickyGrounding.FamilyStickyScaleChainParentFiberMassToFiberDeltaV1

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedCFDividingWitnessBridgeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassToFiberDeltaV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Parent-normalized fibre concentration versus the legacy dividing value

Paper Lemma 7.7(A) uses the parent-normalized quantity
`C_F(fibre,parent)`.  The legacy dividing witness instead stores the absolute
`fiberDeltaMax`, the supremum of the unnormalized maximal concentrations of
the fibres.  This module records the exact missing normalization.

For every actual active fibre,

`canonical C_F * (fibre mass / parent volume) = maximalConcentration fibre`.

Consequently the legacy absolute value is at most the product of the actual
worst normalized `C_F` and the actual worst parent-fibre mass ratio.  No
concentration estimate is supplied by the caller.  In particular, this file
does not claim that a normalized lower bound implies the legacy witness's
absolute lower bound: that implication would require a genuine lower bound
for the parent-fibre mass ratio, which a bare `StickyScaleCover` does not
provide.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The exact parent-normalized Frostman constant of one literal active
fibre. -/
def parentNormalizedFiberCFAt (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse}) : ENNReal :=
  canonicalFrostmanConstant (S.fiberFamily k.1) (S.activeCoarseFamily k)

/-- The genuine worst parent-normalized `C_F` over the finite active
fibres. -/
def parentNormalizedFiberCFMax (S : StickyScaleCover fine rho) : ENNReal :=
  ⨆ k : {k // k ∈ S.activeCoarse}, parentNormalizedFiberCFAt S k

theorem parentNormalizedFiberCFAt_le
    (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse}) :
    parentNormalizedFiberCFAt S k ≤ parentNormalizedFiberCFMax S :=
  le_iSup (parentNormalizedFiberCFAt S) k

/-- Every member of a literal fibre is contained in its actual parent. -/
theorem fiberFamily_subset_parent
    (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse})
    (i : {i // i ∈ S.fiber k.1}) :
    (S.fiberFamily k.1 i : Set Space) ⊆
      (S.activeCoarseFamily k : Set Space) := by
  simpa [StickyScaleCover.fiberFamily,
    StickyScaleCover.activeCoarseFamily, UniformTubeFamily.bodyFamily,
    Tube.coe_body] using S.fiber_carrier_subset_parent k.1 i

/-- An active fibre of positive-radius tubes has positive total volume. -/
theorem fiberFamilyVolume_pos
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (k : {k // k ∈ S.activeCoarse}) :
    0 < familyVolume (S.fiberFamily k.1) := by
  obtain ⟨i, hiActive, hiParent⟩ := S.parent_surjective k.1 k.2
  have hiFiber : i ∈ S.fiber k.1 :=
    (S.mem_fiber i k.1).2 ⟨hiActive, hiParent⟩
  unfold familyVolume
  rw [Finset.sum_pos_iff]
  refine ⟨⟨i, hiFiber⟩, Finset.mem_univ _, ?_⟩
  simpa [StickyScaleCover.fiberFamily, UniformTubeFamily.bodyFamily,
    Tube.coe_body] using (fine.tubes i).volume_pos hdelta

/-- Because the whole fibre lies in its parent, its parent-contained mass is
its literal full family volume. -/
theorem containedMass_fiberFamily_parent_eq_familyVolume
    (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse}) :
    containedMass (S.fiberFamily k.1) (S.activeCoarseFamily k) =
      familyVolume (S.fiberFamily k.1) :=
  containedMass_eq_familyVolume_of_contained
    (S.fiberFamily k.1) (S.activeCoarseFamily k)
    (fiberFamily_subset_parent S k)

/-- Exact normalization identity at one active parent.  Both factors are
computed from the actual cover. -/
theorem parentNormalizedFiberCFAt_mul_parentFiberMassRatio
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta) (hrho : 0 < rho)
    (k : {k // k ∈ S.activeCoarse}) :
    parentNormalizedFiberCFAt S k * parentFiberMassRatio S k =
      maximalConcentration (S.fiberFamily k.1) := by
  have hmass0 : familyVolume (S.fiberFamily k.1) ≠ 0 :=
    (fiberFamilyVolume_pos S hdelta k).ne'
  have hmassTop : familyVolume (S.fiberFamily k.1) ≠ ∞ :=
    familyVolume_ne_top (S.fiberFamily k.1)
  have hparent0 : volume (S.activeCoarseFamily k : Set Space) ≠ 0 := by
    change volume (S.coarse.tubes k.1).carrier ≠ 0
    exact (S.coarse.tubes k.1).volume_pos hrho |>.ne'
  have hparentTop : volume (S.activeCoarseFamily k : Set Space) ≠ ∞ := by
    change volume (S.coarse.tubes k.1).carrier ≠ ∞
    exact (S.coarse.tubes k.1).volume_lt_top.ne
  unfold parentNormalizedFiberCFAt canonicalFrostmanConstant
  unfold parentFiberMassRatio
  rw [containedMass_fiberFamily_parent_eq_familyVolume S k]
  calc
    (maximalConcentration (S.fiberFamily k.1) *
          volume (S.activeCoarseFamily k : Set Space) /
          familyVolume (S.fiberFamily k.1)) *
        (familyVolume (S.fiberFamily k.1) /
          volume (S.activeCoarseFamily k : Set Space)) =
      maximalConcentration (S.fiberFamily k.1) *
          ((volume (S.activeCoarseFamily k : Set Space) /
            familyVolume (S.fiberFamily k.1)) *
            familyVolume (S.fiberFamily k.1)) /
          volume (S.activeCoarseFamily k : Set Space) := by
        simp only [div_eq_mul_inv]
        ac_rfl
    _ = maximalConcentration (S.fiberFamily k.1) *
          volume (S.activeCoarseFamily k : Set Space) /
          volume (S.activeCoarseFamily k : Set Space) := by
        rw [ENNReal.div_mul_cancel hmass0 hmassTop]
    _ = maximalConcentration (S.fiberFamily k.1) :=
      ENNReal.mul_div_cancel_right hparent0 hparentTop

/-- The at-scale Frostman predicate is exactly a bound on the computed worst
parent-normalized `C_F`, once the positive fine radius supplies nonzero fibre
mass. -/
theorem isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta) (C : ENNReal) :
    S.IsFrostmanAtScale C ↔ parentNormalizedFiberCFMax S ≤ C := by
  constructor
  · intro hF
    apply iSup_le
    intro k
    have hIn : IsFrostmanIn C
        (S.fiberFamily k.1) (S.activeCoarseFamily k) :=
      isFrostmanIn_iff_concentration_le.mpr
        ⟨fiberFamily_subset_parent S k, hF k.1 k.2⟩
    apply
      Family8GreedyOccurrenceCanonicalFrostmanBridgeV2.canonicalFrostmanConstant_le_of_isFrostmanIn
        hIn
    rw [containedMass_fiberFamily_parent_eq_familyVolume S k]
    exact (fiberFamilyVolume_pos S hdelta k).ne'
  · intro hCF k hk K hK
    let kk : {k // k ∈ S.activeCoarse} := ⟨k, hk⟩
    have hmass0 :
        containedMass (S.fiberFamily k) (S.activeCoarseFamily kk) ≠ 0 := by
      rw [containedMass_fiberFamily_parent_eq_familyVolume S kk]
      exact (fiberFamilyVolume_pos S hdelta kk).ne'
    have hmassTop :
        containedMass (S.fiberFamily k) (S.activeCoarseFamily kk) ≠ ∞ := by
      rw [containedMass_fiberFamily_parent_eq_familyVolume S kk]
      exact familyVolume_ne_top (S.fiberFamily k)
    have hcanonical : IsFrostmanIn
        (parentNormalizedFiberCFAt S kk)
        (S.fiberFamily k) (S.activeCoarseFamily kk) := by
      exact
        Family8ActiveCoarseCanonicalFrostmanXLowerV3.canonicalFrostmanConstant_isFrostmanIn
          (S.fiberFamily k) (S.activeCoarseFamily kk)
          (fiberFamily_subset_parent S kk) hmass0 hmassTop
    have hCFk : parentNormalizedFiberCFAt S kk ≤ C :=
      (parentNormalizedFiberCFAt_le S kk).trans hCF
    exact (hcanonical.mono hCFk).concentration_le hK

/-- The exact upper transport from paper-normalized fibre concentration to
the absolute legacy `fiberDeltaMax`.  The extra factor is not a callback: it
is the literal finite `iSup` of actual fibre-mass/parent-volume ratios. -/
theorem fiberDeltaMax_le_parentNormalizedFiberCFMax_mul_actualParentLoss
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta) (hrho : 0 < rho) :
    fiberDeltaMax S ≤
      parentNormalizedFiberCFMax S * actualParentFiberMassLoss S := by
  apply iSup_le
  intro k
  rw [← parentNormalizedFiberCFAt_mul_parentFiberMassRatio
    S hdelta hrho k]
  exact mul_le_mul'
    (parentNormalizedFiberCFAt_le S k)
    (parentFiberMassRatio_le_actualParentFiberMassLoss S k)

#print axioms fiberFamilyVolume_pos
#print axioms containedMass_fiberFamily_parent_eq_familyVolume
#print axioms parentNormalizedFiberCFAt_mul_parentFiberMassRatio
#print axioms isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
#print axioms
  fiberDeltaMax_le_parentNormalizedFiberCFMax_mul_actualParentLoss

end StickyScaleCover

end
end Family8NormalizedCFDividingWitnessBridgeV2
