import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ActiveCoarseFrostmanCardScaleMassLowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyParentAggregatedDensityTransportV3.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Active-coarse Frostman concentration gives the normalized coarse count

This is the paper-faithful consumer of the reciprocal Frostman constant of
the coarse family.  The ambient convex body is arbitrary: its volume lower
normalization and the full `IsFrostmanIn` certificate are explicit inputs.
Thus it applies after the paper's unit-scale rescaling without claiming that
an unrescaled sticky parent family lies in the unit ball.

The upstream maximal-density flat-prism construction of this active-coarse
Frostman certificate remains the precise producer seam.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A nonempty active coarse Frostman family in any ambient convex body
satisfies the exact normalization `1 <= C * familyVolume`. -/
theorem one_le_frostmanConstant_mul_activeCoarseFamilyVolume
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    {C : ENNReal} (hrho : 0 < rho)
    (hcoarse : S.activeCoarse.Nonempty)
    (hKVolume : 1 ≤ volume (K : Set Space))
    (hF : IsFrostmanIn C S.activeCoarseFamily K) :
    1 ≤ C * familyVolume S.activeCoarseFamily := by
  obtain ⟨k, hk⟩ := hcoarse
  let kk : {k // k ∈ S.activeCoarse} := ⟨k, hk⟩
  let Kprime : ConvexBody Space := S.activeCoarseFamily kk
  have hsubset : (Kprime : Set Space) ⊆ (K : Set Space) :=
    hF.family_subset kk
  have htubeMass : volume (Kprime : Set Space) ≤
      containedMass S.activeCoarseFamily Kprime := by
    unfold containedMass
    exact Finset.single_le_sum
      (fun j _ => show
        (0 : ENNReal) ≤
          volume (S.activeCoarseFamily j : Set Space) from bot_le)
      ((mem_containedIndices S.activeCoarseFamily Kprime kk).2 subset_rfl)
  have hambient : containedMass S.activeCoarseFamily K =
      familyVolume S.activeCoarseFamily :=
    containedMass_eq_familyVolume_of_contained
      S.activeCoarseFamily K hF.1
  have hcross := IsFrostmanIn.cross_le hF hsubset
  rw [hambient] at hcross
  have hchain : volume (Kprime : Set Space) * volume (K : Set Space) ≤
      (C * familyVolume S.activeCoarseFamily) *
        volume (Kprime : Set Space) := by
    calc
      volume (Kprime : Set Space) * volume (K : Set Space) ≤
          containedMass S.activeCoarseFamily Kprime *
            volume (K : Set Space) := mul_le_mul_left htubeMass _
      _ ≤ (C * familyVolume S.activeCoarseFamily) *
          volume (Kprime : Set Space) := hcross
  have htube0 : volume (Kprime : Set Space) ≠ 0 := by
    change volume (S.coarse.tubes k).carrier ≠ 0
    exact ne_of_gt ((S.coarse.tubes k).volume_pos hrho)
  have htubeTop : volume (Kprime : Set Space) ≠ ∞ := by
    change volume (S.coarse.tubes k).carrier ≠ ∞
    exact (S.coarse.tubes k).volume_lt_top.ne
  have hambientBase : volume (K : Set Space) ≤
      C * familyVolume S.activeCoarseFamily := by
    apply (ENNReal.mul_le_mul_iff_left htube0 htubeTop).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hchain
  exact hKVolume.trans hambientBase

/-- The coarse tube-volume upper bound converts `C <= d^(-e)` into the
paper lower bound up to the explicit dimensional constant eight. -/
theorem global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_frostman
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    {C : ENNReal} {globalDelta : NNReal} {etaPrime : Real}
    (hglobal : 0 < globalDelta)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hKVolume : 1 ≤ volume (K : Set Space))
    (hF : IsFrostmanIn C S.activeCoarseFamily K)
    (hC : C ≤ (globalDelta : ENNReal) ^ (-etaPrime)) :
    (globalDelta : ENNReal) ^ etaPrime ≤
      8 * (activeCoarseCardScaleMass S : ENNReal) := by
  have hd0 : (globalDelta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hglobal.ne'
  have hdTop : (globalDelta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hvolume : familyVolume S.activeCoarseFamily ≤
      8 * (activeCoarseCardScaleMass S : ENNReal) := by
    calc
      familyVolume S.activeCoarseFamily ≤
          (S.activeCoarse.card : ENNReal) *
            (8 * (rho : ENNReal) ^ 2) :=
        activeCoarseFamilyVolume_le_card_mul_eight_sq S hrhoHalf
      _ = 8 * (activeCoarseCardScaleMass S : ENNReal) := by
        simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
          ENNReal.coe_natCast, ENNReal.coe_pow]
        ring
  have hone : 1 ≤ (globalDelta : ENNReal) ^ (-etaPrime) *
      (8 * (activeCoarseCardScaleMass S : ENNReal)) := by
    calc
      1 ≤ C * familyVolume S.activeCoarseFamily :=
        one_le_frostmanConstant_mul_activeCoarseFamilyVolume
          S K hrho hcoarse hKVolume hF
      _ ≤ (globalDelta : ENNReal) ^ (-etaPrime) *
          (8 * (activeCoarseCardScaleMass S : ENNReal)) :=
        mul_le_mul hC hvolume bot_le bot_le
  calc
    (globalDelta : ENNReal) ^ etaPrime =
        (globalDelta : ENNReal) ^ etaPrime * 1 := by simp
    _ ≤ (globalDelta : ENNReal) ^ etaPrime *
        ((globalDelta : ENNReal) ^ (-etaPrime) *
          (8 * (activeCoarseCardScaleMass S : ENNReal))) :=
      mul_le_mul_right hone _
    _ = 8 * (activeCoarseCardScaleMass S : ENNReal) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 hdTop]
      simp

#print axioms one_le_frostmanConstant_mul_activeCoarseFamilyVolume
#print axioms
  global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_frostman

end StickyScaleCover
end
end Family8ActiveCoarseFrostmanCardScaleMassLowerV3
