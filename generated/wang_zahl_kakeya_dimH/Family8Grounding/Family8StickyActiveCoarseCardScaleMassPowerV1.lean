import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Delta-power envelope for normalized active-parent mass

The scale-local Katz--Tao estimate already controls the literal normalized
parent mass `#parents * rho^2` by `1024 * A`.  This file absorbs only that
fixed constant and keeps the estimate on the same Sticky cover.  It is the
numerator input for the honest shading-aware cover loss.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open scoped ENNReal NNReal

namespace Family8StickyActiveCoarseCardScaleMassPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def stickyActiveCoarseCardScaleMassPowerThreshold
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 1024 absorbExponent

theorem stickyActiveCoarseCardScaleMassPowerThreshold_pos
    (absorbExponent : Real) :
    0 < stickyActiveCoarseCardScaleMassPowerThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- A scale-local Katz--Tao power bound gives a power bound for the literal
normalized parent mass, with one explicit fixed-constant absorption. -/
theorem activeCoarseCardScaleMass_le_delta_negativePower_of_katzTaoAtScale
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {A : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    {katzTaoExponent absorbExponent : Real}
    (hA : A ≤ (delta : ENNReal) ^ (-katzTaoExponent))
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      stickyActiveCoarseCardScaleMassPowerThreshold absorbExponent) :
    (activeCoarseCardScaleMass S : ENNReal) ≤
      (delta : ENNReal) ^ (-(katzTaoExponent + absorbExponent)) := by
  have hraw : (activeCoarseCardScaleMass S : ENNReal) ≤ 1024 * A :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale
      D hD S hrhoHalf hKT
  have hconstant : (1024 : ENNReal) ≤
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExponent hD.delta_pos hsmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (activeCoarseCardScaleMass S : ENNReal) ≤ 1024 * A := hraw
    _ ≤ (delta : ENNReal) ^ (-absorbExponent) *
        (delta : ENNReal) ^ (-katzTaoExponent) :=
      mul_le_mul' hconstant hA
    _ = (delta : ENNReal) ^
        (-(katzTaoExponent + absorbExponent)) := by
      rw [show -(katzTaoExponent + absorbExponent) =
          -absorbExponent + -katzTaoExponent by ring,
        ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]

#print axioms stickyActiveCoarseCardScaleMassPowerThreshold_pos
#print axioms
  activeCoarseCardScaleMass_le_delta_negativePower_of_katzTaoAtScale

end
end Family8StickyActiveCoarseCardScaleMassPowerV1
