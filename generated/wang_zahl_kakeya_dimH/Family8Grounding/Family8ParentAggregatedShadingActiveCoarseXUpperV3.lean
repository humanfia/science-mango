import Family8Grounding.Family8StickyParentAggregatedDensityTransportV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ParentAggregatedShadingActiveCoarseXUpperV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8StickyParentAggregatedDensityTransportV3.StickyScaleCover

noncomputable section

/-!
# Parent shading mass is bounded by normalized active-parent cardinality

The parent aggregation is a literal shading of the active coarse tube
family.  Its mass is therefore bounded by that family's indexed volume, and
the standard tube upper bound turns the latter into
`8 * activeCoarse.card * rho^2`.  Packaging the finite normalized quantity
as `NNReal` makes it directly usable as the paper's `X = |T_b| b^2`.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The paper-normalized active-parent cardinality `|T_rho| rho^2`. -/
def activeCoarseCardScaleMass (S : StickyScaleCover fine rho) : NNReal :=
  (S.activeCoarse.card : NNReal) * rho ^ 2

/-- Parent aggregation cannot have more shaded mass than the summed actual
volumes of its active parent bodies. -/
theorem parentAggregatedShading_shadingMass_le_activeCoarseFamilyVolume
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (parentAggregatedShading S Y).shadingMass ≤
      familyVolume S.activeCoarseFamily :=
  (parentAggregatedShading S Y).shadingMass_le_familyVolume

/-- The literal generic upper bridge
`parent mass <= active parent volume <= 8 |T_rho| rho^2`. -/
theorem parentAggregatedShading_shadingMass_le_eight_mul_activeCoarseCardScaleMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹) :
    (parentAggregatedShading S Y).shadingMass ≤
      8 * (activeCoarseCardScaleMass S : ENNReal) := by
  calc
    (parentAggregatedShading S Y).shadingMass ≤
        familyVolume S.activeCoarseFamily :=
      parentAggregatedShading_shadingMass_le_activeCoarseFamilyVolume S Y
    _ ≤ (S.activeCoarse.card : ENNReal) *
          (8 * (rho : ENNReal) ^ 2) :=
      activeCoarseFamilyVolume_le_card_mul_eight_sq S hrhoHalf
    _ = 8 * (activeCoarseCardScaleMass S : ENNReal) := by
      simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
        ENNReal.coe_natCast, ENNReal.coe_pow]
      ring

/-- A lower bound for parent shading mass by eight times a global power
immediately gives the `NNReal` lower bound on the normalized active-parent
cardinality used as `hXLower` in the long-interval numerical theorem. -/
theorem global_rpow_le_activeCoarseCardScaleMass_of_parentMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {globalDelta : NNReal} {etaPrime : Real}
    (hglobal : 0 < globalDelta)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hmassLower :
      8 * (globalDelta : ENNReal) ^ etaPrime ≤
        (parentAggregatedShading S Y).shadingMass) :
    globalDelta ^ etaPrime ≤ activeCoarseCardScaleMass S := by
  have hscaled :
      8 * (globalDelta : ENNReal) ^ etaPrime ≤
        8 * (activeCoarseCardScaleMass S : ENNReal) :=
    hmassLower.trans
      (parentAggregatedShading_shadingMass_le_eight_mul_activeCoarseCardScaleMass
        S Y hrhoHalf)
  have hscaled' :
      (globalDelta : ENNReal) ^ etaPrime * 8 ≤
        (activeCoarseCardScaleMass S : ENNReal) * 8 := by
    simpa [mul_comm] using hscaled
  have hcore : (globalDelta : ENNReal) ^ etaPrime ≤
      (activeCoarseCardScaleMass S : ENNReal) := by
    exact (ENNReal.mul_le_mul_iff_left
      (by norm_num : (8 : ENNReal) ≠ 0)
      (by norm_num : (8 : ENNReal) ≠ ∞)).mp hscaled'
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_rpow_of_ne_zero hglobal.ne']
  exact hcore

#print axioms activeCoarseCardScaleMass
#print axioms
  parentAggregatedShading_shadingMass_le_activeCoarseFamilyVolume
#print axioms
  parentAggregatedShading_shadingMass_le_eight_mul_activeCoarseCardScaleMass
#print axioms global_rpow_le_activeCoarseCardScaleMass_of_parentMass

end StickyScaleCover
end
end Family8ParentAggregatedShadingActiveCoarseXUpperV3
