import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

/-!
# Local Frostman control to Katz--Tao on one literal selected Sticky fibre

This is the honest first step in the low normalized-CF branch.  The ambient
Frostman certificate is not treated as globally Katz--Tao for free: its
actual ambient family-volume density is retained in the constant.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLocalFrostmanKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A local Frostman certificate at one actual parent gives global
Katz--Tao control on the same literal retained subtype.  The constant keeps
the exact ambient family-volume density. -/
theorem selectedFiber_isKatzTao_of_isFrostmanIn
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {C : ENNReal}
    (hF : IsFrostmanIn C
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q)) :
    IsKatzTao
      (C * ambientFamilyVolumeDensity
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q))
      (activeSubtypeFamily (S.fiberFamily q.1) selected) := by
  apply isKatzTao_of_isFrostmanIn_familyVolumeDensity hF
  · change volume (S.coarse.tubes q.1).carrier ≠ 0
    exact (Tube.volume_pos (S.coarse.tubes q.1) hrho).ne'
  · exact (S.activeCoarseFamily q).isCompact.measure_lt_top.ne

#print axioms selectedFiber_isKatzTao_of_isFrostmanIn

end
end Family8StickySelectedFiberLocalFrostmanKatzTaoV1
