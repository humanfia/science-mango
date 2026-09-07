import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedCFDividingWitnessBridgeV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# A genuine lower normalization for parent fibres

Parent surjectivity supplies one literal fine child in every active parent.
The standard tube-volume sandwich therefore gives the uniform, computed
lower bound

`((delta^2 / 2) / (8 * rho^2)) <= fibre volume / parent volume`.

Combining this fact with the exact identity from
`Family8NormalizedCFDividingWitnessBridgeV2` transports a lower bound for the
paper-normalized fibre constant to a lower bound for the legacy absolute
`fiberDeltaMax`.  No lower concentration estimate is assumed in this file.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The uniform geometric floor for the mass of one literal parent fibre,
normalized by the volume of its parent. -/
def parentFiberMassRatioFloor (delta rho : NNReal) : ENNReal :=
  (((delta : ENNReal) ^ 2) / 2) / (8 * (rho : ENNReal) ^ 2)

/-- At positive parent radius, the displayed floor is exactly
`delta^2 / (16 rho^2)`. -/
theorem parentFiberMassRatioFloor_eq_sixteen
    (delta rho : NNReal) (hrho : 0 < rho) :
    parentFiberMassRatioFloor delta rho =
      (delta : ENNReal) ^ 2 / (16 * (rho : ENNReal) ^ 2) := by
  unfold parentFiberMassRatioFloor
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top
      (ENNReal.div_ne_top (by finiteness) (by norm_num)) (by positivity))
    (ENNReal.div_ne_top (by finiteness) (by positivity))).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow]
  ring

/-- One child selected by parent surjectivity contributes its standard
`delta^2 / 2` volume lower bound to the whole literal fibre. -/
theorem half_sq_le_fiberFamilyVolume_of_activeParent
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (k : {k // k ∈ S.activeCoarse}) :
    (delta : ENNReal) ^ 2 / 2 <= familyVolume (S.fiberFamily k.1) := by
  classical
  obtain ⟨i, hiActive, hiParent⟩ := S.parent_surjective k.1 k.2
  have hiFiber : i ∈ S.fiber k.1 :=
    (S.mem_fiber i k.1).2 ⟨hiActive, hiParent⟩
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : {j // j ∈ S.fiber k.1} =>
      volume (S.fiberFamily k.1 j : Set Space))
    (fun _ _ => bot_le)
    (Finset.mem_univ (⟨i, hiFiber⟩ : {j // j ∈ S.fiber k.1}))
  exact (fine.tubes i).half_sq_le_volume_of_le_half hdeltaHalf |>.trans <| by
    simpa [familyVolume, StickyScaleCover.fiberFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body] using hsingle

/-- Every actual active parent fibre has mass ratio at least the explicit
tube-volume floor. -/
theorem parentFiberMassRatioFloor_le
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (k : {k // k ∈ S.activeCoarse}) :
    parentFiberMassRatioFloor delta rho <= parentFiberMassRatio S k := by
  unfold parentFiberMassRatioFloor parentFiberMassRatio
  apply ENNReal.div_le_div
  · exact half_sq_le_fiberFamilyVolume_of_activeParent S hdeltaHalf k
  · change volume (S.coarse.tubes k.1).carrier <=
      8 * (rho : ENNReal) ^ 2
    exact (S.coarse.tubes k.1).volume_le_eight_mul_sq_of_le_half hrhoHalf

/-- Pointwise normalized concentration times the geometric fibre-mass floor
is bounded by the actual absolute maximal concentration of that fibre. -/
theorem parentNormalizedFiberCFAt_mul_floor_le_maximalConcentration
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (k : {k // k ∈ S.activeCoarse}) :
    parentNormalizedFiberCFAt S k * parentFiberMassRatioFloor delta rho <=
      maximalConcentration (S.fiberFamily k.1) := by
  calc
    parentNormalizedFiberCFAt S k * parentFiberMassRatioFloor delta rho <=
        parentNormalizedFiberCFAt S k * parentFiberMassRatio S k :=
      mul_le_mul' le_rfl (parentFiberMassRatioFloor_le S hdeltaHalf hrhoHalf k)
    _ = maximalConcentration (S.fiberFamily k.1) :=
      parentNormalizedFiberCFAt_mul_parentFiberMassRatio S hdelta hrho k

/-- The exact global lower transport: the computed worst normalized
`C_F`, multiplied by the unavoidable scale ratio, is below the actual
legacy `fiberDeltaMax`. -/
theorem parentNormalizedFiberCFMax_mul_floor_le_fiberDeltaMax
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    parentNormalizedFiberCFMax S * parentFiberMassRatioFloor delta rho <=
      fiberDeltaMax S := by
  unfold parentNormalizedFiberCFMax
  rw [ENNReal.iSup_mul]
  apply iSup_le
  intro k
  exact
    (parentNormalizedFiberCFAt_mul_floor_le_maximalConcentration
      S hdelta hrho hdeltaHalf hrhoHalf k).trans
      (maximalConcentration_fiber_le_fiberDeltaMax S k)

/-- A supplied lower bound for the computed normalized `C_F` value can
therefore be transported to the actual absolute dividing value.  The only
loss is the proved geometric scale ratio. -/
theorem mul_floor_le_fiberDeltaMax_of_le_parentNormalizedFiberCFMax
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {lower : ENNReal} (hlower : lower <= parentNormalizedFiberCFMax S) :
    lower * parentFiberMassRatioFloor delta rho <= fiberDeltaMax S :=
  (mul_le_mul' hlower le_rfl).trans
    (parentNormalizedFiberCFMax_mul_floor_le_fiberDeltaMax
      S hdelta hrho hdeltaHalf hrhoHalf)

#print axioms parentFiberMassRatioFloor_eq_sixteen
#print axioms half_sq_le_fiberFamilyVolume_of_activeParent
#print axioms parentFiberMassRatioFloor_le
#print axioms parentNormalizedFiberCFAt_mul_floor_le_maximalConcentration
#print axioms parentNormalizedFiberCFMax_mul_floor_le_fiberDeltaMax
#print axioms mul_floor_le_fiberDeltaMax_of_le_parentNormalizedFiberCFMax

end StickyScaleCover

end
end Family8NormalizedCFDividingWitnessBridgeV4
