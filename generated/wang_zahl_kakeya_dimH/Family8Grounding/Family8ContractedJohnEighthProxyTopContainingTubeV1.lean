import Family8Grounding.Family8ContractedJohnEighthProxyCarrierMonoV1
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8ContractedJohnEighthProxyTopContainingTubeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8ContractedJohnEighthProxyCarrierMonoV1
open Family8ContractedJohnNormalizedProxyScaleRatioV3

noncomputable section

/-!
# A genuine top containing tube for the transported proxy hierarchy

The actual transported source root has radius `3/64`, not one.  To cover the
remaining top interval we keep that real normalized proxy axis and enlarge
only its certified radius to one.  This is a concrete containing tube, not an
identity-radius multiscale cover.
-/

/-- Every transported proxy radius below the selected source root is at most
one. -/
theorem contractedJohnEighthProxyRadius_le_one
    {tau rho : NNReal} (hrho : 0 < rho) (htauRho : tau <= rho) :
    contractedJohnProxyRadius tau rho / 8 <= 1 := by
  calc
    contractedJohnProxyRadius tau rho / 8 <=
        contractedJohnProxyRadius rho rho / 8 :=
      contractedJohnEighthProxyRadius_mono htauRho
    _ = (3 / 64 : NNReal) := by
      rw [contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrho]
      simp [hrho.ne']
    _ <= 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num

/-- The genuine radius-one containing tube retains the actual normalized
proxy axis of `U`. -/
def contractedJohnEighthProxyTopContainingTube
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau) : Tube 1 :=
  (contractedJohnEighthProxyTube P hrho w U).changeRadius 1

@[simp]
theorem contractedJohnEighthProxyTopContainingTube_axis
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau) :
    (contractedJohnEighthProxyTopContainingTube P hrho w U).axis =
      (contractedJohnEighthProxyTube P hrho w U).axis :=
  rfl

/-- The actual proxy lies in its real radius-one containing extension. -/
theorem contractedJohnEighthProxyTube_subset_topContainingTube
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau)
    (htauRho : tau <= rho) :
    (contractedJohnEighthProxyTube P hrho w U).carrier ⊆
      (contractedJohnEighthProxyTopContainingTube P hrho w U).carrier := by
  exact Tube.carrier_subset_changeRadius _
    (contractedJohnEighthProxyRadius_le_one hrho htauRho)

/-- Package the upper endpoint object and its literal carrier containment. -/
structure ContractedJohnEighthProxyTopExtension
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau) : Prop where
  source_scale_le_root : tau <= rho
  carrier_subset_top :
    (contractedJohnEighthProxyTube P hrho w U).carrier ⊆
      (contractedJohnEighthProxyTopContainingTube P hrho w U).carrier

/-- Callback-free producer for the top containing-tube certificate. -/
theorem contractedJohnEighthProxyTopExtension_of_scale_le
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau)
    (htauRho : tau <= rho) :
    ContractedJohnEighthProxyTopExtension P hrho w U where
  source_scale_le_root := htauRho
  carrier_subset_top :=
    contractedJohnEighthProxyTube_subset_topContainingTube
      P hrho w U htauRho

#print axioms contractedJohnEighthProxyRadius_le_one
#print axioms contractedJohnEighthProxyTopContainingTube
#print axioms contractedJohnEighthProxyTube_subset_topContainingTube
#print axioms ContractedJohnEighthProxyTopExtension
#print axioms contractedJohnEighthProxyTopExtension_of_scale_le

end
end Family8ContractedJohnEighthProxyTopContainingTubeV1
