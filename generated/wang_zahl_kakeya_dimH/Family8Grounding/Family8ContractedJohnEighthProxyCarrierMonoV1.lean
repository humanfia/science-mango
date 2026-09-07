import Family8Grounding.Family8ContractedJohnEighthProxyCarrierNestingV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ContractedJohnEighthProxyCarrierMonoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyCarrierNestingV1

noncomputable section

/-!
# Actual normalized proxy carrier monotonicity

This module supplies the real tube-level field needed by a coherent Sticky
cover.  Exact nesting follows from nesting of the normalized unit axes and
the monotonicity of the transported radius.  When the axes are only close,
we instead construct a genuine buffered containing tube and expose the whole
axis-gap/radius budget explicitly.
-/

/-- The contracted-John/eighth radius is monotone in the source scale while
the selected root scale is fixed. -/
theorem contractedJohnEighthProxyRadius_mono
    {delta tau rho : NNReal} (hdeltaTau : delta <= tau) :
    contractedJohnProxyRadius delta rho / 8 <=
      contractedJohnProxyRadius tau rho / 8 := by
  unfold contractedJohnProxyRadius
  gcongr

/-- Tube carriers are monotone when both their unit axes and radii are
monotone. -/
theorem tube_carrier_subset_of_axis_subset_of_radius_le
    {delta tau : NNReal} (T : Tube delta) (U : Tube tau)
    (haxis : T.axis.carrier ⊆ U.axis.carrier)
    (hdeltaTau : delta <= tau) :
    T.carrier ⊆ U.carrier := by
  change Metric.cthickening (delta : Real) T.axis.carrier ⊆
    Metric.cthickening (tau : Real) U.axis.carrier
  exact (Metric.cthickening_subset_of_subset (delta : Real) haxis).trans
    (Metric.cthickening_mono (by exact_mod_cast hdeltaTau) U.axis.carrier)

/-- The actual fixed-scale proxy-parent producer.  The additional `haxis`
is the honest geometric condition required after unit-axis extension; the
source carrier fields are retained below in the full step certificate. -/
theorem contractedJohnEighthProxyTube_carrier_mono_of_axis_subset
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (hdeltaTau : delta <= tau)
    (haxis :
      (contractedJohnEighthProxyTube P hrho w T).axis.carrier ⊆
        (contractedJohnEighthProxyTube P hrho w U).axis.carrier) :
    IsContractedJohnEighthProxyParent P hrho w T U := by
  exact tube_carrier_subset_of_axis_subset_of_radius_le
    (contractedJohnEighthProxyTube P hrho w T)
    (contractedJohnEighthProxyTube P hrho w U) haxis
    (contractedJohnEighthProxyRadius_mono hdeltaTau)

/-- All source-window facts and both levels of transported containment for
one actual hierarchy step. -/
structure ContractedJohnEighthActualHierarchyStep
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau) : Prop where
  delta_le_tau : delta <= tau
  tau_le_root : tau <= rho
  source_carrier_subset : T.carrier ⊆ U.carrier
  ancestor_carrier_subset_root : U.carrier ⊆ P.carrier
  literal_image_subset_parentProxy :
    contractedJohnEighthCarrierImage P hrho w T ⊆
      (contractedJohnEighthProxyTube P hrho w U).carrier
  actual_proxy_carrier_subset :
    IsContractedJohnEighthProxyParent P hrho w T U

/-- Positive producer for an actual hierarchy step.  Source containment
closes the literal-image field; normalized-axis nesting closes the genuine
proxy-tube field. -/
theorem contractedJohnEighthActualHierarchyStep_of_axis_subset
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (hdeltaTau : delta <= tau) (htauRho : tau <= rho)
    (hTU : T.carrier ⊆ U.carrier) (hUP : U.carrier ⊆ P.carrier)
    (haxis :
      (contractedJohnEighthProxyTube P hrho w T).axis.carrier ⊆
        (contractedJohnEighthProxyTube P hrho w U).axis.carrier) :
    ContractedJohnEighthActualHierarchyStep P hrho w T U where
  delta_le_tau := hdeltaTau
  tau_le_root := htauRho
  source_carrier_subset := hTU
  ancestor_carrier_subset_root := hUP
  literal_image_subset_parentProxy :=
    contractedJohnEighthCarrierImage_subset_ancestorProxy
      P hrho w T U hTU hUP
  actual_proxy_carrier_subset :=
    contractedJohnEighthProxyTube_carrier_mono_of_axis_subset
      P hrho w T U hdeltaTau haxis

/-- Requested carrier producer with the complete source-window ledger.  No
condition is hidden: `haxis` is precisely the extra normalized-axis fact
which does not follow merely by applying `Set.image_mono`. -/
theorem contractedJohnEighthProxyTube_carrier_mono
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (hdeltaTau : delta <= tau) (htauRho : tau <= rho)
    (hTU : T.carrier ⊆ U.carrier) (hUP : U.carrier ⊆ P.carrier)
    (haxis :
      (contractedJohnEighthProxyTube P hrho w T).axis.carrier ⊆
        (contractedJohnEighthProxyTube P hrho w U).axis.carrier) :
    IsContractedJohnEighthProxyParent P hrho w T U :=
  (contractedJohnEighthActualHierarchyStep_of_axis_subset
    P hrho w T U hdeltaTau htauRho hTU hUP haxis).actual_proxy_carrier_subset

/-- A genuine containing-tube extension of an actual proxy parent.  It keeps
the parent's normalized axis and increases its certified radius by the
explicit nonnegative buffer. -/
def contractedJohnEighthProxyContainingTube
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau) (buffer : NNReal) :
    Tube (contractedJohnProxyRadius tau rho / 8 + buffer) :=
  (contractedJohnEighthProxyTube P hrho w U).buffer buffer

@[simp]
theorem contractedJohnEighthProxyContainingTube_axis
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau) (buffer : NNReal) :
    (contractedJohnEighthProxyContainingTube
      P hrho w U buffer).axis =
        (contractedJohnEighthProxyTube P hrho w U).axis :=
  rfl

/-- The unbuffered genuine proxy is contained in its genuine containing-tube
extension. -/
theorem contractedJohnEighthProxyTube_subset_containingTube
    {tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (U : Tube tau) (buffer : NNReal) :
    (contractedJohnEighthProxyTube P hrho w U).carrier ⊆
      (contractedJohnEighthProxyContainingTube
        P hrho w U buffer).carrier :=
  Tube.carrier_subset_buffer _ _

/-- A child proxy is contained in a buffered actual parent whenever its
normalized axis lies in an explicit `axisGap`-neighborhood of the parent
axis and the displayed radius budget closes. -/
theorem contractedJohnEighthProxyTube_subset_containingTube_of_axisGap
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (axisGap buffer : NNReal)
    (haxis :
      (contractedJohnEighthProxyTube P hrho w T).axis.carrier ⊆
        Metric.cthickening (axisGap : Real)
          (contractedJohnEighthProxyTube P hrho w U).axis.carrier)
    (hbudget :
      contractedJohnProxyRadius delta rho / 8 + axisGap <=
        contractedJohnProxyRadius tau rho / 8 + buffer) :
    (contractedJohnEighthProxyTube P hrho w T).carrier ⊆
      (contractedJohnEighthProxyContainingTube
        P hrho w U buffer).carrier := by
  change
    Metric.cthickening
        ((contractedJohnProxyRadius delta rho / 8 : NNReal) : Real)
        (contractedJohnEighthProxyTube P hrho w T).axis.carrier ⊆
      Metric.cthickening
        (((contractedJohnProxyRadius tau rho / 8 + buffer : NNReal)) : Real)
        (contractedJohnEighthProxyTube P hrho w U).axis.carrier
  have hthicken := Metric.cthickening_subset_of_subset
    (((contractedJohnProxyRadius delta rho / 8 : NNReal)) : Real) haxis
  rw [cthickening_cthickening (by positivity) (by positivity)] at hthicken
  exact hthicken.trans
    (Metric.cthickening_mono (by exact_mod_cast hbudget)
      (contractedJohnEighthProxyTube P hrho w U).axis.carrier)

#print axioms contractedJohnEighthProxyRadius_mono
#print axioms tube_carrier_subset_of_axis_subset_of_radius_le
#print axioms contractedJohnEighthProxyTube_carrier_mono_of_axis_subset
#print axioms ContractedJohnEighthActualHierarchyStep
#print axioms contractedJohnEighthActualHierarchyStep_of_axis_subset
#print axioms contractedJohnEighthProxyTube_carrier_mono
#print axioms contractedJohnEighthProxyContainingTube
#print axioms contractedJohnEighthProxyTube_subset_containingTube
#print axioms contractedJohnEighthProxyTube_subset_containingTube_of_axisGap

end
end Family8ContractedJohnEighthProxyCarrierMonoV1
