import Family8Grounding.Family8ParentwiseBadParentFactorReplacementV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8ContractedJohnEighthProxyCarrierNestingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizationCarrierV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8TubeJohnContractedLipschitzV1
open Family8TubeJohnUnitRescalingGeometryLeOneV7
open Family8ParentwiseBadParentFactorReplacementV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Carrier nesting for the actual contracted-John/eighth fresh child

The common contracted-John affine equivalence and the common eighth dilation
preserve every source carrier inclusion.  The resulting literal image is
then housed in the genuine normalized proxy tube already used by the fresh
datum.  This module records both facts separately: image nesting is proved,
whereas proxy-tube nesting is exposed as the exact extra certificate needed
to build a new coherent Sticky hierarchy.  In particular, no identity-radius
cover is substituted for the actual proxy family.
-/

/-- The genuine fresh tube: first form the contracted-John proxy and then
apply the repository's eighth normalization. -/
def contractedJohnEighthProxyTube
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) :
    Tube (contractedJohnProxyRadius delta rho / 8) :=
  eighthNormalizedTube (contractedJohnProxyTube P hrho w T)

@[simp]
theorem contractedJohnEighthProxyTube_axis
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) :
    (contractedJohnEighthProxyTube P hrho w T).axis =
      eighthNormalizedAxis (contractedJohnProxyTube P hrho w T) :=
  rfl

/-- The literal double image underlying the actual fresh shading. -/
def contractedJohnEighthCarrierImage
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) : Set Space :=
  eighthDilationPoint ''
    (contractedTubeJohnAffineEquiv P hrho w '' T.carrier)

/-- Applying the same contracted-John map and the same eighth dilation
preserves a source carrier inclusion exactly. -/
theorem contractedJohnEighthCarrierImage_mono
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (hTU : T.carrier ⊆ U.carrier) :
    contractedJohnEighthCarrierImage P hrho w T ⊆
      contractedJohnEighthCarrierImage P hrho w U := by
  exact Set.image_mono (Set.image_mono hTU)

/-- The literal double image of a source tube is contained in its genuine
contracted-John/eighth proxy tube. -/
theorem contractedJohnEighthCarrierImage_subset_proxy
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta)
    (hTP : T.carrier ⊆ P.carrier) :
    contractedJohnEighthCarrierImage P hrho w T ⊆
      (contractedJohnEighthProxyTube P hrho w T).carrier := by
  exact
    (Set.image_mono
      (image_child_carrier_subset_contractedJohnProxyTube
        P hrho w T hTP)).trans
      (image_eighthDilation_tube_carrier_subset_normalizedTube
        (contractedJohnProxyTube P hrho w T))

/-- If a source child lies in a source ancestor, its literal fresh image is
already housed in the ancestor's genuine normalized proxy.  This is the
paper-faithful image-level cross-scale nesting statement. -/
theorem contractedJohnEighthCarrierImage_subset_ancestorProxy
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (hTU : T.carrier ⊆ U.carrier) (hUP : U.carrier ⊆ P.carrier) :
    contractedJohnEighthCarrierImage P hrho w T ⊆
      (contractedJohnEighthProxyTube P hrho w U).carrier := by
  exact (contractedJohnEighthCarrierImage_mono P hrho w T U hTU).trans
    (contractedJohnEighthCarrierImage_subset_proxy P hrho w U hUP)

/-- The exact additional carrier field required of an actual proxy parent.
It speaks about the real normalized proxy tubes, not only their shaded
subsets or their literal affine images. -/
def IsContractedJohnEighthProxyParent
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau) : Prop :=
  (contractedJohnEighthProxyTube P hrho w T).carrier ⊆
    (contractedJohnEighthProxyTube P hrho w U).carrier

/-- A positive hierarchy seam: source nesting gives image-level nesting,
and the explicit `actual_proxy_carrier_subset` field is precisely what a
`CoherentStickyMultiscaleCover.carrier_subset` implementation consumes. -/
structure ContractedJohnEighthProxyParentCertificate
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau) : Prop where
  source_carrier_subset : T.carrier ⊆ U.carrier
  ancestor_carrier_subset_root : U.carrier ⊆ P.carrier
  actual_proxy_carrier_subset :
    IsContractedJohnEighthProxyParent P hrho w T U

/-- The certificate's source fields automatically recover the literal-image
nesting used by every transported shading. -/
theorem ContractedJohnEighthProxyParentCertificate.image_subset_parentProxy
    {delta tau rho : NNReal} {P : Tube rho} {hrho : 0 < rho}
    {w : JohnAxisWitness P.body} {T : Tube delta} {U : Tube tau}
    (h : ContractedJohnEighthProxyParentCertificate P hrho w T U) :
    contractedJohnEighthCarrierImage P hrho w T ⊆
      (contractedJohnEighthProxyTube P hrho w U).carrier :=
  contractedJohnEighthCarrierImage_subset_ancestorProxy P hrho w T U
    h.source_carrier_subset h.ancestor_carrier_subset_root

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The family of the exact bad-parent rescaling consists definitionally of
the genuine contracted-John/eighth proxy tubes. -/
@[simp]
theorem badParentRescaledFibreDatum_family_tubes
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (i : {i // i ∈ S.fiber q.1}) :
    (badParentRescaledFibreDatum S Y hrho hrhoOne q).family.tubes i =
      contractedJohnEighthProxyTube (S.coarse.tubes q.1) hrho
        (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne q)
        (fine.tubes i.1) :=
  rfl

/-- Its shading carrier is the literal common double image, before any
restriction to the fresh selected subtype. -/
@[simp]
theorem badParentRescaledFibreDatum_shading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (i : {i // i ∈ S.fiber q.1}) :
    (badParentRescaledFibreDatum S Y hrho hrhoOne q).shading.carrier i =
      eighthDilationPoint ''
        (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne q ''
          Y.carrier i.1) :=
  rfl

/-- Restricting to the selected fresh subtype does not change the genuine
proxy tube assigned to an index. -/
@[simp]
theorem badParentFreshSuccessorDatum_family_tubes
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (i : {i // i ∈ selected}) :
    (badParentFreshSuccessorDatum
      S Y hrho hrhoOne q selected).family.tubes i =
      contractedJohnEighthProxyTube (S.coarse.tubes q.1) hrho
        (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne q)
        (fine.tubes i.1.1) :=
  rfl

/-- The selected fresh shading remains the literal common double image. -/
@[simp]
theorem badParentFreshSuccessorDatum_shading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (i : {i // i ∈ selected}) :
    (badParentFreshSuccessorDatum
      S Y hrho hrhoOne q selected).shading.carrier i =
      eighthDilationPoint ''
        (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne q ''
          Y.carrier i.1.1) :=
  rfl

/-- A fresh selected shading carrier is contained in the genuine proxy tube
of any source ancestor in the same selected `q` fibre.  All maps here are
the actual maps used by `badParentFreshSuccessorDatum`. -/
theorem badParentFreshSuccessorDatum_shading_subset_ancestorProxy
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (i : {i // i ∈ selected}) {tau : NNReal} (U : Tube tau)
    (hchildAncestor : (fine.tubes i.1.1).carrier ⊆ U.carrier)
    (hancestorRoot : U.carrier ⊆ (S.coarse.tubes q.1).carrier) :
    (badParentFreshSuccessorDatum
      S Y hrho hrhoOne q selected).shading.carrier i ⊆
      (contractedJohnEighthProxyTube (S.coarse.tubes q.1) hrho
        (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne q)
        U).carrier := by
  rw [badParentFreshSuccessorDatum_shading_carrier]
  exact
    (Set.image_mono (Set.image_mono (Y.carrier_subset i.1.1))).trans
      (contractedJohnEighthCarrierImage_subset_ancestorProxy
        (S.coarse.tubes q.1) hrho
        (StickyScaleCover.tubeJohnWitnessLeOne S hrho hrhoOne q)
        (fine.tubes i.1.1) U hchildAncestor hancestorRoot)

#print axioms contractedJohnEighthProxyTube
#print axioms contractedJohnEighthCarrierImage_mono
#print axioms contractedJohnEighthCarrierImage_subset_proxy
#print axioms contractedJohnEighthCarrierImage_subset_ancestorProxy
#print axioms IsContractedJohnEighthProxyParent
#print axioms ContractedJohnEighthProxyParentCertificate
#print axioms ContractedJohnEighthProxyParentCertificate.image_subset_parentProxy
#print axioms badParentRescaledFibreDatum_family_tubes
#print axioms badParentRescaledFibreDatum_shading_carrier
#print axioms badParentFreshSuccessorDatum_family_tubes
#print axioms badParentFreshSuccessorDatum_shading_carrier
#print axioms badParentFreshSuccessorDatum_shading_subset_ancestorProxy

end
end Family8ContractedJohnEighthProxyCarrierNestingV1
