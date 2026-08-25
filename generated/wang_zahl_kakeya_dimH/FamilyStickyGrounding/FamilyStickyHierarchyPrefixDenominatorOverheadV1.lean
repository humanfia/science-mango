import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import FamilyStickyGrounding.FamilyStickyFinalMultiscaleAssemblyCertificateV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyPrefixDenominatorOverheadV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open FamilyStickyActualTubeTranslationV1
open FamilyStickyConvexBodyTranslationConcentrationV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyHierarchyEndpointPrefixBridgeV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1

noncomputable section

/-!
# Quantitative supplied-prefix denominator overhead

The endpoint-to-prefix shading transport preserves shading mass exactly after
the endpoint parent aggregation, but an injective body map may leave extra
prefix occurrences.  This module records the minimal quantitative datum for
those extra occurrences and converts it into the exact quotient-form density
loss.

For the actual hierarchy prefix, finite cardinality and the uniform tube
volume bounds produce the explicit loss
`16 * Fintype.card PrefixIndex` as soon as the endpoint family has one
occurrence.  The final assembly binding below uses the hierarchy certificate's
literal supplied joint output.  The empty-to-singleton obstruction at the end
shows why endpoint nonemptiness cannot be removed from this producer.
-/

/-! ## Generic denominator algebra for a body-preserving embedding -/

namespace BodyPreservingEmbedding

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  {F : ConvexFamily iota} {G : ConvexFamily kappa}
  (E : BodyPreservingEmbedding F G)

/-- The minimal quantitative replacement for range exhaustion: the target
family denominator is at most `volumeLoss` times the source denominator. -/
structure DenominatorOverhead (volumeLoss : ENNReal) : Prop where
  familyVolume_le : familyVolume G <= volumeLoss * familyVolume F

namespace DenominatorOverhead

variable {E} {volumeLoss : ENNReal}
  (D : DenominatorOverhead (F := F) (G := G) volumeLoss)

include D
/-- Exact multiplier form of the density loss.  It is safe when a family
volume or the declared loss is zero or infinite. -/
theorem sourceDensity_le_loss_mul_pushforwardDensity (Y : Shading F) :
    Y.shadingDensity <=
      volumeLoss * (E.pushforwardShading Y).shadingDensity := by
  by_cases hFzero : familyVolume F = 0
  · have hmass : Y.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp
        (Y.shadingMass_le_familyVolume.trans_eq hFzero)
    simp [Shading.shadingDensity, hFzero, hmass,
      E.pushforwardShading_shadingMass]
  · rw [← ENNReal.mul_le_mul_iff_right hFzero (familyVolume_ne_top F)]
    calc
      familyVolume F * Y.shadingDensity = Y.shadingMass := by
        rw [mul_comm, shadingDensity_mul_familyVolume]
      _ = (E.pushforwardShading Y).shadingMass :=
        (E.pushforwardShading_shadingMass Y).symm
      _ = (E.pushforwardShading Y).shadingDensity * familyVolume G :=
        (shadingDensity_mul_familyVolume (E.pushforwardShading Y)).symm
      _ <= (E.pushforwardShading Y).shadingDensity *
          (volumeLoss * familyVolume F) :=
        mul_le_mul_of_nonneg_left D.familyVolume_le bot_le
      _ = familyVolume F *
          (volumeLoss * (E.pushforwardShading Y).shadingDensity) := by
        ac_rfl

/-- Quotient form: the target shading density retains at least the source
density divided by the declared denominator overhead. -/
theorem sourceDensity_div_loss_le_pushforwardDensity (Y : Shading F) :
    Y.shadingDensity / volumeLoss <=
      (E.pushforwardShading Y).shadingDensity := by
  apply ENNReal.div_le_of_le_mul'
  exact sourceDensity_le_loss_mul_pushforwardDensity D Y

end DenominatorOverhead

end BodyPreservingEmbedding

/-! ## Automatic overhead for the actual supplied hierarchy prefix -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  {G : FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  (Q : SuppliedHierarchy.Certificate H G P)
  (C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
    (H.effectiveFamily 0))
  (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    (H.effectiveRadius 0) depth)

namespace Identification

variable {H Q C S}
  (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification H Q C S)

/-- The explicit denominator loss furnished by the full finite supplied
prefix cardinality and the uniform radius-`delta` tube-volume sandwich. -/
def prefixCardinalityVolumeLoss (m : Fin depth) : ENNReal :=
  16 * Fintype.card
    (PrefixIndex H (G := G) (I.endpointEffective.layer m)
      (I.effectivePrefix.parent m))

/-- Every member of the literal supplied prefix obeys the common upper
radius-`delta` tube-volume bound, including both translations. -/
theorem suppliedPrefix_member_volume_le_eight_sq
    (m : Fin depth)
    (j : PrefixIndex H (G := G) (I.endpointEffective.layer m)
      (I.effectivePrefix.parent m)) :
    volume
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m) j :
          Set Space) <=
      8 * (H.effectiveRadius (I.endpointEffective.layer m).1 : ENNReal) ^ 2 := by
  simp only [suppliedPrefixFamily, translateFamily, volume_translateConvexBody]
  change volume
      (FixedPackingPotentialFamily.selectedTube
        (hierarchyFiberSeedData H (I.endpointEffective.layer m)
          (I.effectivePrefix.parent m))
        (P.certificate (I.endpointEffective.layer m))
        (JointCertificateAdapter.plannedOmega Q.joint P Q.usesPlan
          (I.endpointEffective.layer m)) j).carrier <= _
  rw [FixedPackingPotentialFamily.selectedTube, translateTube_volume]
  exact
    ((H.effectiveFamily (I.endpointEffective.layer m).1).tubes j.2.1).volume_le_eight_mul_sq_of_le_half
      (G.childRadius_le_half (I.endpointEffective.layer m))

end Identification

namespace Identification

variable {H Q C S}
  (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification H Q C S)

/-- Every supplied-prefix member also obeys the matching lower tube-volume
bound; translations introduce no loss. -/
theorem half_sq_le_suppliedPrefix_member_volume
    (m : Fin depth)
    (j : PrefixIndex H (G := G) (I.endpointEffective.layer m)
      (I.effectivePrefix.parent m)) :
    (H.effectiveRadius (I.endpointEffective.layer m).1 : ENNReal) ^ 2 / 2 <=
      volume
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m) j :
          Set Space) := by
  simp only [suppliedPrefixFamily, translateFamily, volume_translateConvexBody]
  change _ <= volume
      (FixedPackingPotentialFamily.selectedTube
        (hierarchyFiberSeedData H (I.endpointEffective.layer m)
          (I.effectivePrefix.parent m))
        (P.certificate (I.endpointEffective.layer m))
        (JointCertificateAdapter.plannedOmega Q.joint P Q.usesPlan
          (I.endpointEffective.layer m)) j).carrier
  rw [FixedPackingPotentialFamily.selectedTube, translateTube_volume]
  exact
    ((H.effectiveFamily (I.endpointEffective.layer m).1).tubes j.2.1).half_sq_le_volume_of_le_half
      (G.childRadius_le_half (I.endpointEffective.layer m))

/-- The identified endpoint occurrence inherits the common lower tube-volume
bound from its literal body-equal supplied-prefix image. -/
theorem half_sq_le_endpoint_member_volume
    (m : Fin depth) (i : EndpointIndex H C S m) :
    (H.effectiveRadius (I.endpointEffective.layer m).1 : ENNReal) ^ 2 / 2 <=
      volume (endpointFamily H C S m i : Set Space) := by
  rw [I.endpointPrefix_body_eq m i]
  exact half_sq_le_suppliedPrefix_member_volume I m
    (I.endpointPrefixEmbedding m i)

/-- Every endpoint occurrence contributes its literal body volume to the
summed endpoint denominator. -/
theorem endpoint_member_volume_le_familyVolume
    (m : Fin depth) (i : EndpointIndex H C S m) :
    volume (endpointFamily H C S m i : Set Space) <=
      familyVolume (endpointFamily H C S m) := by
  classical
  unfold familyVolume
  exact Finset.single_le_sum
    (f := fun j : EndpointIndex H C S m =>
      volume (endpointFamily H C S m j : Set Space))
    (fun _ _ => bot_le) (Finset.mem_univ i)

/-- With one actual endpoint occurrence, every supplied-prefix occurrence is
at most sixteen times the full endpoint denominator. -/
theorem suppliedPrefix_member_volume_le_sixteen_mul_endpointFamilyVolume
    (m : Fin depth) (i : EndpointIndex H C S m)
    (j : PrefixIndex H (G := G) (I.endpointEffective.layer m)
      (I.effectivePrefix.parent m)) :
    volume
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m) j :
          Set Space) <=
      16 * familyVolume (endpointFamily H C S m) := by
  calc
    volume
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m) j :
          Set Space) <=
        8 * (H.effectiveRadius (I.endpointEffective.layer m).1 : ENNReal) ^ 2 :=
      suppliedPrefix_member_volume_le_eight_sq I m j
    _ = 16 *
        ((H.effectiveRadius (I.endpointEffective.layer m).1 : ENNReal) ^ 2 / 2) := by
      rw [show (16 : ENNReal) = 8 * 2 by norm_num, mul_assoc,
        ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    _ <= 16 * volume (endpointFamily H C S m i : Set Space) :=
      mul_le_mul_of_nonneg_left
        (half_sq_le_endpoint_member_volume I m i) bot_le
    _ <= 16 * familyVolume (endpointFamily H C S m) :=
      mul_le_mul_of_nonneg_left
        (endpoint_member_volume_le_familyVolume m i) bot_le

/-- A nonempty endpoint family automatically controls the entire supplied
prefix denominator by the explicit cardinality loss. -/
theorem suppliedPrefix_familyVolume_le_cardinality_loss
    (m : Fin depth) (hendpoint : Nonempty (EndpointIndex H C S m)) :
    familyVolume
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m)) <=
      prefixCardinalityVolumeLoss I m *
        familyVolume (endpointFamily H C S m) := by
  classical
  let i : EndpointIndex H C S m := Classical.choice hendpoint
  unfold familyVolume
  calc
    (∑ j : PrefixIndex H (G := G) (I.endpointEffective.layer m)
        (I.effectivePrefix.parent m),
      volume
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m) j :
          Set Space)) <=
        Fintype.card
            (PrefixIndex H (G := G) (I.endpointEffective.layer m)
              (I.effectivePrefix.parent m)) •
          (16 * familyVolume (endpointFamily H C S m)) := by
      exact Finset.sum_le_card_nsmul Finset.univ _ _
        (fun j _hj =>
          suppliedPrefix_member_volume_le_sixteen_mul_endpointFamilyVolume
            I m i j)
    _ = prefixCardinalityVolumeLoss I m *
        ∑ i : EndpointIndex H C S m,
          volume (endpointFamily H C S m i : Set Space) := by
      simp only [prefixCardinalityVolumeLoss, nsmul_eq_mul]
      ac_rfl
/-- The automatic cardinality loss packaged as the minimal generic
denominator-overhead certificate. -/
theorem cardinalityDenominatorOverhead
    (m : Fin depth) (hendpoint : Nonempty (EndpointIndex H C S m)) :
    BodyPreservingEmbedding.DenominatorOverhead
      (F := endpointFamily H C S m)
      (G := suppliedPrefixFamily H Q (I.effectivePrefix.path m)
        (I.endpointEffective.layer m) (I.effectivePrefix.parent m))
      (prefixCardinalityVolumeLoss I m) where
  familyVolume_le :=
    suppliedPrefix_familyVolume_le_cardinality_loss I m hendpoint

/-- The endpoint parent-aggregated shading retains its density in the literal
supplied prefix up to the explicit finite cardinality loss. -/
theorem parentAggregatedDensity_div_cardinalityLoss_le_suppliedPrefixDensity
    (m : Fin depth) (hendpoint : Nonempty (EndpointIndex H C S m))
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y).shadingDensity /
        prefixCardinalityVolumeLoss I m <=
      (Identification.suppliedPrefixShading I m Y).shadingDensity := by
  exact
    (cardinalityDenominatorOverhead I m hendpoint).sourceDensity_div_loss_le_pushforwardDensity
      (E := Identification.endpointPrefixBodyEmbedding I m)
      (StickyScaleCover.parentAggregatedShading (upperEndpointCover C S m) Y)

end Identification



end
end FamilyStickyHierarchyPrefixDenominatorOverheadV1

namespace FamilyStickyHierarchyPrefixDenominatorOverheadV1

/-! ## Binding to the final certificate's literal supplied joint output -/

namespace FinalAssembly

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchyEndpointPrefixBridgeV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  {C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
    (H.effectiveFamily 0)}
  {S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    (H.effectiveRadius 0) depth}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
  (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
    H G P C S epsilon massLoss bodyLoss katzTaoLoss frostmanError katzTaoError)
  (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification
    H A.hierarchy C S)

/-- The shading used at the supplied prefix of the final certificate's exact
joint output has exactly the endpoint parent-aggregated mass. -/
theorem suppliedPrefixShading_shadingMass_eq_parentAggregated
    (m : Fin depth) (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (Identification.suppliedPrefixShading I m Y).shadingMass =
      (StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y).shadingMass := by
  unfold Identification.suppliedPrefixShading
  exact
    BodyPreservingEmbedding.pushforwardShading_shadingMass
      (Identification.endpointPrefixBodyEmbedding I m)
      (StickyScaleCover.parentAggregatedShading (upperEndpointCover C S m) Y)

/-- Any quantitative denominator overhead on the prefix selected by the
stored final-certificate joint output gives the exact quotient-form density
loss. -/
theorem parentAggregatedDensity_div_loss_le_sameJointSuppliedPrefixDensity
    (m : Fin depth) (volumeLoss : ENNReal)
    (D : BodyPreservingEmbedding.DenominatorOverhead
      (F := endpointFamily H C S m)
      (G := suppliedPrefixFamily H A.hierarchy (I.effectivePrefix.path m)
        (I.endpointEffective.layer m) (I.effectivePrefix.parent m))
      volumeLoss)
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y).shadingDensity / volumeLoss <=
      (Identification.suppliedPrefixShading I m Y).shadingDensity := by
  exact D.sourceDensity_div_loss_le_pushforwardDensity
    (E := Identification.endpointPrefixBodyEmbedding I m)
    (StickyScaleCover.parentAggregatedShading (upperEndpointCover C S m) Y)

/-- For the exact joint output stored by the final certificate, endpoint
nonemptiness produces the explicit `16 * card PrefixIndex` density loss
without a caller-supplied volume comparison. -/
theorem parentAggregatedDensity_div_cardinalityLoss_le_sameJointSuppliedPrefixDensity
    (m : Fin depth) (hendpoint : Nonempty (EndpointIndex H C S m))
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (StickyScaleCover.parentAggregatedShading
        (upperEndpointCover C S m) Y).shadingDensity /
        Identification.prefixCardinalityVolumeLoss I m <=
      (Identification.suppliedPrefixShading I m Y).shadingDensity := by
  exact
    Identification.parentAggregatedDensity_div_cardinalityLoss_le_suppliedPrefixDensity
      I m hendpoint Y

end FinalAssembly

/-! ## Sharp zero-denominator obstruction -/

open Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1

/-- No multiplicative overhead, even an infinite one, can dominate a
positive singleton target denominator by an empty source denominator.  Thus
finite target cardinality alone cannot replace endpoint nonemptiness. -/
theorem no_emptySingleton_denominatorOverhead
    (K : ConvexBody Space) (hK : volume (K : Set Space) ≠ 0)
    (volumeLoss : ENNReal) :
    Not (BodyPreservingEmbedding.DenominatorOverhead
      (F := emptyFamily) (G := singletonFamily K) volumeLoss) := by
  intro D
  have hle : volume (K : Set Space) <= 0 := by
    simpa [familyVolume, emptyFamily, singletonFamily] using D.familyVolume_le
  exact hK (nonpos_iff_eq_zero.mp hle)

#print axioms BodyPreservingEmbedding.DenominatorOverhead.sourceDensity_le_loss_mul_pushforwardDensity
#print axioms BodyPreservingEmbedding.DenominatorOverhead.sourceDensity_div_loss_le_pushforwardDensity
#print axioms Identification.suppliedPrefix_member_volume_le_eight_sq
#print axioms Identification.half_sq_le_suppliedPrefix_member_volume
#print axioms Identification.suppliedPrefix_familyVolume_le_cardinality_loss
#print axioms Identification.cardinalityDenominatorOverhead
#print axioms Identification.parentAggregatedDensity_div_cardinalityLoss_le_suppliedPrefixDensity
#print axioms FinalAssembly.suppliedPrefixShading_shadingMass_eq_parentAggregated
#print axioms FinalAssembly.parentAggregatedDensity_div_loss_le_sameJointSuppliedPrefixDensity
#print axioms FinalAssembly.parentAggregatedDensity_div_cardinalityLoss_le_sameJointSuppliedPrefixDensity
#print axioms no_emptySingleton_denominatorOverhead

end FamilyStickyHierarchyPrefixDenominatorOverheadV1
