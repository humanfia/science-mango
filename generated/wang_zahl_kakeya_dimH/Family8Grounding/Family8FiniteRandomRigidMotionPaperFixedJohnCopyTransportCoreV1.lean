import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanConnectorV1
import Family8Grounding.Family8RigidCopyPolynomialJohnKatzTaoV1
import FamilyStickyGrounding.Family6AffineKatzTaoTransportV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1
open Family8RigidCopyPolynomialJohnKatzTaoV1
open Family6AffineConvexVolumeCoreV1
open Family6AffineKatzTaoTransportV3
open FamilyStickyActualTubeTranslationV1

noncomputable section

/-! Exact Katz--Tao, volume, mass, density, and support transport for the
pure-translation copies produced by the automatic fixed-John selector. -/

theorem fixedRigidCopyBodyFamily_isKatzTao
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {C : ENNReal}
    (R : RigidMotion) (F : UniformTubeFamily delta iota)
    (hKT : IsKatzTao C F.bodyFamily) :
    IsKatzTao C (fixedRigidCopyBodyFamily R F) := by
  have heq : fixedRigidCopyBodyFamily R F =
      affineImageFamily R.toAffineEquiv F.bodyFamily := by
    funext i
    apply ConvexBody.ext
    simp only [fixedRigidCopyBodyFamily, affineImageFamily,
      coe_affineImageConvexBody, UniformTubeFamily.bodyFamily_apply,
      Tube.coe_body, rigidTube_carrier]
    rfl
  rw [heq]
  exact isKatzTao_affineImageFamily R.toAffineEquiv F.bodyFamily hKT

theorem indexedRigidCopyTubeFamily_isKatzTao_card_mul
    {tau iota : Type} [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {C : ENNReal}
    (motion : tau -> RigidMotion) (F : UniformTubeFamily delta iota)
    (hKT : IsKatzTao C F.bodyFamily) :
    IsKatzTao ((Fintype.card tau : ENNReal) * C)
      (indexedRigidCopyTubeFamily motion F).bodyFamily := by
  intro K
  unfold IsKatzTaoAt
  rw [containedMass_indexedRigidCopyTubeFamily]
  calc
    (∑ j, containedMass (fixedRigidCopyBodyFamily (motion j) F) K) <=
        ∑ _j : tau, C * volume (K : Set Space) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact fixedRigidCopyBodyFamily_isKatzTao (motion j) F hKT K
    _ = ((Fintype.card tau : ENNReal) * C) *
        volume (K : Set Space) := by
      simp [nsmul_eq_mul]
      ac_rfl

theorem eighthNormalizedIndexedTranslation_actualFamilyVolume
    {tau iota : Type} [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (v : tau -> Space)
    (D : ActualTubeDatum delta iota) :
    (eighthNormalizedDatum
      (indexedRigidCopyDatum (fun j => translationRigidMotion (v j)) D)).actualFamilyVolume =
      (Fintype.card tau : ENNReal) *
        (eighthNormalizedDatum D).actualFamilyVolume := by
  classical
  unfold ActualTubeDatum.actualFamilyVolume familyVolume
  rw [Fintype.sum_prod_type]
  simp_rw [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
    eighthNormalizedDatum_family, eighthNormalizedTubeFamily_tubes,
    indexedRigidCopyDatum, indexedRigidCopyTubeFamily_tubes,
    eighthNormalizedTube_rigidTranslation, translateTube_volume]
  simp [nsmul_eq_mul]

theorem eighthNormalizedIndexedTranslation_shadingMass
    {tau iota : Type} [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (v : tau -> Space)
    (D : ActualTubeDatum delta iota) :
    (eighthNormalizedDatum
      (indexedRigidCopyDatum (fun j => translationRigidMotion (v j)) D)).shading.shadingMass =
      (Fintype.card tau : ENNReal) *
        (eighthNormalizedDatum D).shading.shadingMass := by
  change
    (eighthNormalizedShading
      (indexedRigidCopyTubeFamily
        (fun j => translationRigidMotion (v j)) D.family)
      (indexedRigidCopyShading
        (fun j => translationRigidMotion (v j)) D.family D.shading)).shadingMass =
      (Fintype.card tau : ENNReal) *
        (eighthNormalizedShading D.family D.shading).shadingMass
  rw [eighthNormalizedShading_shadingMass,
    indexedRigidCopyShading_shadingMass,
    eighthNormalizedShading_shadingMass]
  ac_rfl

theorem eighthNormalizedIndexedTranslation_shadingDensity
    {tau iota : Type} [Fintype tau] [Nonempty tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (v : tau -> Space)
    (D : ActualTubeDatum delta iota) :
    (eighthNormalizedDatum
      (indexedRigidCopyDatum (fun j => translationRigidMotion (v j)) D)).shading.shadingDensity =
      (eighthNormalizedDatum D).shading.shadingDensity := by
  change
    (eighthNormalizedDatum
      (indexedRigidCopyDatum
        (fun j => translationRigidMotion (v j)) D)).shading.shadingMass /
        (eighthNormalizedDatum
          (indexedRigidCopyDatum
            (fun j => translationRigidMotion (v j)) D)).actualFamilyVolume =
      (eighthNormalizedDatum D).shading.shadingMass /
        (eighthNormalizedDatum D).actualFamilyVolume
  rw [eighthNormalizedIndexedTranslation_shadingMass,
    eighthNormalizedIndexedTranslation_actualFamilyVolume]
  apply ENNReal.mul_div_mul_left
  · exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty tau)).ne'
  · exact ENNReal.coe_ne_top

theorem indexedTranslation_carrier_subset_twoBall
    {tau iota : Type} [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (v : tau -> Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hv : forall j, ‖v j‖ <= 1) :
    forall a,
      ((indexedRigidCopyDatum
        (fun j => translationRigidMotion (v j)) D).family.tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro a
  exact rigidTranslationTube_carrier_subset_twoBall
    (D.family.tubes a.2) (v a.1)
      (hD.contained_in_unit_ball a.2) (hv a.1)

#print axioms fixedRigidCopyBodyFamily_isKatzTao
#print axioms indexedRigidCopyTubeFamily_isKatzTao_card_mul
#print axioms eighthNormalizedIndexedTranslation_actualFamilyVolume
#print axioms eighthNormalizedIndexedTranslation_shadingMass
#print axioms eighthNormalizedIndexedTranslation_shadingDensity
#print axioms indexedTranslation_carrier_subset_twoBall

end
end Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
