import Family8Grounding.Family8GeneralizedFrostmanCanonicalCardInterpolationV1
import Family8Grounding.Family8PlankLongTubeFrostmanAtParametersProducerV1
import Family8Grounding.Family8EighthNormalizedAmbientDensityCancellationV1
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedRowLongTubeCanonicalFrostmanComparisonV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8AmbientFamilyVolumeDensityV2
open Family8EighthNormalizedAmbientDensityCancellationV1
open Family8EighthNormalizedKatzTaoAmbientFrostmanV2
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8GeneralizedFrostmanCanonicalCardInterpolationV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeAmbientB2SupportV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankLongTubeCenteredFreshV4
open Family8PlankLongTubeFrostmanAtParametersProducerV1
open Family8PlankLongTubeFrostmanTransferV3
open Family8PlankLongTubeGlobalKatzTaoV3
open Family8PlankLongTubeThickenedAmbientFrostmanV3
open FamilyStickyAdjacentTestBodyGeometryV1

noncomputable section

/-!
# Canonical Frostman constant of a normalized row long-tube source

The row Frostman envelope first controls the literal normalized plank row.
The genuine long-tube cover, its one centering translation, and the honest
eighth normalization then produce a unit-ball Frostman certificate for the
actual tube datum.  The factor `65536 = 128 * 512` is exactly the global
Katz--Tao normalization cost times the lower family-volume transport cost.

No convex-plank `BoundAt`, Family 7 union conclusion, or multiplicity bound
is used here.  The visible loss consists only of the certified memberwise
plank-to-long-tube volume ratio and the actual ambient-volume quotient.
-/

/-- The row-local geometric loss between a Frostman certificate on one plank
family and the canonical unit-ball Frostman constant of its eighth-normalized
centered long-tube source. -/
def plankLongTubeCanonicalFrostmanComparisonLoss
    {rowOwner : Type} [Fintype rowOwner] [DecidableEq rowOwner]
    {short long : NNReal}
    (Drow : ShadedConvexPlankFamily rowOwner short long) : ENNReal :=
  (65536 *
      plankLongTubeFrostmanCopyLoss Drow.comparisonConstant short long) *
      volume (unitBallBody : Set Space) /
    volume (Drow.ambient : Set Space)

/-- The explicit geometric loss between the row Frostman envelope and the
canonical unit-ball Frostman constant of its eighth-normalized centered
long-tube source. -/
def normalizedRowLongTubeCanonicalFrostmanLoss
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) : ENNReal :=
  (65536 * normalizedRowLongTubeCopyLoss P r) *
      volume (unitBallBody : Set Space) /
    volume ((P.normalizedRowDatum r).ambient : Set Space)

/-- The normalized-row spelling of the comparison loss is definitionally the
row-local loss on the corresponding affine-normalized plank family. -/
theorem normalizedRowLongTubeCanonicalFrostmanLoss_eq
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    normalizedRowLongTubeCanonicalFrostmanLoss P r =
      plankLongTubeCanonicalFrostmanComparisonLoss
        (P.normalizedRowDatum r) := by
  rfl

/-- A Frostman certificate on one nonempty plank family bounds the canonical
Frostman constant of its genuine centered and eighth-normalized long-tube
source.  This is the row-local core: it has no all-row restriction certificate
and no ambient source family. -/
theorem sourceCanonicalFrostmanConstant_eighthCenteredLongTube_le
    {rowOwner : Type} [Fintype rowOwner] [Nonempty rowOwner]
    [DecidableEq rowOwner]
    {short long : NNReal}
    (Drow : ShadedConvexPlankFamily rowOwner short long)
    (rowCF : ENNReal)
    (hrowFrostman : IsFrostmanIn rowCF Drow.family Drow.ambient)
    (hlongHalf : long ≤ (2 : NNReal)⁻¹) :
    sourceCanonicalFrostmanConstant
        (eighthNormalizedDatum (centeredPlankLongTubeActualDatum Drow)) ≤
      plankLongTubeCanonicalFrostmanComparisonLoss Drow * rowCF := by
  let raw := centeredPlankLongTubeActualDatum Drow
  let normalized := eighthNormalizedDatum raw
  let ambient := closedThickeningBody Drow.ambient 1

  have hlongPos : 0 < long := by
    exact longWidth_pos_of_nonempty Drow
  have hrawKatzTao :
      IsKatzTao (plankLongTubeGlobalKatzTaoConstant Drow rowCF)
        raw.family.bodyFamily := by
    exact centeredPlankLongTubeActualDatum_isKatzTao
      Drow hlongHalf hrowFrostman
  have hnormalizedFrostman :
      IsFrostmanIn
        (eighthNormalizedKatzTaoAmbientFrostmanConstant
          (plankLongTubeGlobalKatzTaoConstant Drow rowCF) raw)
        normalized.family.bodyFamily unitBallBody := by
    exact eighthNormalizedDatum_isFrostmanIn_of_isKatzTao
      raw hlongPos hlongHalf
        (centeredPlankLongTubeActualDatum_B2 Drow hlongHalf)
        hrawKatzTao
  have hnormalizedMass0 :
      containedMass normalized.family.bodyFamily unitBallBody ≠ 0 := by
    rw [containedMass_eq_familyVolume_of_contained
      normalized.family.bodyFamily unitBallBody hnormalizedFrostman.1]
    exact (actualDatum_familyVolume_pos_of_scale normalized
      (div_pos hlongPos (by norm_num))).ne'
  have hcanonical :
      sourceCanonicalFrostmanConstant normalized ≤
        eighthNormalizedKatzTaoAmbientFrostmanConstant
          (plankLongTubeGlobalKatzTaoConstant Drow rowCF) raw := by
    unfold sourceCanonicalFrostmanConstant
    exact canonicalFrostmanConstant_le_of_isFrostmanIn
      hnormalizedFrostman hnormalizedMass0

  have hrawFamilyVolume :
      familyVolume raw.family.bodyFamily =
        familyVolume (plankLongTubeCoverFamily Drow).bodyFamily := by
    let motion : Unit → RigidMotion := fun _ ↦
      translationRigidMotion (-(ambientPlankCertificate Drow).box.center)
    have hcopy :
        familyVolume
            (indexedRigidCopyTubeFamily motion
              (plankLongTubeActualDatum Drow).family).bodyFamily =
          (Fintype.card Unit : ENNReal) *
            familyVolume (plankLongTubeActualDatum Drow).family.bodyFamily :=
      indexedRigidCopyTubeFamily_familyVolume motion
        (plankLongTubeActualDatum Drow).family
    simpa only [raw, centeredPlankLongTubeActualDatum,
      indexedRigidCopyDatum, motion, plankLongTubeActualDatum,
      Fintype.card_unit, Nat.cast_one, one_mul] using hcopy
  have hrawAmbientDensity :
      ambientFamilyVolumeDensity raw.family.bodyFamily ambient =
        ambientFamilyVolumeDensity
          (plankLongTubeCoverFamily Drow).bodyFamily ambient := by
    unfold ambientFamilyVolumeDensity
    rw [hrawFamilyVolume]
  have hglobalConstant :
      plankLongTubeGlobalKatzTaoConstant Drow rowCF =
        (plankLongTubeFrostmanCopyLoss
            Drow.comparisonConstant short long *
          (plankLongTubeThickenedAmbientLoss Drow * rowCF)) *
            ambientFamilyVolumeDensity raw.family.bodyFamily ambient := by
    unfold plankLongTubeGlobalKatzTaoConstant
    rw [hrawAmbientDensity]

  have hambient0 : volume (ambient : Set Space) ≠ 0 := by
    simpa only [ambient] using
      closedThickening_sourceAmbient_volume_ne_zero Drow
  have hambientTop : volume (ambient : Set Space) ≠ ∞ := by
    simpa only [ambient] using
      closedThickening_sourceAmbient_volume_ne_top Drow
  have hnormalizedConstant :
      eighthNormalizedKatzTaoAmbientFrostmanConstant
          (plankLongTubeGlobalKatzTaoConstant Drow rowCF) raw ≤
        (65536 *
          (plankLongTubeFrostmanCopyLoss
              Drow.comparisonConstant short long *
            (plankLongTubeThickenedAmbientLoss Drow * rowCF))) *
          volume (unitBallBody : Set Space) /
            volume (ambient : Set Space) := by
    rw [hglobalConstant]
    exact
      eighthNormalizedKatzTaoAmbientFrostmanConstant_ambientDensity_le
        raw ambient
          (plankLongTubeFrostmanCopyLoss
              Drow.comparisonConstant short long *
            (plankLongTubeThickenedAmbientLoss Drow * rowCF))
          hlongPos

  have hscalar :
      (65536 *
          (plankLongTubeFrostmanCopyLoss
              Drow.comparisonConstant short long *
            (plankLongTubeThickenedAmbientLoss Drow * rowCF))) *
          volume (unitBallBody : Set Space) /
            volume (ambient : Set Space) =
        plankLongTubeCanonicalFrostmanComparisonLoss Drow * rowCF := by
    let V : ENNReal := volume (ambient : Set Space)
    let W : ENNReal := volume (Drow.ambient : Set Space)
    let U : ENNReal := volume (unitBallBody : Set Space)
    let copyLoss : ENNReal :=
      plankLongTubeFrostmanCopyLoss Drow.comparisonConstant short long
    have hV0 : V ≠ 0 := by simpa only [V] using hambient0
    have hVTop : V ≠ ∞ := by simpa only [V] using hambientTop
    have hVcancel : V * V⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hV0 hVTop
    change
      (65536 * (copyLoss * ((V / W) * rowCF))) * U / V =
        ((65536 * copyLoss) * U / W) * rowCF
    simp only [div_eq_mul_inv]
    calc
      (65536 * (copyLoss * (V * W⁻¹ * rowCF))) * U * V⁻¹ =
          (((65536 * copyLoss) * U * W⁻¹) * rowCF) *
            (V * V⁻¹) := by
        ac_rfl
      _ = ((65536 * copyLoss) * U * W⁻¹) * rowCF := by
        rw [hVcancel, mul_one]

  change sourceCanonicalFrostmanConstant normalized ≤
    plankLongTubeCanonicalFrostmanComparisonLoss Drow * rowCF
  calc
    sourceCanonicalFrostmanConstant normalized ≤
        eighthNormalizedKatzTaoAmbientFrostmanConstant
          (plankLongTubeGlobalKatzTaoConstant Drow rowCF) raw := hcanonical
    _ ≤ (65536 *
          (plankLongTubeFrostmanCopyLoss
              Drow.comparisonConstant short long *
            (plankLongTubeThickenedAmbientLoss Drow * rowCF))) *
          volume (unitBallBody : Set Space) /
            volume (ambient : Set Space) := hnormalizedConstant
    _ = plankLongTubeCanonicalFrostmanComparisonLoss Drow * rowCF := hscalar

/-- The exact row Frostman envelope bounds the canonical Frostman constant
of the genuine centered and eighth-normalized long-tube source, with only
the explicit geometric loss above.  The all-row source and retention data are
used only to construct the single row-local Frostman premise of the core. -/
theorem sourceCanonicalFrostmanConstant_normalizedRowLongTubeSource_le
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex)
    {restrictionLoss sourceCF : ENNReal}
    (hsource : IsFrostmanIn sourceCF
      (heavyRetainedOwnerThickenedFamily D C q) P.sourceAmbient)
    (Hretention : FixedThetaAllSlabRowRestrictionLossCertificate
      P restrictionLoss)
    (hlongHalf : P.longWidth r ≤ (2 : NNReal)⁻¹) :
    sourceCanonicalFrostmanConstant
        (eighthNormalizedDatum (normalizedRowLongTubeSource P r)) ≤
      normalizedRowLongTubeCanonicalFrostmanLoss P r *
        P.rowFrostmanEnvelopeWithRestrictionLoss
          restrictionLoss sourceCF r := by
  obtain ⟨s, hs⟩ := R.rowOwners_nonempty r
  let _ : Nonempty {s // s ∈ R.rowOwners r} := ⟨⟨s, hs⟩⟩
  have hrowFrostman :
      IsFrostmanIn
        (P.rowFrostmanEnvelopeWithRestrictionLoss
          restrictionLoss sourceCF r)
        (P.normalizedRowDatum r).family
        (P.normalizedRowDatum r).ambient :=
    P.normalizedRows_isFrostmanIn_withRestrictionLoss
      hsource Hretention r
  rw [normalizedRowLongTubeCanonicalFrostmanLoss_eq]
  exact sourceCanonicalFrostmanConstant_eighthCenteredLongTube_le
    (P.normalizedRowDatum r)
      (P.rowFrostmanEnvelopeWithRestrictionLoss
        restrictionLoss sourceCF r)
      hrowFrostman hlongHalf

#print axioms
  sourceCanonicalFrostmanConstant_eighthCenteredLongTube_le
#print axioms
  sourceCanonicalFrostmanConstant_normalizedRowLongTubeSource_le

end
end Family8NormalizedRowLongTubeCanonicalFrostmanComparisonV1
