import Family8Grounding.Family8StickyScaleCoverSelectedFiberAmbientMassRetentionV3
import Family8Grounding.Family8StickyFiberContractedJohnNormalizedFreshClosedLossV1
import Family8Grounding.Family8StickySelectedFiberLowCFScalarEnvelopeV4
import Mathlib.Tactic

/-!
# Genuine fresh retention on a fixed low-CF Sticky parent, V2

V1 omitted two namespaces and left two elementary ENNReal reorderings implicit.  This corrected successor first uses the low-CF certificate on the full prescribed fibre, so there
is no circular dependence on a later selected subtype.  It gives full-fibre
Katz--Tao control, which is transported to the genuine contracted-John proxy
and fed to the actual normalized fresh selector.  The selected cardinality
then bounds the full low-CF source constant, allowing the selector's literal
loss to be enlarged to the card-envelope loss used by the strict middle
consumer.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFFreshRetentionProducerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnAffineJacobianLowerV3
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnGlobalNormalizedFreshV1
open Family8StickyFiberContractedJohnNormalizedFreshClosedLossV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickyScaleCoverSelectedFiberAmbientMassRetentionV3
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Full-fibre source Katz--Tao constant furnished by the low-CF ambient
certificate at the prescribed parent. -/
def selectedParentLowCFFullSourceConstant
    (S : StickyScaleCover fine rho)
    (q : {q // q ∈ S.activeCoarse}) (lower : ENNReal) : ENNReal :=
  lower * ambientFamilyVolumeDensity
    (S.fiberFamily q.1) (S.activeCoarseFamily q)

/-- Corresponding genuine contracted-John proxy Katz--Tao constant. -/
def selectedParentLowCFFullProxyConstant
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (q : {q // q ∈ S.activeCoarse})
    (lower : ENNReal) : ENNReal :=
  stickyFiberContractedJohnProxyKatzTaoConstant S hrho hrhoOne q
    (selectedParentLowCFFullSourceConstant S q lower)

/-- Literal ceiling-free loss of the genuine normalized fresh selector. -/
def selectedParentLowCFFreshLoss
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (q : {q // q ∈ S.activeCoarse})
    (lower : ENNReal) : ENNReal :=
  480000 *
      (128 * selectedParentLowCFFullProxyConstant
        S hrho hrhoOne q lower) + 2

/-- The genuine fresh selector supplies all retention fields required by the
strict low-CF middle consumer, enlarged to its literal card-envelope loss. -/
theorem exists_lowCF_fresh_selected_cardEnvelope_retention
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower : ENNReal} (hlowerTop : lower ≠ ∞)
    (hLow : IsFrostmanIn lower
      (S.fiberFamily q.1) (S.activeCoarseFamily q)) :
    ∃ selected : Finset {i // i ∈ S.fiber q.1},
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne q)) selected).IsAdmissible ∧
      selectedParentLowCFFreshLoss S hrho hrhoOne q lower ≠ ∞ ∧
      IsFrostmanIn
        (lower *
          (16 * selectedParentLowCFFreshLoss S hrho hrhoOne q lower))
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q) ∧
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower
              (selectedParentLowCFFreshLoss S hrho hrhoOne q lower)) *
          (selected.card : ENNReal) ∧
      (eighthNormalizedDatum
        (stickyFiberContractedJohnProxyDatum
          S Y hrho hrhoOne q)).shading.shadingMass ≤
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower
              (selectedParentLowCFFreshLoss S hrho hrhoOne q lower)) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne q)) selected).shading.shadingMass := by
  let sourceC := selectedParentLowCFFullSourceConstant S q lower
  let proxyC := selectedParentLowCFFullProxyConstant
    S hrho hrhoOne q lower
  let freshLoss := selectedParentLowCFFreshLoss
    S hrho hrhoOne q lower
  have hparent0 : volume (S.activeCoarseFamily q : Set Space) ≠ 0 := by
    change volume (S.coarse.tubes q.1).carrier ≠ 0
    exact (Tube.volume_pos (S.coarse.tubes q.1) hrho).ne'
  have hparentTop : volume (S.activeCoarseFamily q : Set Space) ≠ ∞ :=
    (S.activeCoarseFamily q).isCompact.measure_lt_top.ne
  have hsourceKT : IsKatzTao sourceC (S.fiberFamily q.1) := by
    simpa only [sourceC, selectedParentLowCFFullSourceConstant] using
      (isKatzTao_of_isFrostmanIn_familyVolumeDensity
        hLow hparent0 hparentTop)
  have hsourceCTop : sourceC ≠ ∞ := by
    dsimp only [sourceC, selectedParentLowCFFullSourceConstant]
    exact ENNReal.mul_ne_top hlowerTop
      (ambientFamilyVolumeDensity_ne_top
        (S.fiberFamily q.1) (S.activeCoarseFamily q) hparent0)
  have hproxyKT : IsKatzTao proxyC
      (stickyFiberContractedJohnProxyDatum
        S Y hrho hrhoOne q).family.bodyFamily := by
    change IsKatzTao proxyC
      (stickyFiberContractedJohnProxyFamily
        S hrho hrhoOne q).bodyFamily
    simpa only [proxyC, selectedParentLowCFFullProxyConstant] using
      (stickyFiberContractedJohnProxyFamily_isKatzTao
        S hrho hrhoOne hdelta hdeltaHalf hdeltaRho q hsourceKT)
  have hproxyCTop : proxyC ≠ ∞ := by
    simpa only [proxyC, selectedParentLowCFFullProxyConstant] using
      (stickyFiberContractedJohnProxyKatzTaoConstant_ne_top
        S hrho hrhoOne hdelta q hsourceCTop)
  obtain ⟨selected, hselected, hadmissible, hcard0, hmass0,
      _hselectedKT, _haverage⟩ :=
    exists_stickyFiberContractedJohn_normalizedFresh_closedLoss_of_isKatzTao
      S Y hdelta hrho hrhoOne hdeltaRho q hproxyCTop hproxyKT
  have hfreshTop : freshLoss ≠ ∞ := by
    dsimp only [freshLoss, selectedParentLowCFFreshLoss]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) hproxyCTop), by norm_num⟩
  have hcardFresh :
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
        freshLoss * (selected.card : ENNReal) := by
    simpa only [freshLoss, selectedParentLowCFFreshLoss, proxyC,
      selectedParentLowCFFullProxyConstant] using hcard0
  have hmassFresh :
      (eighthNormalizedDatum
        (stickyFiberContractedJohnProxyDatum
          S Y hrho hrhoOne q)).shading.shadingMass ≤
        freshLoss *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne q)) selected).shading.shadingMass := by
    simpa only [freshLoss, selectedParentLowCFFreshLoss, proxyC,
      selectedParentLowCFFullProxyConstant] using hmass0
  have hLowSelected : IsFrostmanIn (lower * (16 * freshLoss))
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q) :=
    lowCF_isFrostmanIn_selected_of_card_retention
      S hdeltaHalf q selected hLow hcardFresh
  have hdensityCard :
      ambientFamilyVolumeDensity
          (S.fiberFamily q.1) (S.activeCoarseFamily q) ≤
        (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) := by
    apply ambientFamilyVolumeDensity_le_card
    · intro i
      exact fiberFamily_subset_parent S q i
    · exact hparent0
  have hsourceCEnvelope : sourceC ≤
      selectedFiberLowCFCardEnvelope S q selected lower freshLoss := by
    calc
      sourceC ≤ lower *
          (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) := by
        dsimp only [sourceC, selectedParentLowCFFullSourceConstant]
        exact mul_le_mul' le_rfl hdensityCard
      _ ≤ lower * (freshLoss * (selected.card : ENNReal)) :=
        mul_le_mul' le_rfl hcardFresh
      _ ≤ selectedFiberLowCFCardEnvelope
          S q selected lower freshLoss := by
        unfold selectedFiberLowCFCardEnvelope
        calc
          lower * (freshLoss * (selected.card : ENNReal)) ≤
              lower * ((16 * freshLoss) *
                (selected.card : ENNReal)) := by
            apply mul_le_mul' le_rfl
            apply mul_le_mul' ?_ le_rfl
            calc
              freshLoss = 1 * freshLoss := (one_mul _).symm
              _ ≤ 16 * freshLoss := mul_le_mul' (by norm_num) le_rfl
          _ = (lower * (16 * freshLoss)) *
              (selected.card : ENNReal) := by ring
  have hproxyEnvelope : proxyC ≤
      93312 * selectedFiberLowCFCardEnvelope
        S q selected lower freshLoss := by
    calc
      proxyC ≤ 93312 * sourceC := by
        simpa only [proxyC, selectedParentLowCFFullProxyConstant] using
          (stickyFiberContractedJohnProxyKatzTaoConstant_le_fixed
            S hdelta hrho hrhoOne q sourceC)
      _ ≤ 93312 * selectedFiberLowCFCardEnvelope
          S q selected lower freshLoss := mul_le_mul' le_rfl hsourceCEnvelope
  have hfreshLeCardLoss : freshLoss ≤
      stickyFiberContractedJohnSourceClosedLoss
        (selectedFiberLowCFCardEnvelope S q selected lower freshLoss) := by
    dsimp only [freshLoss, selectedParentLowCFFreshLoss]
    unfold stickyFiberContractedJohnSourceClosedLoss
    exact add_le_add
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hproxyEnvelope)) le_rfl
  refine ⟨selected, hselected, hadmissible, ?_, ?_, ?_, ?_⟩
  · simpa only [freshLoss] using hfreshTop
  · simpa only [freshLoss] using hLowSelected
  · exact hcardFresh.trans (mul_le_mul' hfreshLeCardLoss le_rfl)
  · exact hmassFresh.trans (mul_le_mul' hfreshLeCardLoss le_rfl)

#print axioms selectedParentLowCFFullSourceConstant
#print axioms selectedParentLowCFFullProxyConstant
#print axioms selectedParentLowCFFreshLoss
#print axioms exists_lowCF_fresh_selected_cardEnvelope_retention

end
end Family8StickySelectedFiberLowCFFreshRetentionProducerV2
