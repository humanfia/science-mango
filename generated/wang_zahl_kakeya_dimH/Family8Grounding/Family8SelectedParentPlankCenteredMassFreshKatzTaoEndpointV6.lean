import Family8Grounding.Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV2
import Family8Grounding.Family8MassRetainingNormalizedSelectedKatzTaoGenericPowerBudgetsV3
import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8MassRetainingNormalizedSelectedKatzTaoGenericPowerBudgetsV3
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
open Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV2
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Power-budgeted actual centered selected-parent endpoint

One positive threshold simultaneously enforces the terminal scale, B2 scale,
and both finite-constant absorption thresholds. The operator-norm callback is
replaced by the explicit winning-block radius inequality.
-/

def centeredMassFreshKatzTaoThreshold
    (delta0 : NNReal)
    (densityAbsorbEta coefficientAbsorbEta : Real) : NNReal :=
  min (8 * delta0)
    (min (2 : NNReal)⁻¹
      (massRetainingNormalizedSelectedScalarThreshold
        densityAbsorbEta coefficientAbsorbEta))

theorem centeredMassFreshKatzTaoThreshold_pos
    {delta0 : NNReal} (hdelta0 : 0 < delta0)
    (densityAbsorbEta coefficientAbsorbEta : Real) :
    0 < centeredMassFreshKatzTaoThreshold
      delta0 densityAbsorbEta coefficientAbsorbEta := by
  rw [centeredMassFreshKatzTaoThreshold, lt_min_iff, lt_min_iff]
  exact ⟨mul_pos (by norm_num) hdelta0, by norm_num,
    massRetainingNormalizedSelectedScalarThreshold_pos _ _⟩

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_centeredHalfPost_massFresh_apply_katzTaoAtParameters_of_power
    {beta epsilon eta lossEta sourceEta coefficientEta
      densityAbsorbEta coefficientAbsorbEta : Real}
    {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (_hdelta0Pos : 0 < delta0)
    (Y : Shading fine.bodyFamily)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (B : Finset (ActiveParentIndex S)) (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S B hrho label})
    (s : NNReal) (hs : 0 < s)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hscalarRadius :
      ((1 / 2 : Real) *
        (3 * (r : Real) /
          ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
            (delta : Real) ≤ (s : Real))
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hglobalKT : IsKatzTao C fine.bodyFamily)
    (heta : 0 ≤ eta)
    (hlossPower :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C
      let loss := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1
      (loss : ENNReal) ≤ (s : ENNReal) ^ (-lossEta))
    (hsourceDensity :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let hradius := selectedParent_centeredHalfPost_radius_budget
        S hrho P k r hr label B hplank W s hscalarRadius
      let D := centeredHalfPostSelectedPlankFineMassDatum
        s Y e S B hrho label hplank W hradius
      (s : ENNReal) ^ sourceEta ≤ D.shading.shadingDensity)
    (hCproxyPower :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C
      Cproxy ≤ (s : ENNReal) ^ (-coefficientEta))
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hsmall : s ≤ centeredMassFreshKatzTaoThreshold
      delta0 densityAbsorbEta coefficientAbsorbEta)
    (hdensityExponent :
      sourceEta + lossEta + densityAbsorbEta ≤ eta)
    (hcoefficientExponent :
      coefficientEta + coefficientAbsorbEta ≤ eta) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let hradius := selectedParent_centeredHalfPost_radius_budget
      S hrho P k r hr label B hplank W s hscalarRadius
    let D := centeredHalfPostSelectedPlankFineMassDatum
      s Y e S B hrho label hplank W hradius
    let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e S B hrho label hplank W C
    let threshold := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal)
    let loss := threshold + 1
    ∃ selected : Finset (SelectedPlankFineIndex S W),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
        (loss : ENNReal) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass ≤
        (loss : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass ∧
      IsKatzTao (128 * Cproxy)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      KatzTaoHypotheses
        (restrictActualTubeDatum (eighthNormalizedDatum D) selected) eta ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).shading.averageMultiplicity ≤
          katzTaoMultiplicityRHS (s / 8) selected.card epsilon beta ∧
      (selectedPlankFineSourceShading
        Y e S B hrho label W).averageMultiplicity ≤
          (loss : ENNReal) *
            katzTaoMultiplicityRHS (s / 8) selected.card epsilon beta := by
  dsimp only at hlossPower hsourceDensity hCproxyPower ⊢
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let hradius := selectedParent_centeredHalfPost_radius_budget
    S hrho P k r hr label B hplank W s hscalarRadius
  let D := centeredHalfPostSelectedPlankFineMassDatum
    s Y e S B hrho label hplank W hradius
  let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
    s e S B hrho label hplank W C
  let threshold := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal)
  let loss := threshold + 1
  have hsEight : s ≤ 8 * delta0 :=
    hsmall.trans (min_le_left _ _)
  have hsHalf : s ≤ (2 : NNReal)⁻¹ :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsOne : s ≤ 1 := hsHalf.trans (by norm_num)
  have hsmallScalar : s ≤
      massRetainingNormalizedSelectedScalarThreshold
        densityAbsorbEta coefficientAbsorbEta :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hterminal : s / 8 ≤ delta0 := by
    apply (div_le_iff₀ (by norm_num : (0 : NNReal) < 8)).2
    simpa only [mul_comm] using hsEight
  have hbudgets := normalizedSelected_scalar_budgets_of_power
    hs hsOne heta hlossPower hsourceDensity hCproxyPower
      hdensityAbsorbEta hcoefficientAbsorbEta hsmallScalar
        hdensityExponent hcoefficientExponent
  exact exists_centeredHalfPost_massFresh_apply_katzTaoAtParameters
    hKTP Y e S B hrho label hplank W s hs hsHalf hdeltaPos hdeltaHalf
      hradius hCfinite hglobalKT hterminal hbudgets.1 hbudgets.2

#print axioms centeredMassFreshKatzTaoThreshold_pos
#print axioms
  exists_centeredHalfPost_massFresh_apply_katzTaoAtParameters_of_power

end
end Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV6
