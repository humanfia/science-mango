import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostMassDatumV2
import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
import Family8Grounding.Family8MassRetainingNormalizedSelectedKatzTaoEndpointV4
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family6AffineConvexVolumeCoreV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8MassRetainingNormalizedSelectedKatzTaoEndpointV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Same-selected weighted fresh Katz--Tao endpoint for the centered proxy

The centered half-post datum has honest B2 support. A global source
Katz--Tao condition supplies its raw proxy constant, the fixed conflict cap
selects a mass-retaining pairwise subtype, and the parameter property is
applied to that literal same subtype. There is no second selection.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_centeredHalfPost_massFresh_apply_katzTaoAtParameters
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (s : NNReal) (hs : 0 < s) (hsHalf : s ≤ (2 : NNReal)⁻¹)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real))
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hglobalKT : IsKatzTao C fine.bodyFamily)
    (hdelta0 : s / 8 ≤ delta0)
    (hdensityBudget :
      let D := centeredHalfPostSelectedPlankFineMassDatum
        s Y e S B hrho label hplank W hradius
      let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C
      let loss := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1
      (((s / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (loss : ENNReal)) ≤ D.shading.shadingDensity)
    (hcoefficient :
      let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C
      128 * Cproxy ≤ ((s / 8 : NNReal) : ENNReal) ^ (-eta)) :
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
  dsimp only at hdensityBudget hcoefficient ⊢
  let D := centeredHalfPostSelectedPlankFineMassDatum
    s Y e S B hrho label hplank W hradius
  let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
    s e S B hrho label hplank W C
  let threshold := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal)
  let loss := threshold + 1
  have hfiberNonempty : (S.fiber W.1.1.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ :=
      S.parent_surjective W.1.1.1 W.1.1.2
    exact ⟨i, (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩⟩
  let _ : Nonempty (SelectedPlankFineIndex S W) :=
    Finset.nonempty_coe_sort.mpr hfiberNonempty
  have hrawKT : IsKatzTao Cproxy D.family.bodyFamily := by
    simpa only [D, Cproxy,
      centeredHalfPostSelectedPlankFineMassDatum_family] using
        centeredHalfPostSelectedPlankFineProxyFamily_isKatzTao_of_global
          s e S B hrho label hplank W hdeltaPos hdeltaHalf hsHalf
            hglobalKT hradius
  have hratioTop : affineAxisProxyVolumeRatio delta s ≠ ∞ := by
    unfold affineAxisProxyVolumeRatio
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdeltaPos.ne'), by norm_num⟩
  have hCproxyfinite : Cproxy ≠ ∞ := by
    dsimp only [Cproxy,
      centeredHalfPostSelectedPlankFineProxyKatzTaoConstant,
      selectedPlankFineProxyKatzTaoConstant]
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top hratioTop hCfinite
    · exact (affineJacobian_pos
        (centeredHalfPostBucketAffineEquiv
          e S B hrho label hplank W)).ne'
  have hconflict : ∀ i,
      (normalizedConflictIndices D i).card ≤ threshold := by
    intro i
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      D hs hsHalf hCproxyfinite hrawKT i
  obtain ⟨selected, hselected, hpair, hcard, hmass⟩ :=
    exists_normalized_greedyRefinement D hconflict
  have hB2 : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2 := by
    intro i
    simpa only [D, centeredHalfPostSelectedPlankFineMassDatum_family] using
      centeredHalfPostSelectedPlankFineProxyFamily_carrier_subset_B2
        s e S B hrho label hplank W hsHalf i
  have hlossPos : 0 < loss := by
    dsimp only [loss]
    omega
  have hsame :=
    apply_katzTaoAtParameters_to_massRetaining_normalizedSelected
      hKTP D hs hsHalf hB2 selected hselected hpair loss hlossPos hmass
        hrawKT hdelta0 hdensityBudget hcoefficient
  rcases hsame with
    ⟨_hselectedAgain, hadmissible, hhyp, hselectedBound, hDBound⟩
  have hselectedKT : IsKatzTao (128 * Cproxy)
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).family.bodyFamily :=
    restrict_eighthNormalizedDatum_isKatzTao D hsHalf selected hrawKT
  have hsourceBound :
      (selectedPlankFineSourceShading
        Y e S B hrho label W).averageMultiplicity ≤
          (loss : ENNReal) *
            katzTaoMultiplicityRHS (s / 8) selected.card epsilon beta := by
    rw [← centeredHalfPostSelectedPlankFineMassShading_averageMultiplicity
      s Y e S B hrho label hplank W hradius]
    simpa only [D, centeredHalfPostSelectedPlankFineMassDatum] using hDBound
  exact ⟨selected, hselected, hadmissible, hcard, hmass, hselectedKT,
    hhyp, hselectedBound, hsourceBound⟩

#print axioms exists_centeredHalfPost_massFresh_apply_katzTaoAtParameters

end
end Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV2
