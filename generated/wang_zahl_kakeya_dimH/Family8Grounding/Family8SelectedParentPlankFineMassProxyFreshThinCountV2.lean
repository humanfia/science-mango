import Family8Grounding.Family8SelectedParentPlankFineMassProxyFreshSelectionV2
import Family8Grounding.Family8SelectedParentPlankFreshPairwisePackingV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankFineMassProxyFreshThinCountV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineMassProxyFreshSelectionV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFreshPairwisePackingV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Same selected mass-retaining fresh fibre with thin-plank count

The mass-aware greedy theorem and the five-parameter packing theorem are
composed on the literal same selected finset.  Thus the output simultaneously
retains the actual source-fibre average and bounds the selected cardinality;
there is no second empty-shading selection hidden in this connector.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_selectedPlankFine_massProxy_normalizedFresh_with_thinCount
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
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real))
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (selectedPlankFineProxyDatum s e S B hrho label W).family.bodyFamily)
    (R : Real) (hR : 0 ≤ R)
    (ell : SelectedPlankFineIndex S W → Real)
    (hellNorm : ∀ i,
      ell i ≤ ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖)
    (hvector0 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤ ell i * ((s : Real) / 8))
    (hvector1 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤
        ell i * (R * ((s : Real) / 8)))
    (haScale : bucketShortA label ≤ s)
    (hbScale : (bucketShortB label : Real) ≤ R * (s : Real))
    (hsmall : s / 8 ≤ (1 / 100 : NNReal))
    (hthin :
      ((s / 8 : NNReal) : Real) ^ 2 +
        (R * ((s / 8 : NNReal) : Real)) ^ 2 ≤ (3 : Real) / 4) :
    let D := selectedPlankFineMassProxyDatum
      s Y e S B hrho label W haxisLength hradius
    let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
    ∃ selected : Finset (SelectedPlankFineIndex S W),
      selected.Nonempty ∧
      Set.Pairwise (selected : Set (SelectedPlankFineIndex S W))
        (fun i j => EssentiallyDistinct
          ((eighthNormalizedDatum D).family.tubes i)
          ((eighthNormalizedDatum D).family.tubes j)) ∧
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      (selectedPlankFineSourceShading
          Y e S B hrho label W).averageMultiplicity ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.averageMultiplicity ∧
      ((threshold + 1 : Nat) : ENNReal) ≤ 480000 * (128 * C) + 2 ∧
      selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  dsimp only
  let D := selectedPlankFineMassProxyDatum
    s Y e S B hrho label W haxisLength hradius
  let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
  obtain ⟨selected, hselected, hpair, hcard, hmass, hselectedKT,
      havgSource, hloss⟩ :=
    exists_selectedPlankFine_massProxy_normalizedFresh_of_isKatzTao
      Y e S B hrho label W s hs hsHalf haxisLength hradius hCfinite hKT
  refine ⟨selected, hselected, hpair, hcard, hmass, hselectedKT,
    havgSource, hloss, ?_⟩
  have hpairGeometry :
      Set.Pairwise (selected : Set (SelectedPlankFineIndex S W))
        (fun i j => EssentiallyDistinct
          ((eighthNormalizedDatum
            (selectedPlankFineProxyDatum s e S B hrho label W)).family.tubes i)
          ((eighthNormalizedDatum
            (selectedPlankFineProxyDatum s e S B hrho label W)).family.tubes j)) := by
    intro i hi j hj hij
    have hp := hpair hi hj hij
    simpa only [D, eighthNormalizedDatum_family,
      eighthNormalizedTubeFamily_tubes,
      selectedPlankFineMassProxyDatum_family,
      selectedPlankFineProxyFamily_tubes,
      selectedPlankFineProxyDatum_family_tubes] using hp
  exact
    normalizedFreshSelectedPlankFine_card_le_fiveParameterCap_of_pairwise
      e S B hrho label hplank W s hs selected hpairGeometry R hR ell
        hellNorm hvector0 hvector1 haScale hbScale hsmall hthin

#print axioms
  exists_selectedPlankFine_massProxy_normalizedFresh_with_thinCount

end
end Family8SelectedParentPlankFineMassProxyFreshThinCountV2
