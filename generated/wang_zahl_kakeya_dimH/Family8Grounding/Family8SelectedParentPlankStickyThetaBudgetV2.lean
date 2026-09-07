import Family8Grounding.Family8SelectedParentPlankStickyDirectionTransportV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8SelectedParentPlankStickyThetaBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFreshFiveParameterPackingV3
open Family8SelectedParentPlankStickyDirectionTransportV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Automatic same-parent vector envelope

For a fine tube assigned to a selected parent, each short raw coordinate has
two independent rigorous estimates. Literal membership in the selected plank
gives `a` or `b`; Sticky carrier containment gives a direction error, and the
common affine map transports it with its explicit operator norm. Their minimum
is the strongest callback-free estimate available from these structures.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def selectedPlankFineShortEnvelope
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (j : Fin 2) : Real :=
  let frame := (chosenPlankCertificate hplank W).box.frame
  let parent := S.coarse.tubes W.1.1.1
  let side : Fin 2 → Real := ![(bucketShortA label : Real),
    (bucketShortB label : Real)]
  min (side j)
    (|⟪frame j.castSucc,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          parent⟫_Real| +
      affineLinearOpNorm (bucketNormalizedAffineEquiv e label) *
        (14 * (rho : Real)))

/-- Literal plank containment and Sticky direction transport combine into the
minimum envelope, with no asserted invariance under an anisotropic map. -/
theorem selectedPlankFine_rawVector_chosenFrame_le_shortEnvelope
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    |⟪(chosenPlankCertificate hplank W).box.frame 0,
      affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)⟫_Real| ≤
      selectedPlankFineShortEnvelope e S B hrho label hplank W 0 ∧
    |⟪(chosenPlankCertificate hplank W).box.frame 1,
      affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)⟫_Real| ≤
      selectedPlankFineShortEnvelope e S B hrho label hplank W 1 := by
  have hside := selectedPlankFine_rawVector_chosenFrame_bounds
    e S B hrho label hplank W i
  have hop0 := selectedPlankFine_rawVector_coord_le_parent_add_opNorm
    e S B hrho label W i (chosenPlankCertificate hplank W).box.frame 0
  have hop1 := selectedPlankFine_rawVector_coord_le_parent_add_opNorm
    e S B hrho label W i (chosenPlankCertificate hplank W).box.frame 1
  constructor
  · apply le_min hside.1
    simpa only [selectedPlankFineShortEnvelope, Matrix.cons_val_zero,
      Matrix.head_cons, Fin.castSucc_zero] using hop0
  · apply le_min hside.2
    simpa only [selectedPlankFineShortEnvelope, Matrix.cons_val_one,
      Matrix.tail_cons, Matrix.head_cons, Fin.castSucc_one] using hop1

/-- Scalar domination of the automatic envelopes is exactly sufficient for
the two theta-thin raw-vector estimates, using the actual mapped-axis norm. -/
theorem selectedPlankFine_thetaThin_rawVector_bounds_of_shortEnvelope
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (s : NNReal) (R : Real)
    (hbudget0 : ∀ i : SelectedPlankFineIndex S W,
      selectedPlankFineShortEnvelope e S B hrho label hplank W 0 ≤
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)‖ * ((s : Real) / 8))
    (hbudget1 : ∀ i : SelectedPlankFineIndex S W,
      selectedPlankFineShortEnvelope e S B hrho label hplank W 1 ≤
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)‖ * (R * ((s : Real) / 8))) :
    (∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)‖ * ((s : Real) / 8)) ∧
    (∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)‖ * (R * ((s : Real) / 8))) := by
  constructor
  · intro i
    exact (selectedPlankFine_rawVector_chosenFrame_le_shortEnvelope
      e S B hrho label hplank W i).1.trans (hbudget0 i)
  · intro i
    exact (selectedPlankFine_rawVector_chosenFrame_le_shortEnvelope
      e S B hrho label hplank W i).2.trans (hbudget1 i)

/-- Direct consumer for the fresh five-parameter endpoint. There is no vector
callback and no auxiliary length callback; only the two explicit scalar
envelope budgets remain. -/
theorem normalizedFreshSelectedPlankFine_card_le_fiveParameterCap_of_shortEnvelope
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (s : NNReal) (hs : 0 < s)
    (selected : Finset (SelectedPlankFineIndex S W))
    (hselectedAdmissible :
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (selectedPlankFineProxyDatum s e S B hrho label W))
        selected).IsAdmissible)
    (R : Real) (hR : 0 ≤ R)
    (hbudget0 : ∀ i : SelectedPlankFineIndex S W,
      selectedPlankFineShortEnvelope e S B hrho label hplank W 0 ≤
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)‖ * ((s : Real) / 8))
    (hbudget1 : ∀ i : SelectedPlankFineIndex S W,
      selectedPlankFineShortEnvelope e S B hrho label hplank W 1 ≤
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)‖ * (R * ((s : Real) / 8)))
    (haScale : bucketShortA label ≤ s)
    (hbScale : (bucketShortB label : Real) ≤ R * (s : Real))
    (hsmall : s / 8 ≤ (1 / 100 : NNReal))
    (hthin :
      ((s / 8 : NNReal) : Real) ^ 2 +
        (R * ((s / 8 : NNReal) : Real)) ^ 2 ≤ (3 : Real) / 4) :
    selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  have hvectors :=
    selectedPlankFine_thetaThin_rawVector_bounds_of_shortEnvelope
      e S B hrho label hplank W s R hbudget0 hbudget1
  apply normalizedFreshSelectedPlankFine_card_le_fiveParameterCap
    e S B hrho label hplank W s hs selected hselectedAdmissible R hR
    (fun i => ‖affineImageAxisVector
      (bucketNormalizedAffineEquiv e label) (fine.tubes i.1)‖)
  · intro i
    exact le_rfl
  · exact hvectors.1
  · exact hvectors.2
  · exact haScale
  · exact hbScale
  · exact hsmall
  · exact hthin

#print axioms selectedPlankFine_rawVector_chosenFrame_le_shortEnvelope
#print axioms selectedPlankFine_thetaThin_rawVector_bounds_of_shortEnvelope
#print axioms
  normalizedFreshSelectedPlankFine_card_le_fiveParameterCap_of_shortEnvelope

end
end Family8SelectedParentPlankStickyThetaBudgetV2
