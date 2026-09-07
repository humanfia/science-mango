import Family8Grounding.Family8SelectedParentPlankFineProxyDatumV1
import Family8Grounding.Family8NormalizedSelectedContractedJohnFiveParameterPackingV2
import Family8Grounding.Family8ThinPlankFiveParameterMidpointDirectionPackingV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8SelectedParentPlankFreshFiveParameterPackingV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnProxyFiveParameterPackingV2
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8NormalizedSelectedContractedJohnFiveParameterPackingV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyDatumV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterMidpointDirectionPackingV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem tubeAxisMidpoint_affineAxisProxyTube
    (s : NNReal) (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    Family8CommonPointTubePackingV1.tubeAxisMidpoint
        (affineAxisProxyTube s e T) = affineImageAxisCenter e T := by
  unfold Family8CommonPointTubePackingV1.tubeAxisMidpoint
    affineAxisProxyTube affineImageUnitExtensionAxis
  simp only
  module

@[simp] theorem affineAxisProxyTube_direction
    (s : NNReal) (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    (affineAxisProxyTube s e T).axis.direction =
      affineImageAxisDirection e T :=
  rfl

/-- Exact fresh-output admissibility on the literal same-`W` datum supplies
ED for the five-parameter cap.  Center bounds are automatic from `W`; the
two raw-vector estimates are the genuine thick-plank quantitative input. -/
theorem normalizedFreshSelectedPlankFine_card_le_fiveParameterCap
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
    selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  let cert := chosenPlankCertificate hplank W
  let D := selectedPlankFineProxyDatum s e S B hrho label W
  let selectedD := restrictActualTubeDatum (eighthNormalizedDatum D) selected
  let tube : {i // i ∈ selected} → Tube (s / 8) :=
    fun i => selectedD.family.tubes i
  let x : Space := eighthDilationPoint cert.box.center
  have hscalePos : 0 < s / 8 := div_pos hs (by norm_num)
  have htubeEq (i : {i // i ∈ selected}) :
      tube i = eighthNormalizedTube
        (affineAxisProxyTube s (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1.1)) := by
    rfl
  have hmidSource (i : SelectedPlankFineIndex S W) :
      ‖affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) - cert.box.center‖ ≤ 2 := by
    exact selectedPlankFine_affineCenter_dist_chosenBoxCenter_le_two
      e S B hrho label hplank W i
  have hcenterSource (i : SelectedPlankFineIndex S W) :
      affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) ∈ cert.box.carrier := by
    exact selectedPlankFine_affineCenter_mem_chosenBox
      e S B hrho label hplank W i
  have hmidNorm (i : {i // i ∈ selected}) :
      ‖Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) - x‖ ≤ 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube,
      tubeAxisMidpoint_affineAxisProxyTube]
    dsimp only [x, eighthDilationPoint]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    have h := hmidSource i.1
    nlinarith
  have hcenter0Source (i : SelectedPlankFineIndex S W) :
      |⟪cert.box.frame 0,
        affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) - cert.box.center⟫_Real| ≤
        (bucketShortA label : Real) / 2 := by
    have h := cert.box.centeredCoordinate_abs_le_halfSide
      (hcenterSource i) 0
    rw [cert.side_eq] at h
    simpa [inner_sub_right, plankSides] using h
  have hcenter1Source (i : SelectedPlankFineIndex S W) :
      |⟪cert.box.frame 1,
        affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) - cert.box.center⟫_Real| ≤
        (bucketShortB label : Real) / 2 := by
    have h := cert.box.centeredCoordinate_abs_le_halfSide
      (hcenterSource i) 1
    rw [cert.side_eq] at h
    simpa [inner_sub_right, plankSides] using h
  have hmid0 (i : {i // i ∈ selected}) :
      |⟪cert.box.frame 0,
        Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) - x⟫_Real| ≤
        ((s / 8 : NNReal) : Real) / 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube,
      tubeAxisMidpoint_affineAxisProxyTube]
    dsimp only [x, eighthDilationPoint]
    rw [← smul_sub, real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    have h := hcenter0Source i.1
    have haReal : (bucketShortA label : Real) ≤ (s : Real) := by
      exact_mod_cast haScale
    push_cast
    nlinarith
  have hmid1 (i : {i // i ∈ selected}) :
      |⟪cert.box.frame 1,
        Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) - x⟫_Real| ≤
        (R * ((s / 8 : NNReal) : Real)) / 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube,
      tubeAxisMidpoint_affineAxisProxyTube]
    dsimp only [x, eighthDilationPoint]
    rw [← smul_sub, real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    have h := hcenter1Source i.1
    push_cast
    nlinarith
  have hdir0 (i : {i // i ∈ selected}) :
      |⟪cert.box.frame 0, (tube i).axis.direction⟫_Real| ≤
        ((s / 8 : NNReal) : Real) := by
    rw [htubeEq i, eighthNormalizedTube_direction,
      affineAxisProxyTube_direction]
    apply abs_inner_affineImageAxisDirection_le_of_lower_length
      _ _ _ (ell i.1) ((s : Real) / 8)
        (hellNorm i.1) (by positivity) (hvector0 i.1)
  have hdir1 (i : {i // i ∈ selected}) :
      |⟪cert.box.frame 1, (tube i).axis.direction⟫_Real| ≤
        R * ((s / 8 : NNReal) : Real) := by
    rw [htubeEq i, eighthNormalizedTube_direction,
      affineAxisProxyTube_direction]
    apply abs_inner_affineImageAxisDirection_le_of_lower_length
      _ _ _ (ell i.1) (R * ((s : Real) / 8))
        (hellNorm i.1) (mul_nonneg hR (by positivity)) (hvector1 i.1)
  have hpairwise :
      Set.Pairwise (Set.univ : Set {i // i ∈ selected}) fun i j =>
        EssentiallyDistinct (tube i) (tube j) := by
    exact hselectedAdmissible.pairwise_essentiallyDistinct
  have hcap :=
    card_le_thinPlankFivePackingNatCap_of_midpoint_direction_bounds
      cert.box.frame x tube R hscalePos hsmall hR hmidNorm hmid0 hmid1
        hdir0 hdir1 hthin hpairwise
  simpa only [Fintype.card_coe] using hcap

#print axioms tubeAxisMidpoint_affineAxisProxyTube
#print axioms affineAxisProxyTube_direction
#print axioms normalizedFreshSelectedPlankFine_card_le_fiveParameterCap

end
end Family8SelectedParentPlankFreshFiveParameterPackingV3
