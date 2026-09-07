import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostDirectionV1
import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostMassDatumV2
import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
import Family8Grounding.Family8SelectedParentPlankCanonicalThinCountV5
import Family8Grounding.Family8SelectedParentPlankFreshFiveParameterPackingV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankCenteredHalfPostFiveParameterPackingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CommonPointTubePackingV1
open Family4GlobalExtremalUpstream
open Family8ContractedJohnProxyFiveParameterPackingV2
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8NormalizedSelectedContractedJohnFiveParameterPackingV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostDirectionV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineAxisLengthLowerV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFreshFiveParameterPackingV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterMidpointDirectionPackingV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Five-parameter packing for the centered half-post family

The first theorem is the literal same-`W`, same-selected consumer.  The
second specializes to the winning-block John map and the canonical
`q = r / (6912 u₂)` scale.  In that specialization both raw-vector and
axis-length callbacks disappear: the centered half-post multiplies their
numerator and denominator by the same `1/2`.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem centeredHalfPostNormalizedSelected_card_le_fiveParameterCap
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (Y : Shading fine.bodyFamily)
    (s : NNReal) (hs : 0 < s)
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real))
    (selected : Finset (SelectedPlankFineIndex S W))
    (hselectedAdmissible :
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (centeredHalfPostSelectedPlankFineMassDatum
            s Y e S B hrho label hplank W hradius))
        selected).IsAdmissible)
    (R : Real) (hR : 0 ≤ R)
    (ell : SelectedPlankFineIndex S W → Real)
    (hellNorm : ∀ i,
      ell i ≤ ‖affineImageAxisVector
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
          (fine.tubes i.1)‖)
    (hvector0 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector
          (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
            (fine.tubes i.1)⟫_Real| ≤ ell i * ((s : Real) / 8))
    (hvector1 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector
          (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
            (fine.tubes i.1)⟫_Real| ≤
        ell i * (R * ((s : Real) / 8)))
    (haScale : bucketShortA label ≤ s)
    (hbScale : (bucketShortB label : Real) ≤ R * (s : Real))
    (hsmall : s / 8 ≤ (1 / 100 : NNReal))
    (hthin :
      ((s / 8 : NNReal) : Real) ^ 2 +
        (R * ((s / 8 : NNReal) : Real)) ^ 2 ≤ (3 : Real) / 4) :
    selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  let E := centeredHalfPostBucketAffineEquiv
    e S B hrho label hplank W
  let D := centeredHalfPostSelectedPlankFineMassDatum
    s Y e S B hrho label hplank W hradius
  let selectedD := restrictActualTubeDatum (eighthNormalizedDatum D) selected
  let tube : {i // i ∈ selected} → Tube (s / 8) :=
    fun i => selectedD.family.tubes i
  let cert := chosenPlankCertificate hplank W
  have hscalePos : 0 < s / 8 := div_pos hs (by norm_num)
  have htubeEq (i : {i // i ∈ selected}) :
      tube i = eighthNormalizedTube
        (affineAxisProxyTube s E (fine.tubes i.1.1)) := by
    rfl
  have hcenterSource (i : SelectedPlankFineIndex S W) :
      affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) ∈ cert.box.carrier := by
    exact selectedPlankFine_affineCenter_mem_chosenBox
      e S B hrho label hplank W i
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
  have hcenter0 (i : SelectedPlankFineIndex S W) :
      |⟪cert.box.frame 0,
        affineImageAxisCenter E (fine.tubes i.1)⟫_Real| ≤
        (bucketShortA label : Real) / 4 := by
    rw [affineImageAxisCenter_centeredHalfPostBucketAffineEquiv,
      real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]
    nlinarith [hcenter0Source i]
  have hcenter1 (i : SelectedPlankFineIndex S W) :
      |⟪cert.box.frame 1,
        affineImageAxisCenter E (fine.tubes i.1)⟫_Real| ≤
        (bucketShortB label : Real) / 4 := by
    rw [affineImageAxisCenter_centeredHalfPostBucketAffineEquiv,
      real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]
    nlinarith [hcenter1Source i]
  have hmidNorm (i : {i // i ∈ selected}) :
      ‖Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) -
        (0 : Space)‖ ≤ 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube,
      tubeAxisMidpoint_affineAxisProxyTube, sub_zero]
    dsimp only [eighthDilationPoint]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    have h := selectedPlankFine_centeredHalfPost_axisCenter_norm_le_one
      e S B hrho label hplank W i.1
    change ‖affineImageAxisCenter E (fine.tubes i.1.1)‖ ≤ 1 at h
    nlinarith
  have hmid0 (i : {i // i ∈ selected}) :
      |⟪cert.box.frame 0,
        Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) -
          (0 : Space)⟫_Real| ≤
        ((s / 8 : NNReal) : Real) / 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube,
      tubeAxisMidpoint_affineAxisProxyTube, sub_zero]
    dsimp only [eighthDilationPoint]
    rw [real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    have haReal : (bucketShortA label : Real) ≤ (s : Real) := by
      exact_mod_cast haScale
    have h := hcenter0 i.1
    push_cast
    nlinarith
  have hmid1 (i : {i // i ∈ selected}) :
      |⟪cert.box.frame 1,
        Family8CommonPointTubePackingV1.tubeAxisMidpoint (tube i) -
          (0 : Space)⟫_Real| ≤
        (R * ((s / 8 : NNReal) : Real)) / 2 := by
    rw [htubeEq i, tubeAxisMidpoint_eighthNormalizedTube,
      tubeAxisMidpoint_affineAxisProxyTube, sub_zero]
    dsimp only [eighthDilationPoint]
    rw [real_inner_smul_right, abs_mul,
      abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
    have h := hcenter1 i.1
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
      cert.box.frame 0 tube R hscalePos hsmall hR hmidNorm hmid0 hmid1
        hdir0 hdir1 hthin hpairwise
  simpa only [Fintype.card_coe] using hcap

/-- For the actual winning-block map, the canonical `q` scale supplies all
direction hypotheses.  The only geometric premises left are scalar: the
carrier-radius budget and the usual small/thin inequalities. -/
theorem selectedParent_centeredHalfPost_canonical_card_le_fiveParameterCap
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (Y : Shading fine.bodyFamily)
    (hscalar :
      ((1 / 2 : Real) *
        (3 * (r : Real) /
          ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
            (delta : Real) ≤
        (selectedPlankFineCanonicalProxyScale r label : Real))
    (selected : Finset (SelectedPlankFineIndex S W))
    (hselectedAdmissible :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let s := selectedPlankFineCanonicalProxyScale r label
      let hradius := selectedParent_centeredHalfPost_radius_budget
        S hrho P k r hr label (blockAt S.activeCoarseFamily P k).fiber
          hplank W s hscalar
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (centeredHalfPostSelectedPlankFineMassDatum
            s Y e S (blockAt S.activeCoarseFamily P k).fiber hrho label
              hplank W hradius)) selected).IsAdmissible)
    (hsmall : selectedPlankFineCanonicalProxyScale r label / 8 ≤
      (1 / 100 : NNReal))
    (hthin :
      (((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real)) ^ 2 ≤
        (3 : Real) / 4)) :
    selected.card ≤ thinPlankFivePackingNatCap
      (3 * selectedPlankFineCanonicalAspect label) := by
  let e0 := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B0 := (blockAt S.activeCoarseFamily P k).fiber
  let q := selectedPlankFineAxisLengthFloor r label
  let s := selectedPlankFineCanonicalProxyScale r label
  let R := selectedPlankFineCanonicalAspect label
  have hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e0 S B0 hrho label hplank W) *
        (delta : Real) ≤ (s : Real) := by
    exact selectedParent_centeredHalfPost_radius_budget
      S hrho P k r hr label B0 hplank W s hscalar
  have hq : 0 < q := selectedPlankFineAxisLengthFloor_pos hr label
  have hqReal : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hsFormula : s = 8 * bucketShortA label / q := by rfl
  have hRFormula : R =
      (bucketShortB label : Real) / (bucketShortA label : Real) := by rfl
  have hs : 0 < s := by
    rw [hsFormula]
    exact div_pos (mul_pos (by norm_num) (bucketShortA_pos label)) hq
  have hfiberNonempty : (S.fiber W.1.1.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ :=
      S.parent_surjective W.1.1.1 W.1.1.2
    exact ⟨i, (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩⟩
  let i0 : SelectedPlankFineIndex S W :=
    ⟨hfiberNonempty.choose, hfiberNonempty.choose_spec⟩
  have hqTwo : q ≤ 2 := by
    exact selectedPlankFineAxisLengthFloor_le_two
      hfineContained S hrho hrhoOne P k r hr label hplank W i0
  have hqEight : q ≤ 8 := hqTwo.trans (by norm_num)
  have hqEightReal : (q : Real) ≤ 8 := by exact_mod_cast hqEight
  have hR : 0 ≤ R := by
    rw [hRFormula]
    exact div_nonneg (by positivity) (by positivity)
  have hellNorm : ∀ i : SelectedPlankFineIndex S W,
      (q : Real) / 2 ≤
        ‖affineImageAxisVector
          (centeredHalfPostBucketAffineEquiv e0 S B0 hrho label hplank W)
            (fine.tubes i.1)‖ := by
    intro i
    rw [norm_affineImageAxisVector_centeredHalfPostBucketAffineEquiv]
    have hqBucket : (q : Real) ≤
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e0 label)
          (fine.tubes i.1)‖ := by
      simpa only [q, e0, selectedPlankFineAxisLengthFloor] using
        selectedPlankFine_bucketAffineImageAxisVector_norm_lower
          hfineContained S hrho hrhoOne P k r hr label W i
    nlinarith
  have hraw : ∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector
          (centeredHalfPostBucketAffineEquiv e0 S B0 hrho label hplank W)
            (fine.tubes i.1)⟫_Real| ≤ (bucketShortA label : Real) / 2 ∧
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector
          (centeredHalfPostBucketAffineEquiv e0 S B0 hrho label hplank W)
            (fine.tubes i.1)⟫_Real| ≤ (bucketShortB label : Real) / 2 := by
    intro i
    simpa only [e0, B0] using
      selectedPlankFine_centeredHalfPost_rawVector_chosenFrame_bounds
        e0 S B0 hrho label hplank W i
  have hvector0 : ∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector
          (centeredHalfPostBucketAffineEquiv e0 S B0 hrho label hplank W)
            (fine.tubes i.1)⟫_Real| ≤
          ((q : Real) / 2) * ((s : Real) / 8) := by
    intro i
    calc
      _ ≤ (bucketShortA label : Real) / 2 := (hraw i).1
      _ = ((q : Real) / 2) * ((s : Real) / 8) := by
        rw [hsFormula]
        norm_num [NNReal.coe_div, NNReal.coe_mul]
        field_simp [hqReal.ne']
  have haReal : (0 : Real) < (bucketShortA label : Real) := by
    exact_mod_cast bucketShortA_pos label
  have hvector1 : ∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector
          (centeredHalfPostBucketAffineEquiv e0 S B0 hrho label hplank W)
            (fine.tubes i.1)⟫_Real| ≤
          ((q : Real) / 2) * (R * ((s : Real) / 8)) := by
    intro i
    calc
      _ ≤ (bucketShortB label : Real) / 2 := (hraw i).2
      _ = ((q : Real) / 2) * (R * ((s : Real) / 8)) := by
        rw [hsFormula, hRFormula]
        norm_num [NNReal.coe_div, NNReal.coe_mul]
        field_simp [hqReal.ne', haReal.ne']
  have haScale : bucketShortA label ≤ s := by
    rw [hsFormula]
    apply (le_div_iff₀ hq).2
    calc
      bucketShortA label * q ≤ bucketShortA label * 8 :=
        mul_le_mul_of_nonneg_left hqEight (by positivity)
      _ = 8 * bucketShortA label := by ac_rfl
  have hbScale : (bucketShortB label : Real) ≤ R * (s : Real) := by
    rw [hsFormula, hRFormula]
    norm_num [NNReal.coe_div, NNReal.coe_mul]
    have hrewrite :
        (bucketShortB label : Real) / (bucketShortA label : Real) *
            (8 * (bucketShortA label : Real) / (q : Real)) =
          8 * (bucketShortB label : Real) / (q : Real) := by
      field_simp [haReal.ne', hqReal.ne']
    rw [hrewrite]
    apply (le_div_iff₀ hqReal).2
    have hmul := mul_le_mul_of_nonneg_left hqEightReal
      (show (0 : Real) ≤ (bucketShortB label : Real) by positivity)
    nlinarith
  apply centeredHalfPostNormalizedSelected_card_le_fiveParameterCap
    e0 S B0 hrho label hplank W Y s hs hradius selected
      (by simpa only [e0, B0, s, hradius] using hselectedAdmissible)
      R hR (fun _ => (q : Real) / 2) hellNorm hvector0 hvector1
        haScale hbScale hsmall hthin

#print axioms centeredHalfPostNormalizedSelected_card_le_fiveParameterCap
#print axioms
  selectedParent_centeredHalfPost_canonical_card_le_fiveParameterCap

end
end Family8SelectedParentPlankCenteredHalfPostFiveParameterPackingV1
