import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostFiveParameterPackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1

open LeanEval.Analysis.WangZahlKakeya
open Family8CommonPointTubePackingV1
open Family4GlobalExtremalUpstream
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnProxyFiveParameterPackingV2
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8NormalizedSelectedContractedJohnFiveParameterPackingV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostFiveParameterPackingV1
open Family8SelectedParentPlankCenteredHalfPostDirectionV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineAxisLengthLowerV3
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFreshFiveParameterPackingV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterMidpointDirectionPackingV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Radius-adaptive centered proxy scale

The second term in the maximum is the literal scalar upper bound for the
centered-half affine image of a fine radius.  The first term preserves the
canonical direction and midpoint budgets.  Thus the carrier condition is a
theorem about this scale, rather than an extra scale-separation premise.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def selectedParentCenteredHalfPostRadiusFloor
    (delta rho r : NNReal) (label : Fin 3 → Int) : NNReal :=
  3 * r * delta / (4 * rho * sideShapeUpper label 2)

def selectedParentCenteredHalfPostAdaptiveProxyScale
    (delta rho r : NNReal) (label : Fin 3 → Int) : NNReal :=
  max (selectedPlankFineCanonicalProxyScale r label)
    (selectedParentCenteredHalfPostRadiusFloor delta rho r label)

theorem canonicalProxyScale_le_adaptiveProxyScale
    (delta rho r : NNReal) (label : Fin 3 → Int) :
    selectedPlankFineCanonicalProxyScale r label ≤
      selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label := by
  exact le_max_left _ _

theorem centeredHalfPostRadiusFloor_le_adaptiveProxyScale
    (delta rho r : NNReal) (label : Fin 3 → Int) :
    selectedParentCenteredHalfPostRadiusFloor delta rho r label ≤
      selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label := by
  exact le_max_right _ _

theorem selectedParent_centeredHalfPost_adaptive_radius_scalar
    (hrho : 0 < rho) (r : NNReal) (label : Fin 3 → Int) :
    ((1 / 2 : Real) *
      (3 * (r : Real) /
        ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
          (delta : Real) ≤
      (selectedParentCenteredHalfPostAdaptiveProxyScale
        delta rho r label : Real) := by
  have hrhoReal : (0 : Real) < (rho : Real) := by exact_mod_cast hrho
  have huReal : (0 : Real) < (sideShapeUpper label 2 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 2
  calc
    ((1 / 2 : Real) *
        (3 * (r : Real) /
          ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
          (delta : Real) =
        (selectedParentCenteredHalfPostRadiusFloor
          delta rho r label : Real) := by
            simp only [selectedParentCenteredHalfPostRadiusFloor,
              NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
            field_simp [hrhoReal.ne', huReal.ne']
            ring
    _ ≤ (selectedParentCenteredHalfPostAdaptiveProxyScale
          delta rho r label : Real) := by
      exact_mod_cast centeredHalfPostRadiusFloor_le_adaptiveProxyScale
        delta rho r label

theorem adaptiveProxyScale_pos
    (r delta rho : NNReal) (hr : 0 < r) (label : Fin 3 → Int) :
    0 < selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label := by
  apply lt_of_lt_of_le _
    (canonicalProxyScale_le_adaptiveProxyScale delta rho r label)
  change 0 < 8 * bucketShortA label /
    selectedPlankFineAxisLengthFloor r label
  exact div_pos (mul_pos (by norm_num) (bucketShortA_pos label))
    (selectedPlankFineAxisLengthFloor_pos hr label)

/-- The canonical packing proof is monotone in the proxy scale.  This form
isolates that fact: every direction and midpoint estimate survives replacing
the canonical scale by a larger real carrier scale. -/
theorem selectedParent_centeredHalfPost_enlarged_card_le_fiveParameterCap
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
    (s : NNReal)
    (hcanonical : selectedPlankFineCanonicalProxyScale r label ≤ s)
    (hscalar :
      ((1 / 2 : Real) *
        (3 * (r : Real) /
          ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
            (delta : Real) ≤ (s : Real))
    (selected : Finset (SelectedPlankFineIndex S W))
    (hselectedAdmissible :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let hradius := selectedParent_centeredHalfPost_radius_budget
        S hrho P k r hr label (blockAt S.activeCoarseFamily P k).fiber
          hplank W s hscalar
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (centeredHalfPostSelectedPlankFineMassDatum
            s Y e S (blockAt S.activeCoarseFamily P k).fiber hrho label
              hplank W hradius)) selected).IsAdmissible)
    (hsmall : s / 8 ≤ (1 / 100 : NNReal))
    (hthin :
      (((s / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((s / 8 : NNReal) : Real)) ^ 2 ≤ (3 : Real) / 4)) :
    selected.card ≤ thinPlankFivePackingNatCap
      (3 * selectedPlankFineCanonicalAspect label) := by
  let e0 := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B0 := (blockAt S.activeCoarseFamily P k).fiber
  let q := selectedPlankFineAxisLengthFloor r label
  let s0 := selectedPlankFineCanonicalProxyScale r label
  let R := selectedPlankFineCanonicalAspect label
  have hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e0 S B0 hrho label hplank W) *
        (delta : Real) ≤ (s : Real) := by
    exact selectedParent_centeredHalfPost_radius_budget
      S hrho P k r hr label B0 hplank W s hscalar
  have hq : 0 < q := selectedPlankFineAxisLengthFloor_pos hr label
  have hqReal : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hs0Formula : s0 = 8 * bucketShortA label / q := by rfl
  have hRFormula : R =
      (bucketShortB label : Real) / (bucketShortA label : Real) := by rfl
  have hs0 : 0 < s0 := by
    rw [hs0Formula]
    exact div_pos (mul_pos (by norm_num) (bucketShortA_pos label)) hq
  have hs : 0 < s := hs0.trans_le hcanonical
  have hcanonicalReal : (s0 : Real) ≤ (s : Real) := by
    exact_mod_cast hcanonical
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
      _ = ((q : Real) / 2) * ((s0 : Real) / 8) := by
        rw [hs0Formula]
        norm_num [NNReal.coe_div, NNReal.coe_mul]
        field_simp [hqReal.ne']
      _ ≤ ((q : Real) / 2) * ((s : Real) / 8) := by gcongr
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
      _ = ((q : Real) / 2) * (R * ((s0 : Real) / 8)) := by
        rw [hs0Formula, hRFormula]
        norm_num [NNReal.coe_div, NNReal.coe_mul]
        field_simp [hqReal.ne', haReal.ne']
      _ ≤ ((q : Real) / 2) * (R * ((s : Real) / 8)) := by gcongr
  have haScale0 : bucketShortA label ≤ s0 := by
    rw [hs0Formula]
    apply (le_div_iff₀ hq).2
    calc
      bucketShortA label * q ≤ bucketShortA label * 8 :=
        mul_le_mul_of_nonneg_left hqEight (by positivity)
      _ = 8 * bucketShortA label := by ac_rfl
  have haScale : bucketShortA label ≤ s := haScale0.trans hcanonical
  have hbScale0 : (bucketShortB label : Real) ≤ R * (s0 : Real) := by
    rw [hs0Formula, hRFormula]
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
  have hbScale : (bucketShortB label : Real) ≤ R * (s : Real) :=
    hbScale0.trans (mul_le_mul_of_nonneg_left hcanonicalReal hR)
  apply centeredHalfPostNormalizedSelected_card_le_fiveParameterCap
    e0 S B0 hrho label hplank W Y s hs hradius selected
      (by simpa only [e0, B0, hradius] using hselectedAdmissible)
      R hR (fun _ => (q : Real) / 2) hellNorm hvector0 hvector1
        haScale hbScale hsmall hthin

/-- At the adaptive maximum scale, both the radius and the monotonicity
premises of the enlarged packing theorem are automatic. -/
theorem selectedParent_centeredHalfPost_adaptive_card_le_fiveParameterCap
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
    (selected : Finset (SelectedPlankFineIndex S W))
    (hselectedAdmissible :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let s := selectedParentCenteredHalfPostAdaptiveProxyScale
        delta rho r label
      let hscalar := selectedParent_centeredHalfPost_adaptive_radius_scalar
        (delta := delta) hrho r label
      let hradius := selectedParent_centeredHalfPost_radius_budget
        S hrho P k r hr label (blockAt S.activeCoarseFamily P k).fiber
          hplank W s hscalar
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (centeredHalfPostSelectedPlankFineMassDatum
            s Y e S (blockAt S.activeCoarseFamily P k).fiber hrho label
              hplank W hradius)) selected).IsAdmissible)
    (hsmall : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label / 8 ≤ (1 / 100 : NNReal))
    (hthin :
      (((selectedParentCenteredHalfPostAdaptiveProxyScale
          delta rho r label / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((selectedParentCenteredHalfPostAdaptiveProxyScale
            delta rho r label / 8 : NNReal) : Real)) ^ 2 ≤
              (3 : Real) / 4)) :
    selected.card ≤ thinPlankFivePackingNatCap
      (3 * selectedPlankFineCanonicalAspect label) := by
  let s := selectedParentCenteredHalfPostAdaptiveProxyScale
    delta rho r label
  let hscalar := selectedParent_centeredHalfPost_adaptive_radius_scalar
    (delta := delta) hrho r label
  exact selectedParent_centeredHalfPost_enlarged_card_le_fiveParameterCap
    hfineContained S hrho hrhoOne P k r hr label hplank W Y s
      (canonicalProxyScale_le_adaptiveProxyScale delta rho r label)
      hscalar selected
      (by simpa only [s, hscalar] using hselectedAdmissible)
      hsmall hthin

#print axioms canonicalProxyScale_le_adaptiveProxyScale
#print axioms centeredHalfPostRadiusFloor_le_adaptiveProxyScale
#print axioms selectedParent_centeredHalfPost_adaptive_radius_scalar
#print axioms adaptiveProxyScale_pos
#print axioms
  selectedParent_centeredHalfPost_enlarged_card_le_fiveParameterCap
#print axioms
  selectedParent_centeredHalfPost_adaptive_card_le_fiveParameterCap

end
end Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
