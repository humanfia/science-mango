import Family8Grounding.Family8SelectedParentPlankFineAxisLengthLowerV3
import Family8Grounding.Family8SelectedParentPlankFineProxyFreshSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankCanonicalThinCountV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8AffineImageAxisPlankCoordinateBridgeV4
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineAxisLengthLowerV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFineProxyFreshSelectionV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Canonical same-W thin count without vector callbacks

The inverse-John length floor is used as the literal denominator for the two
actual chosen-plank coordinate bounds.  Choosing the proxy radius and aspect
from this floor makes both raw-vector hypotheses of the packing theorem
identities.  Only the scale-smallness scalar and raw proxy Katz--Tao control
remain.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def selectedPlankFineAxisLengthFloor (r : NNReal)
    (label : Fin 3 → Int) : NNReal :=
  r / (6912 * sideShapeUpper label 2)

def selectedPlankFineCanonicalProxyScale (r : NNReal)
    (label : Fin 3 → Int) : NNReal :=
  8 * bucketShortA label / selectedPlankFineAxisLengthFloor r label

def selectedPlankFineCanonicalAspect (label : Fin 3 → Int) : Real :=
  (bucketShortB label : Real) / (bucketShortA label : Real)

theorem selectedPlankFineAxisLengthFloor_pos {r : NNReal}
    (hr : 0 < r) (label : Fin 3 → Int) :
    0 < selectedPlankFineAxisLengthFloor r label := by
  unfold selectedPlankFineAxisLengthFloor
  exact div_pos hr (mul_pos (by norm_num) (sideShapeUpper_pos label 2))

/-- The actual chosen plank also bounds the canonical floor by `2`; this is
Parseval applied to the same real transformed fine axis. -/
theorem selectedPlankFineAxisLengthFloor_le_two
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
    (i : SelectedPlankFineIndex S W) :
    selectedPlankFineAxisLengthFloor r label ≤ 2 := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let d := bucketNormalizedAffineEquiv e label
  let cert := chosenPlankCertificate hplank W
  let T := fine.tubes i.1
  let v := affineImageAxisVector d T
  have h01 := selectedPlankFine_rawVector_chosenFrame_bounds
    e S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W i
  have haxis := selectedPlankFine_axis_image_subset_parent
    e S (blockAt S.activeCoarseFamily P k).fiber hrho label W i
  have hbaseK : d T.axis.base ∈
      (selectedParentPlankBucketFamily e S
        (blockAt S.activeCoarseFamily P k).fiber hrho label W : Set Space) :=
    haxis ⟨T.axis.base, T.axis.base_mem_carrier, rfl⟩
  have hendK : d T.axis.endpoint ∈
      (selectedParentPlankBucketFamily e S
        (blockAt S.activeCoarseFamily P k).fiber hrho label W : Set Space) :=
    haxis ⟨T.axis.endpoint, T.axis.endpoint_mem_carrier, rfl⟩
  have hbase : d T.axis.base ∈ cert.box.carrier := cert.outer_le hbaseK
  have hend : d T.axis.endpoint ∈ cert.box.carrier := cert.outer_le hendK
  have h2raw := abs_inner_affineImageAxisVector_le_frameBox_side
    d T cert.box hbase hend 2
  rw [cert.side_eq] at h2raw
  have h2 : |⟪cert.box.frame 2, v⟫_Real| ≤ (1 : Real) := by
    simpa only [v, plankSides, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, NNReal.coe_one] using h2raw
  have haOne : (bucketShortA label : Real) ≤ 1 := by
    exact_mod_cast cert.a_le_b.trans cert.b_le_one
  have hbOne : (bucketShortB label : Real) ≤ 1 := by
    exact_mod_cast cert.b_le_one
  have h0 : |⟪cert.box.frame 0, v⟫_Real| ≤ (1 : Real) :=
    h01.1.trans haOne
  have h1 : |⟪cert.box.frame 1, v⟫_Real| ≤ (1 : Real) :=
    h01.2.trans hbOne
  let c0 : Real := ⟪cert.box.frame 0, v⟫_Real
  let c1 : Real := ⟪cert.box.frame 1, v⟫_Real
  let c2 : Real := ⟪cert.box.frame 2, v⟫_Real
  have hc0 : c0 ^ 2 ≤ 1 := by
    have hbounds := abs_le.mp h0
    have hp : 0 ≤ (1 - c0) * (1 + c0) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hc1 : c1 ^ 2 ≤ 1 := by
    have hbounds := abs_le.mp h1
    have hp : 0 ≤ (1 - c1) * (1 + c1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hc2 : c2 ^ 2 ≤ 1 := by
    have hbounds := abs_le.mp h2
    have hp : 0 ≤ (1 - c2) * (1 + c2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hparseval := cert.box.frame.sum_sq_inner_right v
  rw [Fin.sum_univ_three] at hparseval
  change c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = ‖v‖ ^ 2 at hparseval
  have hnorm : ‖v‖ ≤ (2 : Real) := by
    by_contra hn
    have hn' : (2 : Real) < ‖v‖ := lt_of_not_ge hn
    nlinarith [norm_nonneg v]
  have hfloorReal :
      (selectedPlankFineAxisLengthFloor r label : Real) ≤ ‖v‖ := by
    simpa only [selectedPlankFineAxisLengthFloor, e, d, T, v] using
      selectedPlankFine_bucketAffineImageAxisVector_norm_lower
        hfineContained S hrho hrhoOne P k r hr label W i
  exact_mod_cast hfloorReal.trans hnorm

/-- On the canonical source scale, both required raw-vector inequalities are
automatic consequences of the actual chosen-plank certificate and the
uniform inverse-John length floor. -/
theorem exists_selectedPlankFine_canonicalFresh_with_thinCount
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
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (selectedPlankFineProxyDatum
        (selectedPlankFineCanonicalProxyScale r label)
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label W).family.bodyFamily)
    (hsmall : selectedPlankFineCanonicalProxyScale r label / 8 ≤
      (1 / 100 : NNReal))
    (hthin :
      (((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real)) ^ 2 ≤
        (3 : Real) / 4)) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let s := selectedPlankFineCanonicalProxyScale r label
    let R := selectedPlankFineCanonicalAspect label
    let D := selectedPlankFineProxyDatum s e S
      (blockAt S.activeCoarseFamily P k).fiber hrho label W
    let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
    ∃ selected : Finset (SelectedPlankFineIndex S W),
      selected.Nonempty ∧
      Set.Pairwise (selected : Set (SelectedPlankFineIndex S W))
        (fun i j => EssentiallyDistinct
          ((eighthNormalizedDatum D).family.tubes i)
          ((eighthNormalizedDatum D).family.tubes j)) ∧
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      ((threshold + 1 : Nat) : ENNReal) ≤ 480000 * (128 * C) + 2 ∧
      selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  dsimp only
  let e0 := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let d := bucketNormalizedAffineEquiv e0 label
  let q := selectedPlankFineAxisLengthFloor r label
  let s := selectedPlankFineCanonicalProxyScale r label
  let R := selectedPlankFineCanonicalAspect label
  have hq : 0 < q := selectedPlankFineAxisLengthFloor_pos hr label
  have hqReal : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hsFormula : s = 8 * bucketShortA label / q := by rfl
  have hRFormula : R =
      (bucketShortB label : Real) / (bucketShortA label : Real) := by rfl
  have hs : 0 < s := by
    rw [hsFormula]
    exact div_pos (mul_pos (by norm_num) (bucketShortA_pos label)) hq
  have hsHalf : s ≤ (2 : NNReal)⁻¹ := by
    have hsTimes : s ≤ (1 / 100 : NNReal) * 8 := by
      exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 8)).mp
        (by simpa only [s] using hsmall)
    rw [div_mul_eq_mul_div, one_mul] at hsTimes
    have hnum : (8 : NNReal) / 100 ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (by norm_num) (by norm_num)).2
      norm_num
    simpa only [inv_eq_one_div] using hsTimes.trans hnum
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
      (q : Real) ≤ ‖affineImageAxisVector d (fine.tubes i.1)‖ := by
    intro i
    simpa only [q, d, e0, selectedPlankFineAxisLengthFloor] using
      selectedPlankFine_bucketAffineImageAxisVector_norm_lower
        hfineContained S hrho hrhoOne P k r hr label W i
  have hraw : ∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector d (fine.tubes i.1)⟫_Real| ≤
          (bucketShortA label : Real) ∧
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector d (fine.tubes i.1)⟫_Real| ≤
          (bucketShortB label : Real) := by
    intro i
    simpa only [d, e0] using
      selectedPlankFine_rawVector_chosenFrame_bounds
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W i
  have hvector0 : ∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector d (fine.tubes i.1)⟫_Real| ≤
          (q : Real) * ((s : Real) / 8) := by
    intro i
    calc
      _ ≤ (bucketShortA label : Real) := (hraw i).1
      _ = (q : Real) * ((s : Real) / 8) := by
        rw [hsFormula]
        norm_num [NNReal.coe_div, NNReal.coe_mul]
        field_simp [hqReal.ne']
  have haReal : (0 : Real) < (bucketShortA label : Real) := by
    exact_mod_cast bucketShortA_pos label
  have hvector1 : ∀ i : SelectedPlankFineIndex S W,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector d (fine.tubes i.1)⟫_Real| ≤
          (q : Real) * (R * ((s : Real) / 8)) := by
    intro i
    calc
      _ ≤ (bucketShortB label : Real) := (hraw i).2
      _ = (q : Real) * (R * ((s : Real) / 8)) := by
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
  exact exists_selectedPlankFine_normalizedFresh_with_thinCount
    e0 S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W
      s hs hsHalf hCfinite hKT R hR (fun _ => (q : Real)) hellNorm
      hvector0 hvector1 haScale hbScale hsmall hthin

#print axioms selectedPlankFineAxisLengthFloor_pos
#print axioms selectedPlankFineAxisLengthFloor_le_two
#print axioms exists_selectedPlankFine_canonicalFresh_with_thinCount

end
end Family8SelectedParentPlankCanonicalThinCountV5
