import Family8Grounding.Family8SelectedParentPlankFineMassProxyFreshThinCountV2
import Family8Grounding.Family8SelectedParentPlankCanonicalThinCountV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankFineMassProxyCanonicalFreshThinCountV2

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
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineAxisLengthLowerV3
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineMassProxyFreshThinCountV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Canonical mass-retaining fresh thin count

The canonical inverse-John length floor supplies the `ell` parameter and both
actual chosen-plank coordinate inequalities for the same mass-aware selected
set.  Only the two genuine proxy-carrier distortion premises, raw proxy
Katz--Tao control, and the two thin-scale scalar conditions remain explicit.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem exists_selectedPlankFine_massProxy_canonicalFresh_with_thinCount
    (Y : Shading fine.bodyFamily)
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
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr) label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr) label) *
        (delta : Real) ≤
      (selectedPlankFineCanonicalProxyScale r label : Real))
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
    let D := selectedPlankFineMassProxyDatum s Y e S
      (blockAt S.activeCoarseFamily P k).fiber hrho label W
        haxisLength hradius
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
      (selectedPlankFineSourceShading Y e S
        (blockAt S.activeCoarseFamily P k).fiber hrho label W).averageMultiplicity ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.averageMultiplicity ∧
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
  exact exists_selectedPlankFine_massProxy_normalizedFresh_with_thinCount
    Y e0 S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W
      s hs hsHalf haxisLength hradius hCfinite hKT R hR
      (fun _ => (q : Real)) hellNorm hvector0 hvector1 haScale hbScale
      hsmall hthin

#print axioms
  exists_selectedPlankFine_massProxy_canonicalFresh_with_thinCount

end
end Family8SelectedParentPlankFineMassProxyCanonicalFreshThinCountV2
