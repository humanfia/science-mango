import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
import Family8Grounding.Family8ThinPlankFiveParameterFrameBoxPackingV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationConflictMeanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionUnitSpherePackingV3
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalOrbitV3
open Family8FiniteRigidMotionOrthogonalTwoCapLawV2
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalPatternCatalogueMembershipV2
open Family8FiniteRigidMotionOrthogonalNetCapCoverV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
open Family8ThinPlankFiveParameterFrameBoxPackingV4
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalBalanceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking

noncomputable section

/-!
# Joint angular--translation mean for honest elongated conflict tests

For a fixed honest elongated test, tube containment forces the rotated source
direction into two caps.  The finite Haar-pattern catalogue therefore leaves
only `O(rho^2)` rotations.  For every one of those rotations, the bounded
shared translation packing contributes the second `O(rho^2)` factor through
the exact volume `240000 * rho^2` of the elongated body.  Both factors are
retained on the same literal rotation-times-translation outcome type used by
the fixed-John/CWA mean.

This is a producer theorem: no conflict mean, load cap, or good-copy property
is assumed.  It is also deliberately only the joint first-moment layer; tuple
selection and the subsequent greedy refinement belong downstream.
-/

private theorem sq_le_sq_of_abs_le' {x a : Real} (h : |x| ≤ a) :
    x ^ 2 ≤ a ^ 2 := by
  have ha : 0 ≤ a := (abs_nonneg x).trans h
  have hsquare := (sq_le_sq₀ (abs_nonneg x) ha).2 h
  simpa only [sq_abs] using hsquare

/-- Containment in an honest elongated body forces the contained tube's
unoriented direction into two caps of radius `601 * rho`.  Only the two short
sides of the body are used. -/
theorem direction_mem_paperElongated_twoCaps
    {rho : NNReal} (S T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hrho : 0 < rho)
    (hcontain : S.carrier ⊆ (paperElongatedBody T frame : Set Space)) :
    S.axis.direction ∈
      Metric.ball (frame 2) (hundredDirectionCap rho : Real) ∪
        Metric.ball (-(frame 2)) (hundredDirectionCap rho : Real) := by
  have hcontainBox : S.carrier ⊆ (paperElongatedFrameBox T frame).carrier := by
    simpa only [coe_paperElongatedBody] using hcontain
  let c0 : Real := ⟪frame 0, S.axis.direction⟫_Real
  let c1 : Real := ⟪frame 1, S.axis.direction⟫_Real
  let c2 : Real := ⟪frame 2, S.axis.direction⟫_Real
  let r : Real := (rho : Real)
  have hc0 : |c0| ≤ 200 * r := by
    simpa [c0, r, paperElongatedFrameBox, paperElongatedSides] using
      (abs_inner_direction_le_frameBox_side
        (paperElongatedFrameBox T frame) S hcontainBox (0 : Fin 3))
  have hc1 : |c1| ≤ 200 * r := by
    simpa [c1, r, paperElongatedFrameBox, paperElongatedSides] using
      (abs_inner_direction_le_frameBox_side
        (paperElongatedFrameBox T frame) S hcontainBox (1 : Fin 3))
  have hc0sq : c0 ^ 2 ≤ (200 * r) ^ 2 := sq_le_sq_of_abs_le' hc0
  have hc1sq : c1 ^ 2 ≤ (200 * r) ^ 2 := sq_le_sq_of_abs_le' hc1
  have hparseval := frame.sum_sq_inner_right S.axis.direction
  rw [Fin.sum_univ_three, S.axis.norm_direction] at hparseval
  norm_num at hparseval
  change c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 1 at hparseval
  have hc2abs : |c2| ≤ 1 := by
    dsimp only [c2]
    simpa only [frame.norm_eq_one, S.axis.norm_direction, one_mul] using
      (abs_real_inner_le_norm (frame 2) S.axis.direction)
  have hr : 0 ≤ r := by positivity
  have hstrict : 400 * r < (hundredDirectionCap rho : Real) := by
    simp only [hundredDirectionCap, NNReal.coe_mul]
    norm_num
    exact mul_lt_mul_of_pos_right (by norm_num : (400 : Real) < 601)
      (NNReal.coe_pos.mpr hrho)
  by_cases hc2 : 0 ≤ c2
  · apply Set.mem_union_left
    change dist S.axis.direction (frame 2) < (hundredDirectionCap rho : Real)
    have hc2Upper : c2 ≤ 1 := (le_abs_self c2).trans hc2abs
    have hc2prod : 0 ≤ c2 * (1 - c2) :=
      mul_nonneg hc2 (sub_nonneg.mpr hc2Upper)
    have hdistSq : (dist S.axis.direction (frame 2)) ^ 2 = 2 - 2 * c2 := by
      rw [dist_eq_norm, norm_sub_sq_real, S.axis.norm_direction,
        frame.norm_eq_one, real_inner_comm]
      change 1 ^ 2 - 2 * c2 + 1 ^ 2 = 2 - 2 * c2
      ring
    have hdistLe : dist S.axis.direction (frame 2) ≤ 400 * r := by
      apply (sq_le_sq₀ dist_nonneg (mul_nonneg (by norm_num) hr)).mp
      rw [hdistSq]
      nlinarith
    exact hdistLe.trans_lt hstrict
  · apply Set.mem_union_right
    change dist S.axis.direction (-(frame 2)) <
      (hundredDirectionCap rho : Real)
    have hc2Nonpos : c2 ≤ 0 := le_of_not_ge hc2
    have hc2Lower : -1 ≤ c2 := neg_le_of_abs_le hc2abs
    have hc2prod : 0 ≤ (-c2) * (1 + c2) :=
      mul_nonneg (neg_nonneg.mpr hc2Nonpos) (by linarith)
    have hdistSq :
        (dist S.axis.direction (-(frame 2))) ^ 2 = 2 + 2 * c2 := by
      rw [dist_eq_norm, norm_sub_sq_real, S.axis.norm_direction, norm_neg,
        frame.norm_eq_one, inner_neg_right, real_inner_comm]
      change 1 ^ 2 - 2 * (-c2) + 1 ^ 2 = 2 + 2 * c2
      ring
    have hdistLe : dist S.axis.direction (-(frame 2)) ≤ 400 * r := by
      apply (sq_le_sq₀ dist_nonneg (mul_nonneg (by norm_num) hr)).mp
      rw [hdistSq]
      nlinarith
    exact hdistLe.trans_lt hstrict

/-- Event form of the preceding geometric lemma. -/
theorem orthogonalElongatedContainment_mem_twoCapEvent
    {rho : NNReal} (S T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (U : OrthogonalThree) (t : Space) (hrho : 0 < rho)
    (hcontain :
      (rigidTube (orthogonalTranslationRigidMotion U t) S).carrier ⊆
        (paperElongatedBody T frame : Set Space)) :
    U ∈ orthogonalTwoCapEvent S.axis.direction (frame 2)
      (hundredDirectionCap rho) := by
  rw [orthogonalTwoCapEvent, ← Set.preimage_union]
  simpa only [Set.mem_preimage,
    rigidTube_orthogonalTranslation_direction] using
      direction_mem_paperElongated_twoCaps
        (rigidTube (orthogonalTranslationRigidMotion U t) S)
        T frame hrho hcontain

/-- Candidate-indexed honest elongated tests for the same product law used by
the bounded fixed-John catalogue. -/
abbrev FixedJohnElongatedTest
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat) :=
  Fin (Fintype.card
    (NormalizedRigidCandidate
      (FixedJohnOrthogonalTranslationChoice D hD n) iota))

def fixedJohnElongatedTargetCandidate
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) :
    NormalizedRigidCandidate
      (FixedJohnOrthogonalTranslationChoice D hD n) iota :=
  normalizedRigidCandidateOfIndex K

def fixedJohnElongatedTargetTube
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) : Tube (delta / 8) :=
  normalizedRigidCandidateTube
    (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
    (fixedJohnElongatedTargetCandidate D hD n K)

def fixedJohnElongatedTargetFrame
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) :
    OrthonormalBasis (Fin 3) Real Space :=
  normalizedRigidCandidateAlignedFrame
    (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
    (fixedJohnElongatedTargetCandidate D hD n K)

def fixedJohnOrthogonalTranslationElongatedBody
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) : ConvexBody Space :=
  normalizedRigidCandidateElongatedBody
    (fixedJohnSampledOrthogonalTranslationMotion D hD n) D K

@[simp] theorem fixedJohnElongatedTargetFrame_two
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) :
    fixedJohnElongatedTargetFrame D hD n K 2 =
      (fixedJohnElongatedTargetTube D hD n K).axis.direction := by
  exact normalizedRigidCandidateAlignedFrame_two
    (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
    (fixedJohnElongatedTargetCandidate D hD n K)

@[simp] theorem fixedJohnOrthogonalTranslationElongatedBody_eq
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) :
    fixedJohnOrthogonalTranslationElongatedBody D hD n K =
      paperElongatedBody (fixedJohnElongatedTargetTube D hD n K)
        (fixedJohnElongatedTargetFrame D hD n K) := by
  rfl

/-- A single net centre approximating the long direction of the fixed
elongated test. -/
def fixedJohnElongatedNetDirectionChoice
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) :
    HundredDirectionChoice (delta / 8) (normalizedRadius_pos hD) :=
  Classical.choose
    (unitDirectionChoice_cover
      (hundredDirectionCap (delta / 8))
      (hundredDirectionCap_pos (normalizedRadius_pos hD))
      (fixedJohnElongatedTargetTube D hD n K).axis.direction
      (fixedJohnElongatedTargetTube D hD n K).axis.norm_direction)

theorem fixedJohnElongatedTarget_dist_netDirection_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) :
    dist (fixedJohnElongatedTargetTube D hD n K).axis.direction
        (fixedJohnElongatedNetDirectionChoice D hD n K).1 ≤
      ((2 * hundredDirectionCap (delta / 8) : NNReal) : Real) := by
  have h := Classical.choose_spec
    (unitDirectionChoice_cover
      (hundredDirectionCap (delta / 8))
      (hundredDirectionCap_pos (normalizedRadius_pos hD))
      (fixedJohnElongatedTargetTube D hD n K).axis.direction
      (fixedJohnElongatedTargetTube D hD n K).axis.norm_direction)
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top h
  simpa [fixedJohnElongatedNetDirectionChoice, edist_dist] using hreal

/-- Sampled rotations that pass the angular test for one source tube and one
fixed elongated target. -/
def fixedJohnElongatedGoodRotations
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) (i : iota) :
    Finset (FixedJohnOrthogonalSample D hD n) :=
  sampledTwoCapFinset
    (sourceTubeDirection (normalizedSourceTube D))
    (hundredNetDirection (delta / 8) (normalizedRadius_pos hD))
    (enlargedHundredDirectionCap (delta / 8)) n
    (i, fixedJohnElongatedNetDirectionChoice D hD n K)

/-- For a fixed sampled rotation, retain precisely the source indices passing
the fixed target's angular test. -/
def fixedJohnElongatedGoodSources
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n) : Finset iota := by
  classical
  exact Finset.univ.filter fun i =>
    r ∈ fixedJohnElongatedGoodRotations D hD n K i

/-- Every actual containment counted by the product load passes the angular
test.  This is the bridge which permits the fixed-rotation translation grid to
be restricted without changing its load. -/
theorem mem_fixedJohnElongatedGoodRotations_of_containment
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (t : FixedJohnPackingTranslation D hD)
    (r : FixedJohnOrthogonalSample D hD n) (i : iota)
    (hcontain :
      (eighthNormalizedTube
        (rigidTube
          (fixedJohnSampledOrthogonalTranslationMotion D hD n (t, r))
          (D.family.tubes i))).carrier ⊆
        (fixedJohnOrthogonalTranslationElongatedBody D hD n K : Set Space)) :
    r ∈ fixedJohnElongatedGoodRotations D hD n K i := by
  let U := sampledHundredOrthogonal
    (normalizedSourceTube D) (normalizedRadius_pos hD) r
  have hmoved :
      rigidTube (orthogonalTranslationRigidMotion U t.1)
          (normalizedSourceTube D i) =
        eighthNormalizedTube
          (rigidTube
            (fixedJohnSampledOrthogonalTranslationMotion D hD n (t, r))
            (D.family.tubes i)) := by
    calc
      rigidTube (orthogonalTranslationRigidMotion U t.1)
          (normalizedSourceTube D i) =
        translateTube
          ((fixedRotationJohnPackingGrid D hD n r).tube i)
          ((fixedRotationJohnPackingGrid D hD n r).gridVector t) := by
            symm
            exact translateTube_rigidTube_orthogonalThree
              (normalizedSourceTube D i) U t.1
      _ = eighthNormalizedTube
          (rigidTube
            (fixedJohnSampledOrthogonalTranslationMotion D hD n (t, r))
            (D.family.tubes i)) :=
        fixedRotationJohnPackingGrid_translateTube_eq_normalizedRigidTube
          D hD n r t i
  have hcontain' :
      (rigidTube (orthogonalTranslationRigidMotion U t.1)
        (normalizedSourceTube D i)).carrier ⊆
          (paperElongatedBody
            (fixedJohnElongatedTargetTube D hD n K)
            (fixedJohnElongatedTargetFrame D hD n K) : Set Space) := by
    rw [hmoved]
    simpa only [fixedJohnOrthogonalTranslationElongatedBody_eq] using hcontain
  have hbase := orthogonalElongatedContainment_mem_twoCapEvent
    (normalizedSourceTube D i)
    (fixedJohnElongatedTargetTube D hD n K)
    (fixedJohnElongatedTargetFrame D hD n K) U t.1
    (normalizedRadius_pos hD) hcontain'
  rw [fixedJohnElongatedTargetFrame_two] at hbase
  have hnet := orthogonalTwoCapEvent_subset_of_center_dist
    (sourceTubeDirection (normalizedSourceTube D) i)
    (fixedJohnElongatedTargetTube D hD n K).axis.direction
    (fixedJohnElongatedNetDirectionChoice D hD n K).1
    (hundredDirectionCap (delta / 8))
    (2 * hundredDirectionCap (delta / 8))
    (fixedJohnElongatedTarget_dist_netDirection_le D hD n K)
  apply (mem_sampledTwoCapFinset_iff
    (sourceTubeDirection (normalizedSourceTube D))
    (hundredNetDirection (delta / 8) (normalizedRadius_pos hD))
    (enlargedHundredDirectionCap (delta / 8)) r
    (i, fixedJohnElongatedNetDirectionChoice D hD n K)).2
  have hlarge := hnet hbase
  simpa only [U, sampledHundredOrthogonal, sourceTubeDirection,
    hundredNetDirection, enlargedHundredDirectionCap] using hlarge

/-- The fixed-rotation translation grid restricted to angularly admissible
source tubes.  Its vector net is definitionally the same bounded packing as in
the CWA product mean. -/
def fixedRotationElongatedPackingGrid
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n) :
    ActualTubeTranslationGrid (delta / 8)
      (FixedJohnPackingTranslation D hD) iota where
  gridVector t := t.1
  tubes := fixedJohnElongatedGoodSources D hD n K r
  tube i := rigidTube
    (orthogonalThreeRigidMotion
      (sampledHundredOrthogonal
        (normalizedSourceTube D) (normalizedRadius_pos hD) r))
    (normalizedSourceTube D i)
  testCard := Fintype.card
    (NormalizedRigidCandidate
      (FixedJohnOrthogonalTranslationChoice D hD n) iota)
  testBody := fixedJohnOrthogonalTranslationElongatedBody D hD n
  activeTests := Finset.univ

@[simp] theorem fixedRotationElongatedPackingGrid_gridVector
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n)
    (t : FixedJohnPackingTranslation D hD) :
    (fixedRotationElongatedPackingGrid D hD n K r).gridVector t = t.1 := rfl

@[simp] theorem fixedRotationElongatedPackingGrid_tubes
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n) :
    (fixedRotationElongatedPackingGrid D hD n K r).tubes =
      fixedJohnElongatedGoodSources D hD n K r := rfl

@[simp] theorem fixedRotationElongatedPackingGrid_tube
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n) (i : iota) :
    (fixedRotationElongatedPackingGrid D hD n K r).tube i =
      (fixedRotationJohnPackingGrid D hD n r).tube i := rfl

@[simp] theorem fixedRotationElongatedPackingGrid_testBody
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n)
    (J : FixedJohnElongatedTest D hD n) :
    (fixedRotationElongatedPackingGrid D hD n K r).testBody J =
      fixedJohnOrthogonalTranslationElongatedBody D hD n J := rfl

/-- Changing the source subset and test bodies leaves the shared translation
packing certificate unchanged. -/
theorem fixedRotationElongatedPacking_isSharedTranslationPacking
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n) :
    IsSharedTranslationPacking
      (fixedRotationElongatedPackingGrid D hD n K r)
      (delta / 8) (1 / 8 : NNReal) := by
  let P := fixedRotationJohnPacking_isSharedTranslationPacking D hD n r
  refine {
    mesh_pos := P.mesh_pos
    gridVector_injective := ?_
    gridVector_norm_le := ?_
    separated := ?_
    cover_motionBall := ?_ }
  · change Function.Injective
      (fun t : FixedJohnPackingTranslation D hD => (t.1 : Space))
    intro t u htu
    exact Subtype.ext htu
  · intro t
    change ‖(t.1 : Space)‖ ≤ (((1 / 8 : NNReal) : Real))
    simpa only [fixedRotationJohnPackingGrid_gridVector] using
      P.gridVector_norm_le t
  · intro t u htu
    change (((2 * (delta / 8) : NNReal) : ENNReal)) <
      edist (t.1 : Space) (u.1 : Space)
    simpa only [fixedRotationJohnPackingGrid_gridVector] using
      P.separated htu
  · change Metric.IsCover (2 * (delta / 8))
      (Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)))
      (Set.range (fun t : FixedJohnPackingTranslation D hD => (t.1 : Space)))
    change Metric.IsCover (2 * (delta / 8))
      (Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)))
      (Set.range (fixedRotationJohnPackingGrid D hD n r).gridVector)
    exact P.cover_motionBall

/-- Angular restriction does not alter the literal full containment load. -/
@[simp] theorem fixedRotationElongatedPackingGrid_singleLoad
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n)
    (t : FixedJohnPackingTranslation D hD) :
    (fixedRotationElongatedPackingGrid D hD n K r).singleLoad K t =
      normalizedRigidBodyLoadNat
        (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
        (fixedJohnOrthogonalTranslationElongatedBody D hD n) K (t, r) := by
  classical
  unfold ActualTubeTranslationGrid.singleLoad normalizedRigidBodyLoadNat
  apply congrArg Finset.card
  ext i
  simp only [fixedRotationElongatedPackingGrid_tubes, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have htranslate :
      translateTube
          ((fixedRotationElongatedPackingGrid D hD n K r).tube i)
          ((fixedRotationElongatedPackingGrid D hD n K r).gridVector t) =
        eighthNormalizedTube
          (rigidTube
            (fixedJohnSampledOrthogonalTranslationMotion D hD n (t, r))
            (D.family.tubes i)) := by
    simpa only [fixedRotationElongatedPackingGrid_tube,
      fixedRotationElongatedPackingGrid_gridVector,
      fixedRotationJohnPackingGrid_gridVector] using
        (fixedRotationJohnPackingGrid_translateTube_eq_normalizedRigidTube
          D hD n r t i)
  rw [htranslate]
  constructor
  · intro hi
    exact hi.2
  · intro hi
    refine ⟨?_, hi⟩
    unfold fixedJohnElongatedGoodSources
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_fixedJohnElongatedGoodRotations_of_containment
      D hD n K t r i hi

/-- The finite Haar-pattern estimate for each source/target angular test,
stated in the `ENNReal` scalar used by the translation-volume estimate.  The
large-cap branch is discharged trivially, so no artificial small-scale
assumption is imposed on the caller. -/
theorem card_fixedJohnElongatedGoodRotations_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (normalizedRadius_pos hD)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2)
    (i : iota) :
    ((fixedJohnElongatedGoodRotations D hD n K i).card : ENNReal) ≤
      (Fintype.card (FixedJohnOrthogonalSample D hD n) : ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
  by_cases hcapHalf : enlargedHundredDirectionCap (delta / 8) ≤ 1 / 2
  · have hreal := card_sampledTwoCapFinset_le_card_mul_eleven_sq
      (sourceTubeDirection (normalizedSourceTube D))
      (hundredNetDirection (delta / 8) (normalizedRadius_pos hD))
      (fun q => unitDirectionChoice_norm
        (hundredDirectionCap (delta / 8))
        (hundredDirectionCap_pos (normalizedRadius_pos hD)) q)
      (enlargedHundredDirectionCap (delta / 8))
      (enlargedHundredDirectionCap_pos (normalizedRadius_pos hD))
      hcapHalf n hround
      (i, fixedJohnElongatedNetDirectionChoice D hD n K)
    exact_mod_cast hreal
  · have hcapReal :
        (1 / 2 : Real) <
          (enlargedHundredDirectionCap (delta / 8) : Real) := by
      exact_mod_cast (lt_of_not_ge hcapHalf)
    have hone :
        (1 : Real) ≤
          11 * (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2 := by
      nlinarith [sq_nonneg
        (enlargedHundredDirectionCap (delta / 8) : Real)]
    have hcard :
        ((fixedJohnElongatedGoodRotations D hD n K i).card : Real) ≤
          (Fintype.card (FixedJohnOrthogonalSample D hD n) : Real) := by
      exact_mod_cast Finset.card_le_univ
        (fixedJohnElongatedGoodRotations D hD n K i)
    have hreal :
        ((fixedJohnElongatedGoodRotations D hD n K i).card : Real) ≤
          (Fintype.card (FixedJohnOrthogonalSample D hD n) : Real) *
            (11 *
              (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :=
      hcard.trans (by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hone (by positivity :
            0 ≤ (Fintype.card
              (FixedJohnOrthogonalSample D hD n) : Real)))
    exact_mod_cast hreal

/-- Elementary finite Fubini identity for a Boolean incidence relation. -/
private theorem sum_card_filter_swap
    {alpha beta : Type} [Fintype alpha] [Fintype beta]
    (p : alpha → beta → Prop) [DecidableRel p] :
    (∑ a : alpha,
        (((Finset.univ : Finset beta).filter (p a)).card : ENNReal)) =
      ∑ b : beta,
        (((Finset.univ : Finset alpha).filter (fun a => p a b)).card :
          ENNReal) := by
  simp_rw [Finset.natCast_card_filter]
  rw [Finset.sum_comm]

/-- Summing the angularly admissible source count over rotations is the same
as summing the admissible rotation count over sources. -/
theorem sum_card_fixedJohnElongatedGoodSources_eq
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n) :
    (∑ r : FixedJohnOrthogonalSample D hD n,
        ((fixedJohnElongatedGoodSources D hD n K r).card : ENNReal)) =
      ∑ i : iota,
        ((fixedJohnElongatedGoodRotations D hD n K i).card : ENNReal) := by
  classical
  simpa only [fixedJohnElongatedGoodSources,
    Finset.filter_mem_eq_inter, Finset.univ_inter] using
    (sum_card_filter_swap
      (p := fun r i =>
        r ∈ fixedJohnElongatedGoodRotations D hD n K i))

/-- Total number of angularly admissible rotation/source pairs. -/
theorem sum_card_fixedJohnElongatedGoodSources_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (normalizedRadius_pos hD)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :
    (∑ r : FixedJohnOrthogonalSample D hD n,
        ((fixedJohnElongatedGoodSources D hD n K r).card : ENNReal)) ≤
      (Fintype.card iota : ENNReal) *
        (Fintype.card (FixedJohnOrthogonalSample D hD n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
  rw [sum_card_fixedJohnElongatedGoodSources_eq D hD n K]
  calc
    (∑ i : iota,
        ((fixedJohnElongatedGoodRotations D hD n K i).card : ENNReal)) ≤
      ∑ _i : iota,
        (Fintype.card (FixedJohnOrthogonalSample D hD n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
      exact Finset.sum_le_sum fun i _hi =>
        card_fixedJohnElongatedGoodRotations_le D hD n K hround i
    _ = (Fintype.card iota : ENNReal) *
        (Fintype.card (FixedJohnOrthogonalSample D hD n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

private theorem normalizedRadius_le_paperElongatedSides
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (j : Fin 3) :
    delta / 8 ≤ paperElongatedSides (delta / 8) j := by
  have hrhoNonneg : 0 ≤ delta / 8 := bot_le
  have hrhoSix : delta / 8 ≤ (6 : NNReal) := by
    apply (div_le_iff₀ (by norm_num : (0 : NNReal) < 8)).2
    calc
      delta ≤ (2 : NNReal)⁻¹ := hD.delta_le_half
      _ ≤ 1 := by norm_num
      _ ≤ 6 * 8 := by norm_num
  fin_cases j <;> simp [paperElongatedSides] <;> nlinarith

/-- One fixed-rotation slice: translation packing sees only angularly
admissible sources, and hence retains their exact cardinality rather than the
full source cardinality. -/
theorem sum_fixedRotationElongatedBodyLoad_mul_motionBallVolume_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (r : FixedJohnOrthogonalSample D hD n) :
    (∑ t : FixedJohnPackingTranslation D hD,
        (normalizedRigidBodyLoadNat
          (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
          (fixedJohnOrthogonalTranslationElongatedBody D hD n) K (t, r) :
            ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card (FixedJohnPackingTranslation D hD) : ENNReal) *
        729 *
        ((fixedJohnElongatedGoodSources D hD n K r).card : ENNReal) *
        volume
          (fixedJohnOrthogonalTranslationElongatedBody D hD n K : Set Space) := by
  let G := fixedRotationElongatedPackingGrid D hD n K r
  let P : IsSharedTranslationPacking G (delta / 8) (1 / 8 : NNReal) :=
    fixedRotationElongatedPacking_isSharedTranslationPacking D hD n K r
  let B := paperElongatedFrameBox
    (fixedJohnElongatedTargetTube D hD n K)
    (fixedJohnElongatedTargetFrame D hD n K)
  have hbody : G.testBody K = B.body := by
    rfl
  have hmesh : ∀ j, delta / 8 ≤ B.side j := by
    intro j
    simpa only [B, paperElongatedFrameBox_side] using
      normalizedRadius_le_paperElongatedSides D hD j
  have h :=
    sum_singleLoad_mul_motionBallVolume_le_card_mul_729_mul_card_mul_volume
      P K B hbody hmesh
  simpa only [G, fixedRotationElongatedPackingGrid_singleLoad,
    fixedRotationElongatedPackingGrid_tubes, motionBallVolume,
    B, fixedJohnOrthogonalTranslationElongatedBody_eq,
    paperElongatedBody] using h

/-- The missing finite analogue of the paper's `delta^2 * delta^2`
containment probability.  The angular cap factor and elongated-body volume
factor occur on the same rotation-times-bounded-translation law. -/
theorem sum_normalizedOrthogonalTranslationElongatedBodyLoad_mul_motionBallVolume_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (normalizedRadius_pos hD)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :
    (∑ g : FixedJohnOrthogonalTranslationChoice D hD n,
        (normalizedRigidBodyLoadNat
          (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
          (fixedJohnOrthogonalTranslationElongatedBody D hD n) K g :
            ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (FixedJohnOrthogonalTranslationChoice D hD n) : ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
        729 * (Fintype.card iota : ENNReal) *
          volume
            (fixedJohnOrthogonalTranslationElongatedBody D hD n K : Set Space) := by
  rw [Fintype.sum_prod_type_right]
  calc
    (∑ r : FixedJohnOrthogonalSample D hD n,
        ∑ t : FixedJohnPackingTranslation D hD,
          (normalizedRigidBodyLoadNat
            (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
            (fixedJohnOrthogonalTranslationElongatedBody D hD n) K (t, r) :
              ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) =
      ∑ r : FixedJohnOrthogonalSample D hD n,
        (∑ t : FixedJohnPackingTranslation D hD,
          (normalizedRigidBodyLoadNat
            (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
            (fixedJohnOrthogonalTranslationElongatedBody D hD n) K (t, r) :
              ENNReal)) *
          volume (Metric.closedBall (0 : Space)
            (((1 / 8 : NNReal) : Real))) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ r : FixedJohnOrthogonalSample D hD n,
        (Fintype.card (FixedJohnPackingTranslation D hD) : ENNReal) *
          729 *
          ((fixedJohnElongatedGoodSources D hD n K r).card : ENNReal) *
          volume
            (fixedJohnOrthogonalTranslationElongatedBody D hD n K : Set Space) := by
      exact Finset.sum_le_sum fun r _hr =>
        sum_fixedRotationElongatedBodyLoad_mul_motionBallVolume_le
          D hD n K r
    _ = (Fintype.card (FixedJohnPackingTranslation D hD) : ENNReal) *
        729 *
        (∑ r : FixedJohnOrthogonalSample D hD n,
          ((fixedJohnElongatedGoodSources D hD n K r).card : ENNReal)) *
        volume
          (fixedJohnOrthogonalTranslationElongatedBody D hD n K : Set Space) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (Fintype.card (FixedJohnPackingTranslation D hD) : ENNReal) *
        729 *
        ((Fintype.card iota : ENNReal) *
          (Fintype.card (FixedJohnOrthogonalSample D hD n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2)) *
        volume
          (fixedJohnOrthogonalTranslationElongatedBody D hD n K : Set Space) := by
      gcongr
      exact sum_card_fixedJohnElongatedGoodSources_le D hD n K hround
    _ = (Fintype.card
          (FixedJohnOrthogonalTranslationChoice D hD n) : ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
        729 * (Fintype.card iota : ENNReal) *
          volume
            (fixedJohnOrthogonalTranslationElongatedBody D hD n K : Set Space) := by
      simp only [FixedJohnOrthogonalTranslationChoice, Fintype.card_prod,
        Nat.cast_mul]
      ring

/-- Explicit scale form: the two displayed quadratic factors make the
`O((delta/8)^4)` gain syntactically visible. -/
theorem sum_normalizedOrthogonalTranslationElongatedBodyLoad_scaleFour_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (K : FixedJohnElongatedTest D hD n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (normalizedRadius_pos hD)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :
    (∑ g : FixedJohnOrthogonalTranslationChoice D hD n,
        (normalizedRigidBodyLoadNat
          (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
          (fixedJohnOrthogonalTranslationElongatedBody D hD n) K g :
            ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (FixedJohnOrthogonalTranslationChoice D hD n) : ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
        729 * (Fintype.card iota : ENNReal) *
        (240000 * ((delta / 8 : NNReal) : ENNReal) ^ 2) := by
  simpa only [fixedJohnOrthogonalTranslationElongatedBody_eq,
    volume_paperElongatedBody] using
      sum_normalizedOrthogonalTranslationElongatedBodyLoad_mul_motionBallVolume_le
        D hD n K hround

#print axioms direction_mem_paperElongated_twoCaps
#print axioms orthogonalElongatedContainment_mem_twoCapEvent
#print axioms mem_fixedJohnElongatedGoodRotations_of_containment
#print axioms fixedRotationElongatedPacking_isSharedTranslationPacking
#print axioms fixedRotationElongatedPackingGrid_singleLoad
#print axioms card_fixedJohnElongatedGoodRotations_le
#print axioms sum_normalizedOrthogonalTranslationElongatedBodyLoad_mul_motionBallVolume_le
#print axioms sum_normalizedOrthogonalTranslationElongatedBodyLoad_scaleFour_le

end
end Family8FiniteRigidMotionOrthogonalTranslationConflictMeanV1
