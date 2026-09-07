import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationConflictMeanV1
import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
import Family8Grounding.Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperElongatedCandidateGridV1
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionUnitSpherePackingV3
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalOrbitV3
open Family8FiniteRigidMotionOrthogonalTwoCapLawV2
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalPatternCatalogueMembershipV2
open Family8FiniteRigidMotionOrthogonalNetCapCoverV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8FiniteRigidMotionOrthogonalNormalizationV4
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
open Family8FiniteRigidMotionOrthogonalTranslationConflictMeanV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
open Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalBalanceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking

noncomputable section

/-!
# Scale-only joint angular--translation mean for elongated conflict tests

This is the source-only analogue of the fixed-John elongated conflict mean.
It uses the same bounded translation packing and sampled angular catalogue but
requires only positivity of the source scale, plus the explicit upper-scale
hypothesis needed to fit the normalized mesh into the length-six test side.
No admissibility, Katz--Tao, essential-distinctness, or endpoint hypothesis is
stored in the construction.
-/

/-- Candidate-indexed elongated tests for the scale-only product law. -/
abbrev ScaleOnlyFixedJohnElongatedTest
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat) :=
  Fin (Fintype.card
    (NormalizedRigidCandidate
      (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) iota))

def scaleOnlyFixedJohnElongatedTargetCandidate
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    NormalizedRigidCandidate
      (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) iota :=
  normalizedRigidCandidateOfIndex K

def scaleOnlyFixedJohnElongatedTargetTube
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) : Tube (delta / 8) :=
  normalizedRigidCandidateTube
    (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
    (scaleOnlyFixedJohnElongatedTargetCandidate D hdelta n K)

def scaleOnlyFixedJohnElongatedTargetFrame
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    OrthonormalBasis (Fin 3) Real Space :=
  normalizedRigidCandidateAlignedFrame
    (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
    (scaleOnlyFixedJohnElongatedTargetCandidate D hdelta n K)

def scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) : ConvexBody Space :=
  normalizedRigidCandidateElongatedBody
    (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D K

@[simp] theorem scaleOnlyFixedJohnElongatedTargetFrame_two
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    scaleOnlyFixedJohnElongatedTargetFrame D hdelta n K 2 =
      (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K).axis.direction := by
  exact normalizedRigidCandidateAlignedFrame_two
    (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
    (scaleOnlyFixedJohnElongatedTargetCandidate D hdelta n K)

@[simp] theorem scaleOnlyFixedJohnOrthogonalTranslationElongatedBody_eq
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n K =
      paperElongatedBody
        (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K)
        (scaleOnlyFixedJohnElongatedTargetFrame D hdelta n K) := by
  rfl

/-- One net centre approximating the long direction of the fixed test. -/
def scaleOnlyFixedJohnElongatedNetDirectionChoice
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    HundredDirectionChoice (delta / 8)
      (scaleOnlyNormalizedRadiusPos hdelta) :=
  Classical.choose
    (unitDirectionChoice_cover
      (hundredDirectionCap (delta / 8))
      (hundredDirectionCap_pos (scaleOnlyNormalizedRadiusPos hdelta))
      (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K).axis.direction
      (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K).axis.norm_direction)

theorem scaleOnlyFixedJohnElongatedTarget_dist_netDirection_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    dist (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K).axis.direction
        (scaleOnlyFixedJohnElongatedNetDirectionChoice D hdelta n K).1 ≤
      ((2 * hundredDirectionCap (delta / 8) : NNReal) : Real) := by
  have h := Classical.choose_spec
    (unitDirectionChoice_cover
      (hundredDirectionCap (delta / 8))
      (hundredDirectionCap_pos (scaleOnlyNormalizedRadiusPos hdelta))
      (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K).axis.direction
      (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K).axis.norm_direction)
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top h
  simpa [scaleOnlyFixedJohnElongatedNetDirectionChoice, edist_dist] using hreal

/-- Sampled rotations passing the angular test for one source and target. -/
def scaleOnlyFixedJohnElongatedGoodRotations
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) (i : iota) :
    Finset (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :=
  sampledTwoCapFinset
    (sourceTubeDirection (normalizedSourceTube D))
    (hundredNetDirection (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta))
    (enlargedHundredDirectionCap (delta / 8)) n
    (i, scaleOnlyFixedJohnElongatedNetDirectionChoice D hdelta n K)

/-- At a fixed rotation, source indices passing the target angular test. -/
def scaleOnlyFixedJohnElongatedGoodSources
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : Finset iota := by
  classical
  exact Finset.univ.filter fun i =>
    r ∈ scaleOnlyFixedJohnElongatedGoodRotations D hdelta n K i

/-- Actual containment implies membership in the fixed target's angular test. -/
theorem mem_scaleOnlyFixedJohnElongatedGoodRotations_of_containment
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (t : ScaleOnlyFixedJohnPackingTranslation delta hdelta)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) (i : iota)
    (hcontain :
      (eighthNormalizedTube
        (rigidTube
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion
            D hdelta n (t, r))
          (D.family.tubes i))).carrier ⊆
        (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
          D hdelta n K : Set Space)) :
    r ∈ scaleOnlyFixedJohnElongatedGoodRotations D hdelta n K i := by
  let U := sampledHundredOrthogonal
    (normalizedSourceTube D) (scaleOnlyNormalizedRadiusPos hdelta) r
  have hmoved :
      rigidTube (orthogonalTranslationRigidMotion U t.1)
          (normalizedSourceTube D i) =
        eighthNormalizedTube
          (rigidTube
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion
              D hdelta n (t, r))
            (D.family.tubes i)) := by
    calc
      rigidTube (orthogonalTranslationRigidMotion U t.1)
          (normalizedSourceTube D i) =
        translateTube
          ((scaleOnlyFixedRotationPackingGrid D hdelta n
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
              D hdelta n) r).tube i)
          ((scaleOnlyFixedRotationPackingGrid D hdelta n
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
              D hdelta n) r).gridVector t) := by
            symm
            exact translateTube_rigidTube_orthogonalThree
              (normalizedSourceTube D i) U t.1
      _ = eighthNormalizedTube
          (rigidTube
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion
              D hdelta n (t, r))
            (D.family.tubes i)) :=
        scaleOnlyFixedRotationPackingGrid_translateTube_eq_normalizedRigidTube
          D hdelta n
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
              D hdelta n) r t i
  have hcontain' :
      (rigidTube (orthogonalTranslationRigidMotion U t.1)
        (normalizedSourceTube D i)).carrier ⊆
          (paperElongatedBody
            (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K)
            (scaleOnlyFixedJohnElongatedTargetFrame D hdelta n K) : Set Space) := by
    rw [hmoved]
    simpa only [scaleOnlyFixedJohnOrthogonalTranslationElongatedBody_eq] using
      hcontain
  have hbase := orthogonalElongatedContainment_mem_twoCapEvent
    (normalizedSourceTube D i)
    (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K)
    (scaleOnlyFixedJohnElongatedTargetFrame D hdelta n K) U t.1
    (scaleOnlyNormalizedRadiusPos hdelta) hcontain'
  rw [scaleOnlyFixedJohnElongatedTargetFrame_two] at hbase
  have hnet := orthogonalTwoCapEvent_subset_of_center_dist
    (sourceTubeDirection (normalizedSourceTube D) i)
    (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K).axis.direction
    (scaleOnlyFixedJohnElongatedNetDirectionChoice D hdelta n K).1
    (hundredDirectionCap (delta / 8))
    (2 * hundredDirectionCap (delta / 8))
    (scaleOnlyFixedJohnElongatedTarget_dist_netDirection_le
      D hdelta n K)
  apply (mem_sampledTwoCapFinset_iff
    (sourceTubeDirection (normalizedSourceTube D))
    (hundredNetDirection (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta))
    (enlargedHundredDirectionCap (delta / 8)) r
    (i, scaleOnlyFixedJohnElongatedNetDirectionChoice D hdelta n K)).2
  have hlarge := hnet hbase
  simpa only [U, sampledHundredOrthogonal, sourceTubeDirection,
    hundredNetDirection, enlargedHundredDirectionCap] using hlarge

/-- The fixed-rotation scale-only grid restricted to angularly admissible
sources. -/
def scaleOnlyFixedRotationElongatedPackingGrid
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
    ActualTubeTranslationGrid (delta / 8)
      (ScaleOnlyFixedJohnPackingTranslation delta hdelta) iota where
  gridVector t := t.1
  tubes := scaleOnlyFixedJohnElongatedGoodSources D hdelta n K r
  tube i := rigidTube
    (orthogonalThreeRigidMotion
      (sampledHundredOrthogonal (normalizedSourceTube D)
        (scaleOnlyNormalizedRadiusPos hdelta) r))
    (normalizedSourceTube D i)
  testCard := Fintype.card
    (NormalizedRigidCandidate
      (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) iota)
  testBody := scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n
  activeTests := Finset.univ

@[simp] theorem scaleOnlyFixedRotationElongatedPackingGrid_gridVector
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n)
    (t : ScaleOnlyFixedJohnPackingTranslation delta hdelta) :
    (scaleOnlyFixedRotationElongatedPackingGrid D hdelta n K r).gridVector t =
      t.1 := rfl

@[simp] theorem scaleOnlyFixedRotationElongatedPackingGrid_tubes
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
    (scaleOnlyFixedRotationElongatedPackingGrid D hdelta n K r).tubes =
      scaleOnlyFixedJohnElongatedGoodSources D hdelta n K r := rfl

@[simp] theorem scaleOnlyFixedRotationElongatedPackingGrid_tube
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) (i : iota) :
    (scaleOnlyFixedRotationElongatedPackingGrid D hdelta n K r).tube i =
      (scaleOnlyFixedRotationPackingGrid D hdelta n
        (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
        r).tube i := rfl

@[simp] theorem scaleOnlyFixedRotationElongatedPackingGrid_testBody
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n)
    (J : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    (scaleOnlyFixedRotationElongatedPackingGrid D hdelta n K r).testBody J =
      scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n J := rfl

/-- Restricting sources and changing tests preserves the shared translation
packing because its certificate depends only on the grid vectors. -/
theorem scaleOnlyFixedRotationElongated_isSharedTranslationPacking
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
    IsSharedTranslationPacking
      (scaleOnlyFixedRotationElongatedPackingGrid D hdelta n K r)
      (delta / 8) (1 / 8 : NNReal) := by
  let P := scaleOnlyFixedRotation_isSharedTranslationPacking D hdelta n
    (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n) r
  refine {
    mesh_pos := P.mesh_pos
    gridVector_injective := ?_
    gridVector_norm_le := ?_
    separated := ?_
    cover_motionBall := ?_ }
  · change Function.Injective
      (fun t : ScaleOnlyFixedJohnPackingTranslation delta hdelta =>
        (t.1 : Space))
    intro t u htu
    exact Subtype.ext htu
  · intro t
    change ‖(t.1 : Space)‖ ≤ (((1 / 8 : NNReal) : Real))
    simpa only [scaleOnlyFixedRotationPackingGrid_gridVector] using
      P.gridVector_norm_le t
  · intro t u htu
    change (((2 * (delta / 8) : NNReal) : ENNReal)) <
      edist (t.1 : Space) (u.1 : Space)
    simpa only [scaleOnlyFixedRotationPackingGrid_gridVector] using
      P.separated htu
  · change Metric.IsCover (2 * (delta / 8))
      (Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)))
      (Set.range
        (fun t : ScaleOnlyFixedJohnPackingTranslation delta hdelta =>
          (t.1 : Space)))
    change Metric.IsCover (2 * (delta / 8))
      (Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)))
      (Set.range
        (scaleOnlyFixedRotationPackingGrid D hdelta n
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
          r).gridVector)
    exact P.cover_motionBall

/-- Angular restriction leaves the literal full containment load unchanged. -/
@[simp] theorem scaleOnlyFixedRotationElongatedPackingGrid_singleLoad
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n)
    (t : ScaleOnlyFixedJohnPackingTranslation delta hdelta) :
    (scaleOnlyFixedRotationElongatedPackingGrid D hdelta n K r).singleLoad K t =
      normalizedRigidBodyLoadNat
        (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
        (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
        K (t, r) := by
  classical
  unfold ActualTubeTranslationGrid.singleLoad normalizedRigidBodyLoadNat
  apply congrArg Finset.card
  ext i
  simp only [scaleOnlyFixedRotationElongatedPackingGrid_tubes,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have htranslate :
      translateTube
          ((scaleOnlyFixedRotationElongatedPackingGrid
            D hdelta n K r).tube i)
          ((scaleOnlyFixedRotationElongatedPackingGrid
            D hdelta n K r).gridVector t) =
        eighthNormalizedTube
          (rigidTube
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion
              D hdelta n (t, r))
            (D.family.tubes i)) := by
    simpa only [scaleOnlyFixedRotationElongatedPackingGrid_tube,
      scaleOnlyFixedRotationElongatedPackingGrid_gridVector,
      scaleOnlyFixedRotationPackingGrid_gridVector] using
        (scaleOnlyFixedRotationPackingGrid_translateTube_eq_normalizedRigidTube
          D hdelta n
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
              D hdelta n) r t i)
  rw [htranslate]
  constructor
  · intro hi
    exact hi.2
  · intro hi
    refine ⟨?_, hi⟩
    unfold scaleOnlyFixedJohnElongatedGoodSources
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_scaleOnlyFixedJohnElongatedGoodRotations_of_containment
      D hdelta n K t r i hi

/-- Pointwise finite-pattern estimate for the scale-only angular test. -/
theorem card_scaleOnlyFixedJohnElongatedGoodRotations_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2)
    (i : iota) :
    ((scaleOnlyFixedJohnElongatedGoodRotations
        D hdelta n K i).card : ENNReal) ≤
      (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
  by_cases hcapHalf : enlargedHundredDirectionCap (delta / 8) ≤ 1 / 2
  · have hreal := card_sampledTwoCapFinset_le_card_mul_eleven_sq
      (sourceTubeDirection (normalizedSourceTube D))
      (hundredNetDirection (delta / 8)
        (scaleOnlyNormalizedRadiusPos hdelta))
      (fun q => unitDirectionChoice_norm
        (hundredDirectionCap (delta / 8))
        (hundredDirectionCap_pos (scaleOnlyNormalizedRadiusPos hdelta)) q)
      (enlargedHundredDirectionCap (delta / 8))
      (enlargedHundredDirectionCap_pos
        (scaleOnlyNormalizedRadiusPos hdelta))
      hcapHalf n hround
      (i, scaleOnlyFixedJohnElongatedNetDirectionChoice D hdelta n K)
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
        ((scaleOnlyFixedJohnElongatedGoodRotations
            D hdelta n K i).card : Real) ≤
          (Fintype.card
            (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : Real) := by
      exact_mod_cast Finset.card_le_univ
        (scaleOnlyFixedJohnElongatedGoodRotations D hdelta n K i)
    have hreal :
        ((scaleOnlyFixedJohnElongatedGoodRotations
            D hdelta n K i).card : Real) ≤
          (Fintype.card
              (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : Real) *
            (11 *
              (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :=
      hcard.trans (by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hone (by positivity :
            0 ≤ (Fintype.card
              (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : Real)))
    exact_mod_cast hreal

/-- Finite Fubini for a Boolean incidence relation. -/
private theorem scaleOnly_sum_card_filter_swap
    {alpha beta : Type} [Fintype alpha] [Fintype beta]
    (p : alpha → beta → Prop) [DecidableRel p] :
    (∑ a : alpha,
        (((Finset.univ : Finset beta).filter (p a)).card : ENNReal)) =
      ∑ b : beta,
        (((Finset.univ : Finset alpha).filter (fun a => p a b)).card :
          ENNReal) := by
  simp_rw [Finset.natCast_card_filter]
  rw [Finset.sum_comm]

/-- Double count the same rotation/source angular incidences. -/
theorem sum_card_scaleOnlyFixedJohnElongatedGoodSources_eq
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n) :
    (∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        ((scaleOnlyFixedJohnElongatedGoodSources
          D hdelta n K r).card : ENNReal)) =
      ∑ i : iota,
        ((scaleOnlyFixedJohnElongatedGoodRotations
          D hdelta n K i).card : ENNReal) := by
  classical
  simpa only [scaleOnlyFixedJohnElongatedGoodSources,
    Finset.filter_mem_eq_inter, Finset.univ_inter] using
    (scaleOnly_sum_card_filter_swap
      (p := fun r i =>
        r ∈ scaleOnlyFixedJohnElongatedGoodRotations D hdelta n K i))

/-- Total number of admissible rotation/source pairs. -/
theorem sum_card_scaleOnlyFixedJohnElongatedGoodSources_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :
    (∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        ((scaleOnlyFixedJohnElongatedGoodSources
          D hdelta n K r).card : ENNReal)) ≤
      (Fintype.card iota : ENNReal) *
        (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
  rw [sum_card_scaleOnlyFixedJohnElongatedGoodSources_eq D hdelta n K]
  calc
    (∑ i : iota,
        ((scaleOnlyFixedJohnElongatedGoodRotations
          D hdelta n K i).card : ENNReal)) ≤
      ∑ _i : iota,
        (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
      exact Finset.sum_le_sum fun i _hi =>
        card_scaleOnlyFixedJohnElongatedGoodRotations_le
          D hdelta n K hround i
    _ = (Fintype.card iota : ENNReal) *
        (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The normalized mesh fits all three elongated sides.  The upper-scale
hypothesis is used only for the length-six third side. -/
private theorem scaleOnlyNormalizedRadius_le_paperElongatedSides
    {delta : NNReal} (hdeltaHalf : delta ≤ 1 / 2) (j : Fin 3) :
    delta / 8 ≤ paperElongatedSides (delta / 8) j := by
  have hrhoNonneg : 0 ≤ delta / 8 := bot_le
  have hrhoSix : delta / 8 ≤ (6 : NNReal) := by
    apply (div_le_iff₀ (by norm_num : (0 : NNReal) < 8)).2
    calc
      delta ≤ 1 / 2 := hdeltaHalf
      _ ≤ 1 := by norm_num
      _ ≤ 6 * 8 := by norm_num
  fin_cases j <;> simp [paperElongatedSides] <;> nlinarith

/-- One fixed-rotation translation slice with its exact angular source count. -/
theorem sum_scaleOnlyFixedRotationElongatedBodyLoad_mul_motionBallVolume_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
    (∑ t : ScaleOnlyFixedJohnPackingTranslation delta hdelta,
        (normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
          K (t, r) : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (ScaleOnlyFixedJohnPackingTranslation delta hdelta) : ENNReal) *
        729 *
        ((scaleOnlyFixedJohnElongatedGoodSources
          D hdelta n K r).card : ENNReal) *
        volume
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
            D hdelta n K : Set Space) := by
  let G := scaleOnlyFixedRotationElongatedPackingGrid D hdelta n K r
  let P : IsSharedTranslationPacking G (delta / 8) (1 / 8 : NNReal) :=
    scaleOnlyFixedRotationElongated_isSharedTranslationPacking
      D hdelta n K r
  let B := paperElongatedFrameBox
    (scaleOnlyFixedJohnElongatedTargetTube D hdelta n K)
    (scaleOnlyFixedJohnElongatedTargetFrame D hdelta n K)
  have hbody : G.testBody K = B.body := by
    rfl
  have hmesh : ∀ j, delta / 8 ≤ B.side j := by
    intro j
    simpa only [B, paperElongatedFrameBox_side] using
      scaleOnlyNormalizedRadius_le_paperElongatedSides hdeltaHalf j
  have h :=
    sum_singleLoad_mul_motionBallVolume_le_card_mul_729_mul_card_mul_volume
      P K B hbody hmesh
  simpa only [G, scaleOnlyFixedRotationElongatedPackingGrid_singleLoad,
    scaleOnlyFixedRotationElongatedPackingGrid_tubes, motionBallVolume,
    B, scaleOnlyFixedJohnOrthogonalTranslationElongatedBody_eq,
    paperElongatedBody] using h

/-- Division-free joint angular--translation mean on the same scale-only
product outcome type. -/
theorem sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_mul_motionBallVolume_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :
    (∑ g : ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n,
        (normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
          K g : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) :
            ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
        729 * (Fintype.card iota : ENNReal) *
          volume
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
              D hdelta n K : Set Space) := by
  rw [Fintype.sum_prod_type_right]
  calc
    (∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        ∑ t : ScaleOnlyFixedJohnPackingTranslation delta hdelta,
          (normalizedRigidBodyLoadNat
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
            K (t, r) : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) =
      ∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        (∑ t : ScaleOnlyFixedJohnPackingTranslation delta hdelta,
          (normalizedRigidBodyLoadNat
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
            K (t, r) : ENNReal)) *
          volume (Metric.closedBall (0 : Space)
            (((1 / 8 : NNReal) : Real))) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        (Fintype.card
          (ScaleOnlyFixedJohnPackingTranslation delta hdelta) : ENNReal) *
          729 *
          ((scaleOnlyFixedJohnElongatedGoodSources
            D hdelta n K r).card : ENNReal) *
          volume
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
              D hdelta n K : Set Space) := by
      exact Finset.sum_le_sum fun r _hr =>
        sum_scaleOnlyFixedRotationElongatedBodyLoad_mul_motionBallVolume_le
          D hdelta hdeltaHalf n K r
    _ = (Fintype.card
          (ScaleOnlyFixedJohnPackingTranslation delta hdelta) : ENNReal) *
        729 *
        (∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
          ((scaleOnlyFixedJohnElongatedGoodSources
            D hdelta n K r).card : ENNReal)) *
        volume
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
            D hdelta n K : Set Space) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (Fintype.card
          (ScaleOnlyFixedJohnPackingTranslation delta hdelta) : ENNReal) *
        729 *
        ((Fintype.card iota : ENNReal) *
          (Fintype.card
            (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : ENNReal) *
          (11 *
            (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2)) *
        volume
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
            D hdelta n K : Set Space) := by
      gcongr
      exact sum_card_scaleOnlyFixedJohnElongatedGoodSources_le
        D hdelta n K hround
    _ = (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) :
            ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
        729 * (Fintype.card iota : ENNReal) *
          volume
            (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody
              D hdelta n K : Set Space) := by
      simp only [ScaleOnlyFixedJohnOrthogonalTranslationChoice,
        Fintype.card_prod, Nat.cast_mul]
      ring

/-- Supplied-scale endpoint displaying the two quadratic factors explicitly. -/
theorem sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_scaleFour_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2) (n : Nat)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta n)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest iota
              (HundredDirectionChoice
                (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))) : Real) ≤
        (n : Real) *
          (enlargedHundredDirectionCap (delta / 8) : Real) ^ 2) :
    (∑ g : ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n,
        (normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n) D
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta n)
          K g : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) :
            ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
        729 * (Fintype.card iota : ENNReal) *
        (240000 * ((delta / 8 : NNReal) : ENNReal) ^ 2) := by
  simpa only [scaleOnlyFixedJohnOrthogonalTranslationElongatedBody_eq,
    volume_paperElongatedBody] using
      sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_mul_motionBallVolume_le
        D hdelta hdeltaHalf n K hround

/-- Automatic-scale endpoint: the ceiling catalogue discharges the rounding
premise while retaining the same literal scale-only product law. -/
theorem sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_scaleFour_automatic_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta
      (scaleOnlyOrthogonalCatalogueScale D hdelta)) :
    (∑ g : ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta),
        (normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)) D
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta))
          K g : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)) : ENNReal) *
        (11 *
          (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
        729 * (Fintype.card iota : ENNReal) *
        (240000 * ((delta / 8 : NNReal) : ENNReal) ^ 2) := by
  exact
    sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_scaleFour_le
      D hdelta hdeltaHalf (scaleOnlyOrthogonalCatalogueScale D hdelta) K
      (scaleOnlyOrthogonalCatalogueScale_rounding D hdelta)

#print axioms scaleOnlyFixedJohnElongatedTarget_dist_netDirection_le
#print axioms mem_scaleOnlyFixedJohnElongatedGoodRotations_of_containment
#print axioms scaleOnlyFixedRotationElongated_isSharedTranslationPacking
#print axioms scaleOnlyFixedRotationElongatedPackingGrid_singleLoad
#print axioms card_scaleOnlyFixedJohnElongatedGoodRotations_le
#print axioms
  sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_mul_motionBallVolume_le
#print axioms
  sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_scaleFour_le
#print axioms
  sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_scaleFour_automatic_le

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1
