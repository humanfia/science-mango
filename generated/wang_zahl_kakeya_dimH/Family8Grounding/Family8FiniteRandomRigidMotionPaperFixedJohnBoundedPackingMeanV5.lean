import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
import FamilyStickyGrounding.FamilyStickySharedTranslationPackingExistenceV1
import FamilyStickyGrounding.FamilyStickySharedTranslationPackingNonemptyV1
import FamilyStickyGrounding.FamilyStickyActualSharedLocalExpectationV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8PolynomialJohnFrameBoxTestNetV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingExistenceV1
open FamilyStickySharedTranslationPackingExistenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingNonemptyV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# A genuine bounded finite translation law and its fixed-John mean

Take a maximal finite `(delta / 8)`-mesh packing of the normalized motion
ball `B(0, 1/8)`.  A normalized center `v` represents the original physical
translation `8 v`; hence every physical vector lies in `B(0,1)`, and exact
eighth-normalization sends it back to `v`.  This is one shared finite law for
all tests, not a product of test-dependent lattices.

The existing shared-packing incidence theorem then bounds the literal exact
mean by the explicit formula

`297 * #T * side_0 * side_1 / (1/8)^2`.

This closes existence of a bounded law and a uniform geometric mean
majorant.  A paper-strength lower bound for the repetition count still
requires comparing that majorant to the maximal-concentration cap.
-/

/-- The canonical finite packing of the normalized motion ball. -/
def fixedJohnPackingCertificate
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    PackingCertificate
      (Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)))
      (delta / 8) :=
  Classical.choice
    (exists_motionBallPackingCertificate (1 / 8 : NNReal) (delta / 8)
      (admissibleNormalizedRadiusPos hD))

/-- Literal finite outcome type of the bounded shared law. -/
abbrev FixedJohnPackingTranslation
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :=
  ↥(fixedJohnPackingCertificate D hD).centers

noncomputable instance fixedJohnPackingTranslationNonempty
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    Nonempty (FixedJohnPackingTranslation D hD) :=
  motionBallPackingCertificate_translation_nonempty
    (fixedJohnPackingCertificate D hD)

/-- Convert a normalized packing center back to the original physical
translation vector. -/
def fixedJohnPackingGridVector
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (g : FixedJohnPackingTranslation D hD) : Space :=
  (8 : Real) • (g.1 : Space)

@[simp] theorem eighthTranslationVector_fixedJohnPackingGridVector
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (g : FixedJohnPackingTranslation D hD) :
    eighthTranslationVector (fixedJohnPackingGridVector D hD g) = g.1 := by
  unfold eighthTranslationVector fixedJohnPackingGridVector
  module

/-- The physical translation vectors are honestly supported in `B(0,1)`. -/
theorem fixedJohnPackingGridVector_norm_le_one
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (g : FixedJohnPackingTranslation D hD) :
    ‖fixedJohnPackingGridVector D hD g‖ ≤ 1 := by
  have hgmem : (g.1 : Space) ∈
      Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)) :=
    (fixedJohnPackingCertificate D hD).centers_subset g.2
  have hg : ‖(g.1 : Space)‖ ≤ (((1 / 8 : NNReal) : Real)) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hgmem
  calc
    ‖fixedJohnPackingGridVector D hD g‖ =
        8 * ‖(g.1 : Space)‖ := by
      simp [fixedJohnPackingGridVector, norm_smul]
    _ ≤ 8 * (((1 / 8 : NNReal) : Real)) :=
      mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = 1 := by norm_num

/-- Actual normalized grid attached to the bounded law. -/
def fixedJohnPackingNormalizedGrid
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :=
  normalizedTranslationBodyGrid
    (fixedJohnPackingGridVector D hD) D
    (fixedJohnCatalogueBody hD) Finset.univ

@[simp] theorem fixedJohnPackingNormalizedGrid_gridVector
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (g : FixedJohnPackingTranslation D hD) :
    (fixedJohnPackingNormalizedGrid D hD).gridVector g = g.1 :=
  eighthTranslationVector_fixedJohnPackingGridVector D hD g

/-- The canonical normalized grid is one genuine shared packing of
`B(0,1/8)`. -/
theorem fixedJohnPacking_isSharedTranslationPacking
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    IsSharedTranslationPacking (fixedJohnPackingNormalizedGrid D hD)
      (delta / 8) (1 / 8 : NNReal) := by
  let C := fixedJohnPackingCertificate D hD
  let G := fixedJohnPackingNormalizedGrid D hD
  refine {
    mesh_pos := admissibleNormalizedRadiusPos hD
    gridVector_injective := ?_
    gridVector_norm_le := ?_
    separated := ?_
    cover_motionBall := ?_ }
  · intro g k hgk
    apply Subtype.ext
    simpa only [G, fixedJohnPackingNormalizedGrid_gridVector] using hgk
  · intro g
    have hgmem : (g.1 : Space) ∈
        Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)) :=
      C.centers_subset g.2
    simpa only [G, fixedJohnPackingNormalizedGrid_gridVector,
      Metric.mem_closedBall, dist_zero_right] using hgmem
  · intro g k hgk
    rw [fixedJohnPackingNormalizedGrid_gridVector,
      fixedJohnPackingNormalizedGrid_gridVector]
    have hsep := C.separated g.2 k.2
      (fun hval ↦ hgk (Subtype.ext hval))
    convert hsep using 1
    norm_num
  · have hrange : Set.range G.gridVector =
        (↑C.centers : Set Space) := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        rw [fixedJohnPackingNormalizedGrid_gridVector]
        change (g.1 : Space) ∈ C.centers
        simpa only [C] using g.2
      · intro hv
        change v ∈ C.centers at hv
        refine ⟨⟨v, ?_⟩, ?_⟩
        · simpa only [C] using hv
        · simp only [G, fixedJohnPackingNormalizedGrid_gridVector]
    rw [hrange]
    exact C.cover

/-- Literal sides of the representative fixed-John frame box. -/
def fixedJohnPackingSide
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : Fin 3 → NNReal :=
  (representativeTestBox (delta / 8) (admissibleNormalizedRadiusPos hD)
    (normalizedJohnCatalogueOfIndex K)).side

/-- A fixed-John test is itself exactly a frame-box body, so its dimension
certificate has comparison constant one. -/
theorem fixedJohnCatalogueBody_hasBoxDimensions
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    HasBoxDimensions 1 (fixedJohnPackingSide D hD K)
      (fixedJohnCatalogueBody hD K) := by
  let B := representativeTestBox (delta / 8)
    (admissibleNormalizedRadiusPos hD) (normalizedJohnCatalogueOfIndex K)
  change HasBoxDimensions 1 B.side B.body
  refine ⟨by norm_num, B, rfl, ?_, le_rfl⟩
  have hinv : (1 : NNReal)⁻¹ = 1 := by norm_num
  rw [hinv]
  have hrescale : B.rescale 1 = B := by
    cases B
    simp [FrameBox.rescale]
  rw [hrescale]

/-- Every representative short side dominates the packing mesh. -/
theorem normalizedRadius_le_fixedJohnPackingSide
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) (i : Fin 3) :
    delta / 8 ≤ fixedJohnPackingSide D hD K i := by
  simp only [fixedJohnPackingSide, representativeTestBox,
    FrameBox.rescale_side]
  let p := representativeParameter (delta / 8)
    (admissibleNormalizedRadiusPos hD) (normalizedJohnCatalogueOfIndex K)
  change delta / 8 ≤ 2 * p.certificate.box.side i
  rw [congrFun p.certificate.side_eq i]
  have hp : 2 * (delta / 8) ≤ p.side i :=
    p.two_mul_delta_le_side i
  nlinarith

theorem normalizedRadius_le_eighth
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota} (hD : D.IsAdmissible) :
    delta / 8 ≤ (1 / 8 : NNReal) := by
  nlinarith [hD.delta_le_half]

/-- Explicit shared-packing mean majorant for one fixed-John test. -/
def fixedJohnPackingMean
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : Real :=
  (297 * (Fintype.card iota : Real) *
      (fixedJohnPackingSide D hD K 0 : Real) *
      (fixedJohnPackingSide D hD K 1 : Real)) /
    (((1 / 8 : NNReal) : Real) ^ 2)

theorem fixedJohnPackingMean_nonneg
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    0 ≤ fixedJohnPackingMean D hD K := by
  unfold fixedJohnPackingMean
  positivity

/-- The exact finite-law mean is bounded by the honest shared-packing
incidence formula. -/
theorem fixedJohnPackingFiniteMean_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnFiniteMean (fixedJohnPackingGridVector D hD) D hD K ≤
      fixedJohnPackingMean D hD K := by
  let G := fixedJohnPackingNormalizedGrid D hD
  let P : IsSharedTranslationPacking G (delta / 8) (1 / 8 : NNReal) :=
    fixedJohnPacking_isSharedTranslationPacking D hD
  have hdim : ∀ L, HasBoxDimensions 1
      (fixedJohnPackingSide D hD L) (G.testBody L) := by
    intro L
    simpa only [G, fixedJohnPackingNormalizedGrid,
      normalizedTranslationBodyGrid] using
      fixedJohnCatalogueBody_hasBoxDimensions D hD L
  have hnormalized :
      297 * (G.tubes.card : Real) *
          (fixedJohnPackingSide D hD K 0 : Real) *
          (fixedJohnPackingSide D hD K 1 : Real) ≤
        (((1 / 8 : NNReal) : Real) ^ 2) *
          fixedJohnPackingMean D hD K := by
    simp only [G, fixedJohnPackingNormalizedGrid,
      normalizedTranslationBodyGrid, Finset.card_univ]
    unfold fixedJohnPackingMean
    norm_num [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  have havg :=
    FamilyStickyActualSharedLocalExpectationV1.average_singleLoad_le_mean
      P hdim K (Finset.mem_univ K)
      (fixedJohnPackingMean_nonneg D hD K)
      (normalizedRadius_le_fixedJohnPackingSide D hD K 0)
      (normalizedRadius_le_fixedJohnPackingSide D hD K 1)
      (normalizedRadius_le_eighth hD) hnormalized
  have hload (g : FixedJohnPackingTranslation D hD) :
      G.singleLoad K g =
        normalizedTranslationBodyLoadNat
          (fixedJohnPackingGridVector D hD) D
          (fixedJohnCatalogueBody hD) K g := by
    exact normalizedTranslationBodyGrid_singleLoad
      (fixedJohnPackingGridVector D hD) D
      (fixedJohnCatalogueBody hD) Finset.univ K g
  simpa only [fixedJohnFiniteMean, hload] using havg

/-- The exact-mean selector specialized to the canonical bounded packing
law.  There is no supplied finite type, support callback, lattice, or mean
callback. -/
theorem exists_boundedPackingTuple_normalizedConflictIndices_card_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    ∃ omega : Fin
        (fixedJohnRepetitions (fixedJohnPackingGridVector D hD) D hD) →
          FixedJohnPackingTranslation D hD,
      (∀ K : FixedJohnTest D hD,
        (∑ j, (normalizedTranslationBodyLoadNat
          (fixedJohnPackingGridVector D hD) D
          (fixedJohnCatalogueBody hD) K (omega j) : Real)) ≤
          fixedJohnTailParameter D hD *
            fixedJohnTranslationPaperCap
              (fixedJohnPackingGridVector D hD) D hD K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D)
          a).card ≤
            fixedJohnLoadThreshold
              (fixedJohnPackingGridVector D hD) D hD) := by
  exact exists_translationTuple_normalizedConflictIndices_card_le_exactMean
    (fixedJohnPackingGridVector D hD) D hD
    (fixedJohnPackingGridVector_norm_le_one D hD)

#print axioms eighthTranslationVector_fixedJohnPackingGridVector
#print axioms fixedJohnPackingGridVector_norm_le_one
#print axioms fixedJohnPacking_isSharedTranslationPacking
#print axioms fixedJohnCatalogueBody_hasBoxDimensions
#print axioms normalizedRadius_le_fixedJohnPackingSide
#print axioms fixedJohnPackingFiniteMean_le
#print axioms
  exists_boundedPackingTuple_normalizedConflictIndices_card_le

end
end Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
