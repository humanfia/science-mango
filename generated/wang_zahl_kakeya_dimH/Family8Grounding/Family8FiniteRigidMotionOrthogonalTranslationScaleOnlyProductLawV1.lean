import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizationV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
open FamilyStickySharedTranslationPackingExistenceV1
open FamilyStickySharedTranslationPackingNonemptyV1
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalBalanceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking

noncomputable section

/-!
# Scale-only orthogonal-translation product law

The finite rotation law, bounded translation packing, fixed John catalogue,
and their division-free first-moment bound require only positivity of the
source radius.  In particular, none of these constructions needs source
unit-ball support or source essential distinctness.
-/

/-- Positivity of the radius after the common eighth normalization. -/
theorem scaleOnlyNormalizedRadiusPos
    {delta : NNReal} (hdelta : 0 < delta) :
    0 < delta / 8 :=
  div_pos hdelta (by norm_num)

/-- The fixed polynomial John test type at the normalized scale. -/
abbrev ScaleOnlyFixedJohnTest
    (delta : NNReal) (hdelta : 0 < delta) :=
  Fin (Fintype.card
    (CatalogueIndex (delta / 8) (scaleOnlyNormalizedRadiusPos hdelta)))

/-- The fixed polynomial John catalogue at the normalized scale. -/
def scaleOnlyFixedJohnCatalogueBody
    {delta : NNReal} (hdelta : 0 < delta) :
    ScaleOnlyFixedJohnTest delta hdelta -> ConvexBody Space :=
  normalizedJohnCatalogueBody (delta / 8)
    (scaleOnlyNormalizedRadiusPos hdelta)

/-- A maximal finite packing of the normalized motion ball at mesh
`delta / 8`. -/
def scaleOnlyFixedJohnPackingCertificate
    (delta : NNReal) (hdelta : 0 < delta) :
    PackingCertificate
      (Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)))
      (delta / 8) :=
  Classical.choice
    (exists_motionBallPackingCertificate (1 / 8 : NNReal) (delta / 8)
      (scaleOnlyNormalizedRadiusPos hdelta))

/-- The literal finite translation outcome type of the bounded law. -/
abbrev ScaleOnlyFixedJohnPackingTranslation
    (delta : NNReal) (hdelta : 0 < delta) :=
  ↥(scaleOnlyFixedJohnPackingCertificate delta hdelta).centers

noncomputable instance scaleOnlyFixedJohnPackingTranslationNonempty
    (delta : NNReal) (hdelta : 0 < delta) :
    Nonempty (ScaleOnlyFixedJohnPackingTranslation delta hdelta) :=
  motionBallPackingCertificate_translation_nonempty
    (scaleOnlyFixedJohnPackingCertificate delta hdelta)

/-- Convert a normalized packing centre into the corresponding physical
translation vector. -/
def scaleOnlyFixedJohnPackingGridVector
    {delta : NNReal} (hdelta : 0 < delta)
    (g : ScaleOnlyFixedJohnPackingTranslation delta hdelta) : Space :=
  (8 : Real) • (g.1 : Space)

@[simp] theorem eighthTranslationVector_scaleOnlyFixedJohnPackingGridVector
    {delta : NNReal} (hdelta : 0 < delta)
    (g : ScaleOnlyFixedJohnPackingTranslation delta hdelta) :
    eighthTranslationVector
        (scaleOnlyFixedJohnPackingGridVector hdelta g) = g.1 := by
  unfold eighthTranslationVector scaleOnlyFixedJohnPackingGridVector
  module

/-- Every physical translation represented by the bounded packing has norm
at most one. -/
theorem scaleOnlyFixedJohnPackingGridVector_norm_le_one
    {delta : NNReal} (hdelta : 0 < delta)
    (g : ScaleOnlyFixedJohnPackingTranslation delta hdelta) :
    ‖scaleOnlyFixedJohnPackingGridVector hdelta g‖ ≤ 1 := by
  have hgmem : (g.1 : Space) ∈
      Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)) :=
    (scaleOnlyFixedJohnPackingCertificate delta hdelta).centers_subset g.2
  have hg : ‖(g.1 : Space)‖ ≤ (((1 / 8 : NNReal) : Real)) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hgmem
  calc
    ‖scaleOnlyFixedJohnPackingGridVector hdelta g‖ =
        8 * ‖(g.1 : Space)‖ := by
      simp [scaleOnlyFixedJohnPackingGridVector, norm_smul]
    _ ≤ 8 * (((1 / 8 : NNReal) : Real)) :=
      mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = 1 := by norm_num

/-- The sampled orthogonal catalogue based on the normalized source tubes. -/
abbrev ScaleOnlyFixedJohnOrthogonalSample
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat) :=
  HundredOrthogonalSample (normalizedSourceTube D)
    (scaleOnlyNormalizedRadiusPos hdelta) n

/-- The independent bounded-translation times sampled-rotation outcome. -/
abbrev ScaleOnlyFixedJohnOrthogonalTranslationChoice
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat) :=
  ScaleOnlyFixedJohnPackingTranslation delta hdelta ×
    ScaleOnlyFixedJohnOrthogonalSample D hdelta n

/-- The physical rigid motion represented by one product-law outcome. -/
def scaleOnlyFixedJohnSampledOrthogonalTranslationMotion
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (g : ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) :
    RigidMotion :=
  orthogonalTranslationRigidMotion
    (sampledHundredOrthogonal (normalizedSourceTube D)
      (scaleOnlyNormalizedRadiusPos hdelta) g.2)
    (scaleOnlyFixedJohnPackingGridVector hdelta g.1)

/-- For a fixed sampled rotation, the translation factor is an actual shared
translation grid with an arbitrary finite family of convex tests. -/
def scaleOnlyFixedRotationPackingGrid
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {testCard : Nat}
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (testBody : Fin testCard -> ConvexBody Space)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
    ActualTubeTranslationGrid (delta / 8)
      (ScaleOnlyFixedJohnPackingTranslation delta hdelta) iota where
  gridVector t := t.1
  tubes := Finset.univ
  tube i := rigidTube
    (orthogonalThreeRigidMotion
      (sampledHundredOrthogonal (normalizedSourceTube D)
        (scaleOnlyNormalizedRadiusPos hdelta) r))
    (normalizedSourceTube D i)
  testCard := testCard
  testBody := testBody
  activeTests := Finset.univ

@[simp] theorem scaleOnlyFixedRotationPackingGrid_gridVector
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {testCard : Nat}
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (testBody : Fin testCard -> ConvexBody Space)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n)
    (t : ScaleOnlyFixedJohnPackingTranslation delta hdelta) :
    (scaleOnlyFixedRotationPackingGrid D hdelta n testBody r).gridVector t =
      t.1 :=
  rfl

@[simp] theorem scaleOnlyFixedRotationPackingGrid_tubes
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {testCard : Nat}
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (testBody : Fin testCard -> ConvexBody Space)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
    (scaleOnlyFixedRotationPackingGrid D hdelta n testBody r).tubes =
      Finset.univ :=
  rfl

/-- Changing the rotated tube attached to each source index does not change
the shared translation-packing certificate. -/
theorem scaleOnlyFixedRotation_isSharedTranslationPacking
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {testCard : Nat}
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (testBody : Fin testCard -> ConvexBody Space)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
    IsSharedTranslationPacking
      (scaleOnlyFixedRotationPackingGrid D hdelta n testBody r)
      (delta / 8) (1 / 8 : NNReal) := by
  let C := scaleOnlyFixedJohnPackingCertificate delta hdelta
  let G := scaleOnlyFixedRotationPackingGrid D hdelta n testBody r
  refine {
    mesh_pos := scaleOnlyNormalizedRadiusPos hdelta
    gridVector_injective := ?_
    gridVector_norm_le := ?_
    separated := ?_
    cover_motionBall := ?_ }
  · intro g k hgk
    exact Subtype.ext hgk
  · intro g
    have hgmem : (g.1 : Space) ∈
        Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)) :=
      C.centers_subset g.2
    simpa only [G, scaleOnlyFixedRotationPackingGrid_gridVector,
      Metric.mem_closedBall, dist_zero_right] using hgmem
  · intro g k hgk
    rw [scaleOnlyFixedRotationPackingGrid_gridVector,
      scaleOnlyFixedRotationPackingGrid_gridVector]
    have hsep := C.separated g.2 k.2
      (fun hval => hgk (Subtype.ext hval))
    convert hsep using 1
    norm_num
  · have hrange : Set.range G.gridVector =
        (↑C.centers : Set Space) := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        rw [scaleOnlyFixedRotationPackingGrid_gridVector]
        change (g.1 : Space) ∈ C.centers
        simpa only [C] using g.2
      · intro hv
        change v ∈ C.centers at hv
        refine ⟨⟨v, ?_⟩, ?_⟩
        · simpa only [C] using hv
        · simp only [G, scaleOnlyFixedRotationPackingGrid_gridVector]
    rw [hrange]
    exact C.cover

/-- The fixed-rotation translation grid is exactly the normalized physical
product motion. -/
theorem scaleOnlyFixedRotationPackingGrid_translateTube_eq_normalizedRigidTube
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {testCard : Nat}
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (testBody : Fin testCard -> ConvexBody Space)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n)
    (t : ScaleOnlyFixedJohnPackingTranslation delta hdelta) (i : iota) :
    translateTube
        ((scaleOnlyFixedRotationPackingGrid D hdelta n testBody r).tube i)
        ((scaleOnlyFixedRotationPackingGrid D hdelta n testBody r).gridVector t) =
      eighthNormalizedTube
        (rigidTube
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion
            D hdelta n (t, r))
          (D.family.tubes i)) := by
  change
    translateTube
      (rigidTube
        (orthogonalThreeRigidMotion
          (sampledHundredOrthogonal (normalizedSourceTube D)
            (scaleOnlyNormalizedRadiusPos hdelta) r))
        (normalizedSourceTube D i)) t.1 =
      eighthNormalizedTube
        (rigidTube
          (orthogonalTranslationRigidMotion
            (sampledHundredOrthogonal (normalizedSourceTube D)
              (scaleOnlyNormalizedRadiusPos hdelta) r)
            (scaleOnlyFixedJohnPackingGridVector hdelta t))
          (D.family.tubes i))
  rw [eighthNormalizedTube_orthogonalTranslation,
    eighthTranslationVector_scaleOnlyFixedJohnPackingGridVector]
  exact translateTube_rigidTube_orthogonalThree
    (normalizedSourceTube D i)
    (sampledHundredOrthogonal (normalizedSourceTube D)
      (scaleOnlyNormalizedRadiusPos hdelta) r) t.1

/-- The fixed-rotation grid load equals the corresponding slice of the
product rigid-body load. -/
@[simp] theorem scaleOnlyFixedRotationPackingGrid_singleLoad
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {testCard : Nat}
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (testBody : Fin testCard -> ConvexBody Space)
    (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n)
    (K : Fin testCard)
    (t : ScaleOnlyFixedJohnPackingTranslation delta hdelta) :
    (scaleOnlyFixedRotationPackingGrid D hdelta n testBody r).singleLoad K t =
      normalizedRigidBodyLoadNat
        (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n)
        D testBody K (t, r) := by
  classical
  unfold ActualTubeTranslationGrid.singleLoad normalizedRigidBodyLoadNat
  apply congrArg Finset.card
  ext i
  simp only [scaleOnlyFixedRotationPackingGrid_tubes, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [scaleOnlyFixedRotationPackingGrid_translateTube_eq_normalizedRigidTube]
  rfl

/-- Division-free mean bound for an arbitrary frame-box test. -/
theorem sum_scaleOnlyOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {testCard : Nat}
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (testBody : Fin testCard -> ConvexBody Space)
    (K : Fin testCard) (B : FrameBox)
    (hbody : testBody K = B.body)
    (hmesh : forall j, delta / 8 ≤ B.side j) :
    (∑ g : ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n,
        (normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n)
          D testBody K g : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) :
            ENNReal) *
        729 * (Fintype.card iota : ENNReal) *
          volume (testBody K : Set Space) := by
  have hslice (r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :
      (∑ t : ScaleOnlyFixedJohnPackingTranslation delta hdelta,
          (normalizedRigidBodyLoadNat
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n)
            D testBody K (t, r) : ENNReal)) *
          volume (Metric.closedBall (0 : Space)
            (((1 / 8 : NNReal) : Real))) ≤
        (Fintype.card
            (ScaleOnlyFixedJohnPackingTranslation delta hdelta) : ENNReal) *
          729 * (Fintype.card iota : ENNReal) *
            volume (testBody K : Set Space) := by
    let G := scaleOnlyFixedRotationPackingGrid D hdelta n testBody r
    let P : IsSharedTranslationPacking G (delta / 8) (1 / 8 : NNReal) :=
      scaleOnlyFixedRotation_isSharedTranslationPacking
        D hdelta n testBody r
    have hbodyG : G.testBody K = B.body := hbody
    have h :=
      sum_singleLoad_mul_motionBallVolume_le_card_mul_729_mul_card_mul_volume
        P K B hbodyG hmesh
    simpa only [G, scaleOnlyFixedRotationPackingGrid_singleLoad,
      scaleOnlyFixedRotationPackingGrid_tubes, Finset.card_univ,
      motionBallVolume, hbody] using h
  rw [Fintype.sum_prod_type_right]
  calc
    (∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        ∑ t : ScaleOnlyFixedJohnPackingTranslation delta hdelta,
          (normalizedRigidBodyLoadNat
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n)
            D testBody K (t, r) : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) =
      ∑ r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        (∑ t : ScaleOnlyFixedJohnPackingTranslation delta hdelta,
          (normalizedRigidBodyLoadNat
            (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n)
            D testBody K (t, r) : ENNReal)) *
          volume (Metric.closedBall (0 : Space)
            (((1 / 8 : NNReal) : Real))) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _r : ScaleOnlyFixedJohnOrthogonalSample D hdelta n,
        (Fintype.card
            (ScaleOnlyFixedJohnPackingTranslation delta hdelta) : ENNReal) *
          729 * (Fintype.card iota : ENNReal) *
            volume (testBody K : Set Space) := by
      exact Finset.sum_le_sum fun r _hr => hslice r
    _ = (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) :
            ENNReal) *
        729 * (Fintype.card iota : ENNReal) *
          volume (testBody K : Set Space) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ScaleOnlyFixedJohnOrthogonalTranslationChoice, Fintype.card_prod,
        Nat.cast_mul]
      ring

/-- Every side of the representative fixed-John box dominates the normalized
packing mesh. -/
theorem scaleOnlyNormalizedRadius_le_fixedJohnTestBoxSide
    {delta : NNReal} (hdelta : 0 < delta)
    (K : ScaleOnlyFixedJohnTest delta hdelta) (i : Fin 3) :
    delta / 8 ≤
      (representativeTestBox (delta / 8)
        (scaleOnlyNormalizedRadiusPos hdelta)
        (normalizedJohnCatalogueOfIndex K)).side i := by
  simp only [representativeTestBox, FrameBox.rescale_side]
  let p := representativeParameter (delta / 8)
    (scaleOnlyNormalizedRadiusPos hdelta)
    (normalizedJohnCatalogueOfIndex K)
  change delta / 8 ≤ 2 * p.certificate.box.side i
  rw [congrFun p.certificate.side_eq i]
  have hp : 2 * (delta / 8) ≤ p.side i :=
    p.two_mul_delta_le_side i
  nlinarith

/-- The scale-only fixed-John catalogue satisfies the exact division-free
product-law mean bound. -/
theorem sum_scaleOnlyFixedJohnOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) (n : Nat)
    (K : ScaleOnlyFixedJohnTest delta hdelta) :
    (∑ g : ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n,
        (normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n)
          D (scaleOnlyFixedJohnCatalogueBody hdelta) K g : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta n) :
            ENNReal) *
        729 * (Fintype.card iota : ENNReal) *
          volume (scaleOnlyFixedJohnCatalogueBody hdelta K : Set Space) := by
  let B := representativeTestBox (delta / 8)
    (scaleOnlyNormalizedRadiusPos hdelta)
    (normalizedJohnCatalogueOfIndex K)
  apply sum_scaleOnlyOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le
    D hdelta n (scaleOnlyFixedJohnCatalogueBody hdelta) K B
  · rfl
  · intro i
    exact scaleOnlyNormalizedRadius_le_fixedJohnTestBoxSide hdelta K i

#print axioms scaleOnlyNormalizedRadiusPos
#print axioms scaleOnlyFixedJohnPackingGridVector_norm_le_one
#print axioms scaleOnlyFixedRotation_isSharedTranslationPacking
#print axioms
  scaleOnlyFixedRotationPackingGrid_translateTube_eq_normalizedRigidTube
#print axioms scaleOnlyFixedRotationPackingGrid_singleLoad
#print axioms
  sum_scaleOnlyOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le
#print axioms
  sum_scaleOnlyFixedJohnOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
