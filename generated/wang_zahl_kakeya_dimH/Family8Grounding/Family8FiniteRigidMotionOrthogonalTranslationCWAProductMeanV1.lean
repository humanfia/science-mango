import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
import Family8Grounding.Family8FiniteRigidMotionOrthogonalNormalizedSupportV1
import FamilyStickyGrounding.FamilyStickyActualSharedLocalBalanceV1
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizationV4
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid
open FamilyStickyActualTranslationPointHitV1
open FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalBalanceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking

noncomputable section

/-!
# Product rotation--bounded-translation mean for John/CWA tests

This file supplies only the volume-proportional one-choice mean for the
literal product of the sampled orthogonal catalogue and the bounded shared
translation packing.  For each fixed rotation, containment of a moved tube
forces its rotated axis base to be a translation point hit.  The full
widened-box packing estimate costs `27`; covering the motion ball by the
same packing at triple mesh costs a second `27`.  Summing over rotations
therefore gives the division-free constant `729`, with no loss depending on
the number of sampled rotations.

This is deliberately not a conflict theorem and not a good-copy theorem.  In
particular it does not prove the joint `O(delta^4)` conflict incidence, choose
a Chernoff tuple, perform a greedy refinement, or prove the desired retained
copied-cardinality bound.  No Frostman or copied-cardinality conclusion is
used as an input below.
-/

/-- Literal one-motion cardinal load for an arbitrary convex test body after
the common eighth normalization. -/
def normalizedRigidBodyLoadNat
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (testBody : testIndex -> ConvexBody Space)
    (K : testIndex) (g : motionChoice) : Nat := by
  classical
  exact ((Finset.univ : Finset iota).filter fun i =>
    (eighthNormalizedTube
      (rigidTube (motion g) (D.family.tubes i))).carrier ⊆
        (testBody K : Set Space)).card

/-- The full three-dimensional point-hit estimate, kept division-free.  The
two factors `27` are respectively the widened target box and the triple-mesh
cover of the motion ball. -/
theorem card_pointHits_mul_motionBallVolume_le_card_mul_729_mul_volume
    {delta : NNReal} {translation tubeIndex : Type*}
    [Fintype translation] [DecidableEq translation]
    [DecidableEq tubeIndex]
    {G : ActualTubeTranslationGrid delta translation tubeIndex}
    {mesh motionRadius : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (B : FrameBox) (hA : A ⊆ B.carrier) (x : Space)
    (hmesh : forall i, mesh ≤ B.side i) :
    ((P.pointHits A x).card : ENNReal) * motionBallVolume P ≤
      (Fintype.card translation : ENNReal) * 729 *
        volume (B.body : Set Space) := by
  have hsideE (i : Fin 3) :
      (mesh : ENNReal) ≤ (B.side i : ENNReal) :=
    ENNReal.coe_le_coe.mpr (hmesh i)
  have hwiden (i : Fin 3) :
      (B.side i : ENNReal) + 2 * (mesh : ENNReal) ≤
        3 * (B.side i : ENNReal) := by
    calc
      (B.side i : ENNReal) + 2 * (mesh : ENNReal) ≤
          (B.side i : ENNReal) + 2 * (B.side i : ENNReal) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (hsideE i) bot_le)
      _ = 3 * (B.side i : ENNReal) := by ring
  have hhit :
      ((P.pointHits A x).card : ENNReal) * meshBallVolume P ≤
        27 * volume (B.body : Set Space) := by
    calc
      ((P.pointHits A x).card : ENNReal) * meshBallVolume P ≤
          ∏ i, ((B.side i : ENNReal) + 2 * (mesh : ENNReal)) := by
        simpa only [meshBallVolume, nsmul_eq_mul] using
          P.card_pointHits_nsmul_ballVolume_le_widenedBox A B hA x
      _ ≤ ∏ i, (3 * (B.side i : ENNReal)) :=
        Finset.prod_le_prod (fun _ _ => bot_le) (fun i _ => hwiden i)
      _ = 27 * ∏ i, (B.side i : ENNReal) := by
        rw [Finset.prod_mul_distrib]
        norm_num
      _ = 27 * volume (B.body : Set Space) := by
        rw [B.volume_body]
  have hcover :
      motionBallVolume P ≤
        (Fintype.card translation : ENNReal) * threeMeshBallVolume P := by
    simpa only [motionBallVolume, threeMeshBallVolume, nsmul_eq_mul] using
      P.volume_motionBall_le_card_smul_ballVolume_three
  have hcover27 :
      motionBallVolume P ≤
        (Fintype.card translation : ENNReal) * (27 * meshBallVolume P) := by
    calc
      motionBallVolume P ≤
          (Fintype.card translation : ENNReal) * threeMeshBallVolume P :=
        hcover
      _ = (Fintype.card translation : ENNReal) *
          (27 * meshBallVolume P) := by
        rw [threeMeshBallVolume_eq_twentySeven_mul_meshBallVolume P]
  calc
    ((P.pointHits A x).card : ENNReal) * motionBallVolume P ≤
        ((P.pointHits A x).card : ENNReal) *
          ((Fintype.card translation : ENNReal) *
            (27 * meshBallVolume P)) :=
      mul_le_mul_of_nonneg_left hcover27 bot_le
    _ = (Fintype.card translation : ENNReal) * 27 *
        (((P.pointHits A x).card : ENNReal) * meshBallVolume P) := by ring
    _ ≤ (Fintype.card translation : ENNReal) * 27 *
        (27 * volume (B.body : Set Space)) :=
      mul_le_mul_of_nonneg_left hhit bot_le
    _ = (Fintype.card translation : ENNReal) * 729 *
        volume (B.body : Set Space) := by ring

/-- Double counting upgrades the point-hit estimate to the total load of one
translation grid. -/
theorem sum_singleLoad_mul_motionBallVolume_le_card_mul_729_mul_card_mul_volume
    {delta : NNReal} {translation tubeIndex : Type*}
    [Fintype translation] [DecidableEq translation]
    [DecidableEq tubeIndex]
    {G : ActualTubeTranslationGrid delta translation tubeIndex}
    {mesh motionRadius : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (K : Fin G.testCard) (B : FrameBox)
    (hbody : G.testBody K = B.body)
    (hmesh : forall i, mesh ≤ B.side i) :
    (∑ g : translation, (G.singleLoad K g : ENNReal)) *
        motionBallVolume P ≤
      (Fintype.card translation : ENNReal) * 729 *
        (G.tubes.card : ENNReal) * volume (B.body : Set Space) := by
  have hdoubleNat :
      (∑ g : translation, G.singleLoad K g) =
        ∑ i ∈ G.tubes, G.tubeHitCount K i := by
    simpa only [toIncidenceModel_loadNat, toIncidenceModel_gridHitsTube,
      toIncidenceModel_tubes] using
      G.toIncidenceModel.sum_loadNat_eq_sum_gridHitsTube K
  have hdouble :
      (∑ g : translation, (G.singleLoad K g : ENNReal)) =
        ∑ i ∈ G.tubes, (G.tubeHitCount K i : ENNReal) := by
    exact_mod_cast hdoubleNat
  have htestSubset : (G.testBody K : Set Space) ⊆ B.carrier := by
    rw [hbody, B.coe_body]
  have hone (i : tubeIndex) :
      (G.tubeHitCount K i : ENNReal) * motionBallVolume P ≤
        (Fintype.card translation : ENNReal) * 729 *
          volume (B.body : Set Space) := by
    have hhitNat := tubeHitCount_le_pointHitCount_axisBase G K i
    rw [pointHitCount_eq_card_pointHits P K (G.tube i).axis.base] at hhitNat
    have hhit :
        (G.tubeHitCount K i : ENNReal) ≤
          ((P.pointHits (G.testBody K : Set Space)
            (G.tube i).axis.base).card : ENNReal) := by
      exact_mod_cast hhitNat
    calc
      (G.tubeHitCount K i : ENNReal) * motionBallVolume P ≤
          ((P.pointHits (G.testBody K : Set Space)
            (G.tube i).axis.base).card : ENNReal) * motionBallVolume P :=
        mul_le_mul_of_nonneg_right hhit bot_le
      _ ≤ (Fintype.card translation : ENNReal) * 729 *
          volume (B.body : Set Space) :=
        card_pointHits_mul_motionBallVolume_le_card_mul_729_mul_volume
          P (G.testBody K : Set Space) B htestSubset
            (G.tube i).axis.base hmesh
  calc
    (∑ g : translation, (G.singleLoad K g : ENNReal)) *
        motionBallVolume P =
      ∑ i ∈ G.tubes,
        (G.tubeHitCount K i : ENNReal) * motionBallVolume P := by
      rw [hdouble, Finset.sum_mul]
    _ ≤ ∑ _i ∈ G.tubes,
        (Fintype.card translation : ENNReal) * 729 *
          volume (B.body : Set Space) := by
      exact Finset.sum_le_sum fun i _hi => hone i
    _ = (Fintype.card translation : ENNReal) * 729 *
        (G.tubes.card : ENNReal) * volume (B.body : Set Space) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The rotation sample occurring in the bounded product law. -/
abbrev FixedJohnOrthogonalSample
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat) :=
  HundredOrthogonalSample (normalizedSourceTube D) (normalizedRadius_pos hD) n

/-- The literal independent product of the bounded translation packing and
the sampled orthogonal catalogue. -/
abbrev FixedJohnOrthogonalTranslationChoice
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat) :=
  FixedJohnPackingTranslation D hD × FixedJohnOrthogonalSample D hD n

/-- Raw physical rigid motion represented by one product-law outcome. -/
def fixedJohnSampledOrthogonalTranslationMotion
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (g : FixedJohnOrthogonalTranslationChoice D hD n) : RigidMotion :=
  sampledOrthogonalTranslationMotion D hD n
    (fixedJohnPackingGridVector D hD) g

/-- For one fixed sampled rotation, regard the bounded translation factor as
an ordinary actual tube-translation grid. -/
def fixedRotationJohnPackingGrid
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (r : FixedJohnOrthogonalSample D hD n) :
    ActualTubeTranslationGrid (delta / 8)
      (FixedJohnPackingTranslation D hD) iota where
  gridVector t := t.1
  tubes := Finset.univ
  tube i := rigidTube
    (orthogonalThreeRigidMotion
      (sampledHundredOrthogonal
        (normalizedSourceTube D) (normalizedRadius_pos hD) r))
    (normalizedSourceTube D i)
  testCard := Fintype.card
    (CatalogueIndex (delta / 8) (admissibleNormalizedRadiusPos hD))
  testBody := fixedJohnCatalogueBody hD
  activeTests := Finset.univ

@[simp] theorem fixedRotationJohnPackingGrid_gridVector
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (r : FixedJohnOrthogonalSample D hD n)
    (t : FixedJohnPackingTranslation D hD) :
    (fixedRotationJohnPackingGrid D hD n r).gridVector t = t.1 :=
  rfl

@[simp] theorem fixedRotationJohnPackingGrid_tubes
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (r : FixedJohnOrthogonalSample D hD n) :
    (fixedRotationJohnPackingGrid D hD n r).tubes = Finset.univ :=
  rfl

/-- Changing only the tube attached to each index leaves the shared
translation-packing certificate unchanged. -/
theorem fixedRotationJohnPacking_isSharedTranslationPacking
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (r : FixedJohnOrthogonalSample D hD n) :
    IsSharedTranslationPacking (fixedRotationJohnPackingGrid D hD n r)
      (delta / 8) (1 / 8 : NNReal) := by
  let C := fixedJohnPackingCertificate D hD
  let G := fixedRotationJohnPackingGrid D hD n r
  refine {
    mesh_pos := admissibleNormalizedRadiusPos hD
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
    simpa only [G, fixedRotationJohnPackingGrid_gridVector,
      Metric.mem_closedBall, dist_zero_right] using hgmem
  · intro g k hgk
    rw [fixedRotationJohnPackingGrid_gridVector,
      fixedRotationJohnPackingGrid_gridVector]
    have hsep := C.separated g.2 k.2
      (fun hval => hgk (Subtype.ext hval))
    convert hsep using 1
    norm_num
  · have hrange : Set.range G.gridVector =
        (↑C.centers : Set Space) := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        rw [fixedRotationJohnPackingGrid_gridVector]
        change (g.1 : Space) ∈ C.centers
        simpa only [C] using g.2
      · intro hv
        change v ∈ C.centers at hv
        refine ⟨⟨v, ?_⟩, ?_⟩
        · simpa only [C] using hv
        · simp only [G, fixedRotationJohnPackingGrid_gridVector]
    rw [hrange]
    exact C.cover

/-- Rotating first and then translating is exactly the repository's
rotation-plus-translation rigid action on a tube. -/
theorem translateTube_rigidTube_orthogonalThree
    {rho : NNReal} (T : Tube rho) (U : OrthogonalThree) (t : Space) :
    translateTube (rigidTube (orthogonalThreeRigidMotion U) T) t =
      rigidTube (orthogonalTranslationRigidMotion U t) T := by
  rw [Tube.mk.injEq, UnitSegment.mk.injEq]
  constructor
  · simp only [translateTube, translateUnitSegment_base, rigidTube_axis,
      rigidUnitSegment_base, orthogonalThreeRigidMotion_apply,
      orthogonalTranslationRigidMotion_apply]
  · simp only [translateTube, translateUnitSegment_direction, rigidTube_axis,
      rigidUnitSegment_direction, orthogonalTranslationRigidMotion_linear]
    rfl

/-- Exact alignment of the fixed-rotation translation grid with the
normalized product rigid motion. -/
theorem fixedRotationJohnPackingGrid_translateTube_eq_normalizedRigidTube
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (r : FixedJohnOrthogonalSample D hD n)
    (t : FixedJohnPackingTranslation D hD) (i : iota) :
    translateTube
        ((fixedRotationJohnPackingGrid D hD n r).tube i)
        ((fixedRotationJohnPackingGrid D hD n r).gridVector t) =
      eighthNormalizedTube
        (rigidTube
          (fixedJohnSampledOrthogonalTranslationMotion D hD n (t, r))
          (D.family.tubes i)) := by
  change
    translateTube
      (rigidTube
        (orthogonalThreeRigidMotion
          (sampledHundredOrthogonal
            (normalizedSourceTube D) (normalizedRadius_pos hD) r))
        (normalizedSourceTube D i)) t.1 =
      eighthNormalizedTube
        (rigidTube
          (orthogonalTranslationRigidMotion
            (sampledHundredOrthogonal
              (normalizedSourceTube D) (normalizedRadius_pos hD) r)
            (fixedJohnPackingGridVector D hD t))
          (D.family.tubes i))
  rw [eighthNormalizedTube_orthogonalTranslation,
    eighthTranslationVector_fixedJohnPackingGridVector]
  exact translateTube_rigidTube_orthogonalThree
    (normalizedSourceTube D i)
    (sampledHundredOrthogonal
      (normalizedSourceTube D) (normalizedRadius_pos hD) r) t.1

/-- The fixed-rotation grid load is the corresponding slice of the product
rigid-body load. -/
@[simp] theorem fixedRotationJohnPackingGrid_singleLoad
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (n : Nat)
    (r : FixedJohnOrthogonalSample D hD n)
    (K : FixedJohnTest D hD) (t : FixedJohnPackingTranslation D hD) :
    (fixedRotationJohnPackingGrid D hD n r).singleLoad K t =
      normalizedRigidBodyLoadNat
        (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
        (fixedJohnCatalogueBody hD) K (t, r) := by
  classical
  unfold ActualTubeTranslationGrid.singleLoad normalizedRigidBodyLoadNat
  apply congrArg Finset.card
  ext i
  simp only [fixedRotationJohnPackingGrid_tubes, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [fixedRotationJohnPackingGrid_translateTube_eq_normalizedRigidTube]
  rfl

/-- Division-free volume-proportional mean/load estimate for the literal
rotation-times-bounded-translation law.  In particular, after division by
the motion-ball and outcome cardinalities, the rotation catalogue contributes
no factor to the mean. -/
theorem sum_normalizedOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (n : Nat) (K : FixedJohnTest D hD) :
    (∑ g : FixedJohnOrthogonalTranslationChoice D hD n,
        (normalizedRigidBodyLoadNat
          (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
          (fixedJohnCatalogueBody hD) K g : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) ≤
      (Fintype.card
          (FixedJohnOrthogonalTranslationChoice D hD n) : ENNReal) *
        729 * (Fintype.card iota : ENNReal) *
          volume (fixedJohnCatalogueBody hD K : Set Space) := by
  let B := representativeTestBox (delta / 8)
    (admissibleNormalizedRadiusPos hD) (normalizedJohnCatalogueOfIndex K)
  have hslice (r : FixedJohnOrthogonalSample D hD n) :
      (∑ t : FixedJohnPackingTranslation D hD,
          (normalizedRigidBodyLoadNat
            (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
            (fixedJohnCatalogueBody hD) K (t, r) : ENNReal)) *
          volume (Metric.closedBall (0 : Space)
            (((1 / 8 : NNReal) : Real))) ≤
        (Fintype.card (FixedJohnPackingTranslation D hD) : ENNReal) *
          729 * (Fintype.card iota : ENNReal) *
            volume (fixedJohnCatalogueBody hD K : Set Space) := by
    let G := fixedRotationJohnPackingGrid D hD n r
    let P : IsSharedTranslationPacking G (delta / 8) (1 / 8 : NNReal) :=
      fixedRotationJohnPacking_isSharedTranslationPacking D hD n r
    have hbody : G.testBody K = B.body := by
      rfl
    have hmesh : forall j, delta / 8 ≤ B.side j := by
      intro j
      simpa only [B, fixedJohnPackingSide] using
        normalizedRadius_le_fixedJohnPackingSide D hD K j
    have h :=
      sum_singleLoad_mul_motionBallVolume_le_card_mul_729_mul_card_mul_volume
        P K B hbody hmesh
    simpa only [G, fixedRotationJohnPackingGrid_singleLoad,
      fixedRotationJohnPackingGrid_tubes, Finset.card_univ,
      motionBallVolume, B, fixedJohnCatalogueBody,
      normalizedJohnCatalogueBody, representativeTestBody] using h
  rw [Fintype.sum_prod_type_right]
  calc
    (∑ r : FixedJohnOrthogonalSample D hD n,
        ∑ t : FixedJohnPackingTranslation D hD,
          (normalizedRigidBodyLoadNat
            (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
            (fixedJohnCatalogueBody hD) K (t, r) : ENNReal)) *
        volume (Metric.closedBall (0 : Space)
          (((1 / 8 : NNReal) : Real))) =
      ∑ r : FixedJohnOrthogonalSample D hD n,
        (∑ t : FixedJohnPackingTranslation D hD,
          (normalizedRigidBodyLoadNat
            (fixedJohnSampledOrthogonalTranslationMotion D hD n) D
            (fixedJohnCatalogueBody hD) K (t, r) : ENNReal)) *
          volume (Metric.closedBall (0 : Space)
            (((1 / 8 : NNReal) : Real))) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _r : FixedJohnOrthogonalSample D hD n,
        (Fintype.card (FixedJohnPackingTranslation D hD) : ENNReal) *
          729 * (Fintype.card iota : ENNReal) *
            volume (fixedJohnCatalogueBody hD K : Set Space) := by
      exact Finset.sum_le_sum fun r _hr => hslice r
    _ = (Fintype.card
          (FixedJohnOrthogonalTranslationChoice D hD n) : ENNReal) *
        729 * (Fintype.card iota : ENNReal) *
          volume (fixedJohnCatalogueBody hD K : Set Space) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        FixedJohnOrthogonalTranslationChoice, Fintype.card_prod,
        Nat.cast_mul]
      ring

#print axioms normalizedRigidBodyLoadNat
#print axioms card_pointHits_mul_motionBallVolume_le_card_mul_729_mul_volume
#print axioms
  sum_singleLoad_mul_motionBallVolume_le_card_mul_729_mul_card_mul_volume
#print axioms fixedRotationJohnPacking_isSharedTranslationPacking
#print axioms fixedRotationJohnPackingGrid_translateTube_eq_normalizedRigidTube
#print axioms fixedRotationJohnPackingGrid_singleLoad
#print axioms
  sum_normalizedOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le

end
end Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
