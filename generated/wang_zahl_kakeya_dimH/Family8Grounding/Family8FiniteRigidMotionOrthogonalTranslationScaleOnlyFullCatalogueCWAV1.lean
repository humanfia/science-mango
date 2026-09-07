import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
import Family8Grounding.Family8FiniteRigidMotionB2SourceNormalizedSupportV1
import Family8Grounding.Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1
import Family8Grounding.Family8PolynomialJohnFrameBoxCardinalAllConvexV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRigidMotionB2SourceNormalizedSupportV1
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalNormalizedChoiceV3
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
open Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
open Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8PolynomialJohnFrameBoxCardinalAllConvexV1

noncomputable section

/-!
# Scale-only full-catalogue Convex Wolff bridge

The joint scale-only selector controls the complete polynomial John catalogue
for one selected tuple of orthogonal--translation motions.  This module
converts precisely that tail into the cardinal-normalized Convex Wolff axioms
for the full product copy, before any fresh greedy restriction.

Raw `B(0,2)` support is used only to put each moved, eighth-normalized tube in
the unit ball.  No admissibility, essential-distinctness, `BoundAt`, or
Family 7 conclusion is involved.
-/

/-- The exact cardinal-normalized coefficient supplied by a scale-only John
tail.  The universal John-catalogue volume loss is applied separately in the
Convex Wolff conclusion. -/
def scaleOnlyFullCopiedCWAParameter
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (_D : ActualTubeDatum delta iota) (_hdelta : 0 < delta)
    (repetitions : Nat) (AJohn : Real) (C : ENNReal) : ENNReal :=
  (ENNReal.ofReal AJohn * C / scaleOnlyJointHalfSq delta) /
    (Fintype.card (Fin repetitions × iota) : ENNReal)

/-- A selected scale-only tuple satisfying the complete John-catalogue tail
satisfies the literal cardinal-normalized Convex Wolff axioms on its full
eighth-normalized indexed rigid-copy family. -/
theorem fullNormalizedCopied_satisfiesConvexWolffAxioms_of_scaleOnlyJohnTail
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hB2 : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {repetitions : Nat}
    (omega : Fin repetitions → ScaleOnlyJointChoice D hdelta)
    (AJohn : Real) (hAJohn : 0 ≤ AJohn)
    {C : ENNReal} (hCTop : C ≠ ∞)
    (htail : ∀ K : ScaleOnlyFixedJohnTest delta hdelta,
      (∑ j, scaleOnlyJointJohnLoad D hdelta K (omega j)) ≤
        AJohn * scaleOnlyJointJohnCap C D hdelta K) :
    SatisfiesConvexWolffAxioms
      (scaleOnlyFullCopiedCWAParameter D hdelta repetitions AJohn C *
        johnCatalogueVolumeConstant)
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j ↦
            scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
              (scaleOnlyOrthogonalCatalogueScale D hdelta) (omega j)) D)).family.bodyFamily := by
  classical
  let n := scaleOnlyOrthogonalCatalogueScale D hdelta
  let motion : ScaleOnlyJointChoice D hdelta → RigidMotion :=
    scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta n
  let copied := indexedRigidCopyDatum (fun j ↦ motion (omega j)) D
  let normalized := eighthNormalizedDatum copied
  let fullCard : ENNReal :=
    Fintype.card (Fin repetitions × iota)
  let lower : ENNReal := scaleOnlyJointHalfSq delta
  let B : ENNReal := ENNReal.ofReal AJohn * C / lower
  have hlower0 : lower ≠ 0 := by
    dsimp only [lower, scaleOnlyJointHalfSq]
    apply ENNReal.div_ne_zero.mpr
    exact ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr
      (div_pos hdelta (by norm_num)).ne'), by norm_num⟩
  have hfullCardTop : fullCard ≠ ∞ := by
    dsimp only [fullCard]
    exact ENNReal.coe_ne_top
  have hunit : ∀ a : Fin repetitions × iota,
      (normalized.family.tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
    intro a
    change
      (eighthNormalizedTube
        (rigidTube
          (orthogonalTranslationRigidMotion
            (sampledHundredOrthogonal (normalizedSourceTube D)
              (scaleOnlyNormalizedRadiusPos hdelta) (omega a.1).2)
            (scaleOnlyFixedJohnPackingGridVector hdelta (omega a.1).1))
          (D.family.tubes a.2))).carrier ⊆
        Metric.closedBall (0 : Space) 1
    exact
      eighthNormalized_orthogonalTranslation_carrier_subset_unitBall_of_B2
        (D.family.tubes a.2) hdeltaHalf (hB2 a.2)
        (sampledHundredOrthogonal (normalizedSourceTube D)
          (scaleOnlyNormalizedRadiusPos hdelta) (omega a.1).2)
        (scaleOnlyFixedJohnPackingGridVector hdelta (omega a.1).1)
        (scaleOnlyFixedJohnPackingGridVector_norm_le_one
          hdelta (omega a.1).1)
  apply satisfiesConvexWolffAxioms_of_polynomialJohnCatalogue
    (scaleOnlyNormalizedRadiusPos hdelta) normalized.family.tubes hunit
      (B / fullCard)
  intro q
  change
    ((containedIndices normalized.family.bodyFamily
      (representativeTestBody (delta / 8)
        (scaleOnlyNormalizedRadiusPos hdelta) q)).card : ENNReal) ≤
      (B / fullCard) *
        volume (representativeTestBody (delta / 8)
          (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) * fullCard
  by_cases hfullCard0 : fullCard = 0
  · have hcard :
        ((containedIndices normalized.family.bodyFamily
          (representativeTestBody (delta / 8)
            (scaleOnlyNormalizedRadiusPos hdelta) q)).card : ENNReal) ≤
          fullCard := by
      dsimp only [fullCard]
      exact_mod_cast Finset.card_le_univ
        (containedIndices normalized.family.bodyFamily
          (representativeTestBody (delta / 8)
            (scaleOnlyNormalizedRadiusPos hdelta) q))
    simpa only [hfullCard0, mul_zero] using hcard
  · let K : ScaleOnlyFixedJohnTest delta hdelta :=
      normalizedJohnCatalogueIndex q
    have hindices :
        normalizedRigidBodyIndices motion D
            (scaleOnlyFixedJohnCatalogueBody hdelta) omega K =
          containedIndices normalized.family.bodyFamily
            (representativeTestBody (delta / 8)
              (scaleOnlyNormalizedRadiusPos hdelta) q) := by
      ext b
      simp only [normalizedRigidBodyIndices, Finset.mem_filter,
        Finset.mem_univ, true_and, mem_containedIndices,
        UniformTubeFamily.bodyFamily_apply, Tube.coe_body, normalized,
        copied, motion, n, eighthNormalizedDatum_family,
        eighthNormalizedTubeFamily_tubes, indexedRigidCopyDatum,
        indexedRigidCopyTubeFamily_tubes, scaleOnlyFixedJohnCatalogueBody,
        normalizedJohnCatalogueBody_index, K]
    have hcountNat :
        (containedIndices normalized.family.bodyFamily
          (representativeTestBody (delta / 8)
            (scaleOnlyNormalizedRadiusPos hdelta) q)).card =
          ∑ j, normalizedRigidBodyLoadNat motion D
            (scaleOnlyFixedJohnCatalogueBody hdelta) K (omega j) := by
      rw [← hindices]
      exact normalizedRigidBodyIndices_card_eq_sum_load motion D
        (scaleOnlyFixedJohnCatalogueBody hdelta) omega K
    have hcountReal :
        ((containedIndices normalized.family.bodyFamily
          (representativeTestBody (delta / 8)
            (scaleOnlyNormalizedRadiusPos hdelta) q)).card : Real) ≤
          AJohn *
            (C * volume
                (representativeTestBody (delta / 8)
                  (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) /
              lower).toReal := by
      have h := htail K
      rw [hcountNat]
      simpa only [Nat.cast_sum, scaleOnlyJointJohnLoad, scaleOnlyJointJohnCap,
        scaleOnlyFixedJohnCatalogueBody, normalizedJohnCatalogueBody_index,
        lower, K, n, motion] using h
    have hratioTop :
        C * volume
              (representativeTestBody (delta / 8)
                (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) /
            lower ≠ ∞ := by
      exact ENNReal.div_ne_top
        (ENNReal.mul_ne_top hCTop
          (representativeTestBody (delta / 8)
            (scaleOnlyNormalizedRadiusPos hdelta) q).isCompact.measure_lt_top.ne)
        hlower0
    have hcountENN :
        ((containedIndices normalized.family.bodyFamily
          (representativeTestBody (delta / 8)
            (scaleOnlyNormalizedRadiusPos hdelta) q)).card : ENNReal) ≤
          ENNReal.ofReal AJohn *
            (C * volume
                (representativeTestBody (delta / 8)
                  (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) /
              lower) := by
      apply (ENNReal.toReal_le_toReal ENNReal.coe_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hratioTop)).mp
      calc
        (((containedIndices normalized.family.bodyFamily
            (representativeTestBody (delta / 8)
              (scaleOnlyNormalizedRadiusPos hdelta) q)).card : ENNReal)).toReal =
            ((containedIndices normalized.family.bodyFamily
              (representativeTestBody (delta / 8)
                (scaleOnlyNormalizedRadiusPos hdelta) q)).card : Real) := by
          norm_num
        _ ≤ AJohn *
              (C * volume
                  (representativeTestBody (delta / 8)
                    (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) /
                lower).toReal := hcountReal
        _ = (ENNReal.ofReal AJohn *
              (C * volume
                  (representativeTestBody (delta / 8)
                    (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) /
                lower)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hAJohn]
    calc
      ((containedIndices normalized.family.bodyFamily
          (representativeTestBody (delta / 8)
            (scaleOnlyNormalizedRadiusPos hdelta) q)).card : ENNReal) ≤
          ENNReal.ofReal AJohn *
            (C * volume
                (representativeTestBody (delta / 8)
                  (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) /
              lower) := hcountENN
      _ = B * volume
            (representativeTestBody (delta / 8)
              (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) := by
        simp only [B, div_eq_mul_inv]
        ac_rfl
      _ = (B / fullCard) *
            volume (representativeTestBody (delta / 8)
              (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) *
            (Fintype.card (Fin repetitions × iota) : ENNReal) := by
        dsimp only [fullCard]
        symm
        calc
          (B / (Fintype.card (Fin repetitions × iota) : ENNReal)) *
                volume (representativeTestBody (delta / 8)
                  (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) *
                (Fintype.card (Fin repetitions × iota) : ENNReal) =
              (B / (Fintype.card (Fin repetitions × iota) : ENNReal)) *
                (Fintype.card (Fin repetitions × iota) : ENNReal) *
                volume (representativeTestBody (delta / 8)
                  (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) := by
            ac_rfl
          _ = B * volume
                (representativeTestBody (delta / 8)
                  (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) := by
            rw [ENNReal.div_mul_cancel]
            · exact hfullCard0
            · exact hfullCardTop
      _ = (scaleOnlyFullCopiedCWAParameter
              D hdelta repetitions AJohn C) *
            volume (representativeTestBody (delta / 8)
              (scaleOnlyNormalizedRadiusPos hdelta) q : Set Space) *
            (Fintype.card (Fin repetitions × iota) : ENNReal) := by
        rfl

#print axioms scaleOnlyFullCopiedCWAParameter
#print axioms
  fullNormalizedCopied_satisfiesConvexWolffAxioms_of_scaleOnlyJohnTail

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1
