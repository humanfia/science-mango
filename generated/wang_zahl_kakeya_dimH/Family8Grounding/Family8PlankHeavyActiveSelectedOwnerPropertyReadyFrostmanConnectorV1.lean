import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeGlobalKatzTaoV3
open Family8PlankLongTubeAmbientB2SupportV3
open Family8PlankLongTubeCenteredFreshV4
open Family8ActiveCoarseCanonicalFrostmanXLowerV3
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The complete-owner-fibre row reaches the existing Frostman consumer

The row datum already stores every literal source occurrence, so its genuine
long-tube datum is simply `plankLongTubeActualDatum`.  This module supplies the
thin structural bridge that was missing downstream:

* the proved nonempty-row and canonical-Frostman interfaces are reused;
* the existing centered fresh selector can therefore be called directly;
* the final Frostman call retains the density and base inequalities as the two
  explicit scalar hypotheses supplied by later analytic arguments.
-/

/-- Passing from a shaded plank family to its genuine long-tube cover and one
centering translation does not decrease average multiplicity. -/
theorem source_averageMultiplicity_le_centeredPlankLongTubeActualDatum
    {index : Type} [Fintype index] [DecidableEq index]
    (D : ShadedConvexPlankFamily index a b) :
    D.shading.averageMultiplicity ≤
      (centeredPlankLongTubeActualDatum D).shading.averageMultiplicity := by
  let motion : Unit → RigidMotion := fun _ ↦
    translationRigidMotion (-(ambientPlankCertificate D).box.center)
  have hcopy := source_averageMultiplicity_le_indexedRigidCopy
    motion (plankLongTubeActualDatum D).family
      (plankLongTubeActualDatum D).shading
  simpa only [centeredPlankLongTubeActualDatum,
    indexedRigidCopyDatum, plankLongTubeActualDatum,
    plankLongTubeCoverShading_averageMultiplicity] using hcopy

/-- The full positive connector.  Apart from row nonemptiness and scale
conditions, its only analytic inputs are the explicitly named density and
base budgets consumed by the existing deterministic Frostman theorem. -/
theorem exists_activeSelectedOwnerRow_fresh_admissible_frostman
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass :
      (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selectedCells hmass hactive thetaScale S).Nonempty)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hdelta0 : b / 8 ≤ delta0)
    (hdensityBudget :
      let P := activeSelectedOwnerRowPlankDatum
        D C q cell hcell selectedCells hmass hactive thetaScale S
      let source := centeredPlankLongTubeActualDatum P
      let canonicalC := canonicalFrostmanConstant P.family P.ambient
      let sourceC := plankLongTubeGlobalKatzTaoConstant P canonicalC
      let threshold := Nat.ceil ((480000 * (128 * sourceC) : ENNReal).toReal)
      (((b / 8 : NNReal) : ENNReal) ^ eta ≤
        (eighthNormalizedDatum source).shading.shadingDensity /
          (threshold + 1 : Nat)))
    (hbaseBudget :
      let P := activeSelectedOwnerRowPlankDatum
        D C q cell hcell selectedCells hmass hactive thetaScale S
      let canonicalC := canonicalFrostmanConstant P.family P.ambient
      let sourceC := plankLongTubeGlobalKatzTaoConstant P canonicalC
      let threshold := Nat.ceil ((480000 * (128 * sourceC) : ENNReal).toReal)
      ((threshold + 1 : Nat) : ENNReal) *
          ((128 * sourceC) * volume (unitBallBody : Set Space)) ≤
        ((b / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card (Unit × ActiveSelectedOwnerRowOccurrence
            D C q cell hcell selectedCells hmass hactive thetaScale S) : ENNReal) *
            (((b / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    let P := activeSelectedOwnerRowPlankDatum
      D C q cell hcell selectedCells hmass hactive thetaScale S
    let source := centeredPlankLongTubeActualDatum P
    let canonicalC := canonicalFrostmanConstant P.family P.ambient
    let sourceC := plankLongTubeGlobalKatzTaoConstant P canonicalC
    let threshold := Nat.ceil ((480000 * (128 * sourceC) : ENNReal).toReal)
    ∃ selected : Finset
        (Unit × ActiveSelectedOwnerRowOccurrence
          D C q cell hcell selectedCells hmass hactive thetaScale S),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum source) selected).IsAdmissible ∧
      IsKatzTao (128 * sourceC)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) selected).family.bodyFamily ∧
      P.shading.averageMultiplicity ≤
        (threshold + 1 : Nat) *
          frostmanMultiplicityRHS (b / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum source) selected).actualFamilyVolume
            epsilon beta := by
  dsimp only
  let P := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selectedCells hmass hactive thetaScale S
  let canonicalC := canonicalFrostmanConstant P.family P.ambient
  let sourceC := plankLongTubeGlobalKatzTaoConstant P canonicalC
  let source := centeredPlankLongTubeActualDatum P
  let threshold := Nat.ceil ((480000 * (128 * sourceC) : ENNReal).toReal)
  obtain ⟨selected, hselected, hadmissible, hcard, hmassRetained,
      hselectedKT, _hrowAverage⟩ :=
    exists_activeSelectedOwnerRow_fresh_admissible
      D C q cell hcell selectedCells hmass hactive thetaScale S hrow hbHalf
  have hloss0 : ((threshold + 1 : Nat) : ENNReal) ≠ 0 := by
    simp
  have hlossTop : ((threshold + 1 : Nat) : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hsourceFrostman : source.shading.averageMultiplicity ≤
      ((threshold + 1 : Nat) : ENNReal) *
        frostmanMultiplicityRHS (b / 8)
          (restrictActualTubeDatum
            (eighthNormalizedDatum source) selected).actualFamilyVolume
          epsilon beta := by
    apply source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS
      hF source selected ((threshold + 1 : Nat) : ENNReal) (128 * sourceC)
      hloss0 hlossTop hdelta0 hadmissible
    · simpa only [threshold, sourceC, canonicalC, P] using hcard
    · simpa only [threshold, sourceC, canonicalC, source, P] using hmassRetained
    · simpa only [threshold, sourceC, canonicalC, source, P] using hselectedKT
    · simpa only [threshold, sourceC, canonicalC, source, P] using hdensityBudget
    · simpa only [threshold, sourceC, canonicalC, P] using hbaseBudget
  refine ⟨selected, hselected, hadmissible, hselectedKT, ?_⟩
  exact (source_averageMultiplicity_le_centeredPlankLongTubeActualDatum P).trans
    hsourceFrostman

#print axioms activeSelectedOwnerRowPlankDatum_shadingMass
#print axioms activeSelectedOwnerRowOccurrence_card
#print axioms activeSelectedOwnerRowOccurrence_nonempty
#print axioms activeSelectedOwnerRowPlankDatum_frostmanThickenedPlankControl
#print axioms activeSelectedOwnerRow_branching_le_M_mul_theta
#print axioms activeSelectedOwnerRowPlankDatum_isFrostmanIn_canonical
#print axioms activeSelectedOwnerRowPlankDatum_canonicalFrostmanConstant_ne_top
#print axioms exists_activeSelectedOwnerRow_fresh_admissible
#print axioms exists_activeSelectedOwnerRow_fresh_admissible_frostman

end
end Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1
