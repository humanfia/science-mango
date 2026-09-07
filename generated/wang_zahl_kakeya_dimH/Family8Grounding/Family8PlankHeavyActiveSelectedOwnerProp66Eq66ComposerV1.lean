import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankHeavyActiveSelectedOwnerProp66Eq66ComposerV1

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
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The complete-owner row as a same-object Prop. 6.6 / Eq. 66 seam

This module does not assert the missing `M ^ (beta / 2)` aggregation.  It
packages one literal complete-owner row, its centered/eighth-normalized fresh
selection, and every structural fact already proved for exactly that row.
The four analytic seams remain visibly named:

* correlation of the downstream actual-third average with this row average;
* the normalized density power budget;
* the normalized Frostman base budget;
* the final cross-row aggregation into the exact convex-plank factor.

Consequently the endpoint below is a conditional composer, not a new proof
of the general convex-plank Frostman multiplicity hypothesis.
-/

/-- The one complete-owner row used everywhere in this module.  In
particular, the row scale is the same `theta` appearing in the original
thickened-plank control. -/
abbrev PropertyReadyRowDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) :=
  activeSelectedOwnerRowPlankDatum
    D C q cell hcell selectedCells hmass hactive theta S

/-- The literal, injectively source-indexed occurrence type of the row. -/
abbrev PropertyReadyRowOccurrence
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) :=
  ActiveSelectedOwnerRowOccurrence
    D C q cell hcell selectedCells hmass hactive theta S

/-- The centered genuine long-tube source associated to the same row. -/
abbrev PropertyReadyRowSource
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) :=
  centeredPlankLongTubeActualDatum
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S)

/-- The canonical finite Frostman constant of this row, not of a proxy. -/
def propertyReadyRowCanonicalFrostmanConstant
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) : ENNReal :=
  let P := PropertyReadyRowDatum
    D C q cell hcell selectedCells hmass hactive S
  canonicalFrostmanConstant P.family P.ambient

/-- The global Katz--Tao constant of the genuine long-tube cover of this
same row. -/
def propertyReadyRowSourceKatzTaoConstant
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) : ENNReal :=
  let P := PropertyReadyRowDatum
    D C q cell hcell selectedCells hmass hactive S
  plankLongTubeGlobalKatzTaoConstant P
    (propertyReadyRowCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive S)

/-- The exact deterministic fresh-selection bucket threshold. -/
def propertyReadyRowFreshThreshold
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) : Nat :=
  Nat.ceil ((480000 * (128 * propertyReadyRowSourceKatzTaoConstant
    D C q cell hcell selectedCells hmass hactive S) : ENNReal).toReal)

/-- The exact ENNReal loss occurring in the fresh-selection theorem. -/
def propertyReadyRowFreshLoss
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) : ENNReal :=
  ((propertyReadyRowFreshThreshold
    D C q cell hcell selectedCells hmass hactive S + 1 : Nat) : ENNReal)

/-- The restricted fresh datum selected from the normalized same-row source. -/
abbrev PropertyReadySelectedRowDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space)
    (selected : Finset (Unit × PropertyReadyRowOccurrence
      D C q cell hcell selectedCells hmass hactive S)) :=
  restrictActualTubeDatum
    (eighthNormalizedDatum (PropertyReadyRowSource
      D C q cell hcell selectedCells hmass hactive S)) selected

/-- The exact convex-plank factor for the same row, its canonical Frostman
constant, and the inherited original `M`.  Expanding this definition exposes
the required `M ^ (beta / 2)` term. -/
def propertyReadyRowProp66Factor
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) (epsilon beta : Real) (M : NNReal) : ENNReal :=
  convexPlankFrostmanFactor
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S)
    epsilon beta
    (propertyReadyRowCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive S) M

/-- Named downstream obligation tying the actual-third scalar to this exact
row average. -/
def ActualThirdAverageCorrelationObligation
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space)
    (actualThirdAverage correlationLoss : ENNReal) : Prop :=
  actualThirdAverage ≤ correlationLoss *
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S).shading.averageMultiplicity

/-- Named density-power obligation consumed by the existing normalized
Frostman theorem. -/
def DensityPowerBudgetObligation
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) (eta : Real) : Prop :=
  (((b / 8 : NNReal) : ENNReal) ^ eta) ≤
    (eighthNormalizedDatum (PropertyReadyRowSource
      D C q cell hcell selectedCells hmass hactive S)).shading.shadingDensity /
      propertyReadyRowFreshLoss
        D C q cell hcell selectedCells hmass hactive S

/-- Named base-budget obligation consumed by the same normalized Frostman
call. -/
def BaseBudgetObligation
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) (eta : Real) : Prop :=
  propertyReadyRowFreshLoss
      D C q cell hcell selectedCells hmass hactive S *
      ((128 * propertyReadyRowSourceKatzTaoConstant
          D C q cell hcell selectedCells hmass hactive S) *
        volume (unitBallBody : Set Space)) ≤
    ((b / 8 : NNReal) : ENNReal) ^ (-eta) *
      ((Fintype.card (Unit × PropertyReadyRowOccurrence
        D C q cell hcell selectedCells hmass hactive S) : ENNReal) *
        (((b / 8 : NNReal) : ENNReal) ^ 2 / 2))

/-- The genuinely missing analytic aggregation.  Its conclusion is the
same-row convex-plank factor and therefore contains the inherited
`M ^ (beta / 2)` term; no theorem in this module fabricates it. -/
def CrossRowAggregationObligation
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space) (epsilon beta : Real) (M : NNReal)
    (correlationLoss : ENNReal)
    (selected : Finset (Unit × PropertyReadyRowOccurrence
      D C q cell hcell selectedCells hmass hactive S)) : Prop :=
  correlationLoss *
      (propertyReadyRowFreshLoss
          D C q cell hcell selectedCells hmass hactive S *
        frostmanMultiplicityRHS (b / 8)
          (PropertyReadySelectedRowDatum
            D C q cell hcell selectedCells hmass hactive S selected).actualFamilyVolume
          epsilon beta) ≤
    propertyReadyRowProp66Factor
      D C q cell hcell selectedCells hmass hactive S epsilon beta M

/-- A same-object certificate for the positive row-to-Prop66/Eq66 seam.
The five producer obligations remain explicit; all other fields below are
filled by existing row and fresh-selection theorems. -/
structure PropertyReadyRowProp66Eq66Composer
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space)
    (epsilon beta eta : Real) (M : NNReal)
    (actualThirdAverage correlationLoss : ENNReal) where
  hrow : (activeSelectedOwnersInCertifiedSlab
    D C q cell hcell selectedCells hmass hactive theta S).Nonempty
  actualThirdAverage_correlation :
    ActualThirdAverageCorrelationObligation
      D C q cell hcell selectedCells hmass hactive S
        actualThirdAverage correlationLoss
  densityPowerBudget : DensityPowerBudgetObligation
    D C q cell hcell selectedCells hmass hactive S eta
  baseBudget : BaseBudgetObligation
    D C q cell hcell selectedCells hmass hactive S eta
  selected : Finset (Unit × PropertyReadyRowOccurrence
    D C q cell hcell selectedCells hmass hactive S)
  selected_nonempty : selected.Nonempty
  selected_admissible : (PropertyReadySelectedRowDatum
    D C q cell hcell selectedCells hmass hactive S selected).IsAdmissible
  fresh_card_retained :
    (Fintype.card (Unit × PropertyReadyRowOccurrence
      D C q cell hcell selectedCells hmass hactive S) : ENNReal) ≤
      propertyReadyRowFreshLoss
        D C q cell hcell selectedCells hmass hactive S *
          (selected.card : ENNReal)
  fresh_mass_retained :
    (eighthNormalizedDatum (PropertyReadyRowSource
      D C q cell hcell selectedCells hmass hactive S)).shading.shadingMass ≤
      propertyReadyRowFreshLoss
          D C q cell hcell selectedCells hmass hactive S *
        (PropertyReadySelectedRowDatum
          D C q cell hcell selectedCells hmass hactive S selected).shading.shadingMass
  selected_katzTao :
    IsKatzTao
      (128 * propertyReadyRowSourceKatzTaoConstant
        D C q cell hcell selectedCells hmass hactive S)
      (PropertyReadySelectedRowDatum
        D C q cell hcell selectedCells hmass hactive S selected).family.bodyFamily
  row_average_fresh_retained :
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S).shading.averageMultiplicity ≤
      propertyReadyRowFreshLoss
          D C q cell hcell selectedCells hmass hactive S *
        (PropertyReadySelectedRowDatum
          D C q cell hcell selectedCells hmass hactive S selected).shading.averageMultiplicity
  row_average_le_frostman :
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S).shading.averageMultiplicity ≤
      propertyReadyRowFreshLoss
          D C q cell hcell selectedCells hmass hactive S *
        frostmanMultiplicityRHS (b / 8)
          (PropertyReadySelectedRowDatum
            D C q cell hcell selectedCells hmass hactive S selected).actualFamilyVolume
          epsilon beta
  row_mass_identity :
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S).shading.shadingMass =
      ∑ s : ActiveSelectedOwnerRow
          D C q cell hcell selectedCells hmass hactive theta S,
        ownerFiberMass C s.1.1
  occurrence_card_identity :
    Fintype.card (PropertyReadyRowOccurrence
      D C q cell hcell selectedCells hmass hactive S) =
      ∑ s : ActiveSelectedOwnerRow
          D C q cell hcell selectedCells hmass hactive theta S,
        (ownerFiber C s.1.1).card
  row_mass_floor :
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive theta S).card : ENNReal) *
        retainedOwnerHalfAverageFloor C q ≤
      (PropertyReadyRowDatum
        D C q cell hcell selectedCells hmass hactive S).shading.shadingMass
  occurrence_card_bounds :
    (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive theta S).card *
          ownerBucketBranching q ≤
        Fintype.card (PropertyReadyRowOccurrence
          D C q cell hcell selectedCells hmass hactive S) ∧
    Fintype.card (PropertyReadyRowOccurrence
        D C q cell hcell selectedCells hmass hactive S) ≤
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive theta S).card *
          (2 * ownerBucketBranching q)
  occurrence_nonempty : Nonempty (PropertyReadyRowOccurrence
    D C q cell hcell selectedCells hmass hactive S)
  inherited_thick_control : FrostmanThickenedPlankControl
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S) M
  branching_le_M_mul_theta :
    (ownerBucketBranching q : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal)
  canonical_frostman : IsFrostmanIn
    (propertyReadyRowCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive S)
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S).family
    (PropertyReadyRowDatum
      D C q cell hcell selectedCells hmass hactive S).ambient
  canonical_frostman_finite :
    propertyReadyRowCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive S ≠ ∞
  crossRowAggregation : CrossRowAggregationObligation
    D C q cell hcell selectedCells hmass hactive S epsilon beta M
      correlationLoss selected

/-- Positive producer for the same-object certificate.  The fresh object and
all card/mass/KT/M/N/canonical fields are obtained by calling existing
theorems.  `hCross` is intentionally the only universally selected analytic
aggregation input; its codomain is the named exact `M ^ (beta / 2)`
obligation above. -/
theorem exists_propertyReadyRowProp66Eq66Composer
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (S : ConvexBody Space)
    (hrow : (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selectedCells hmass hactive theta S).Nonempty)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hdelta0 : b / 8 ≤ delta0)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M)
    (hratio : a / b ≤ theta) (htheta : theta ≤ 1)
    (actualThirdAverage correlationLoss : ENNReal)
    (hActual : ActualThirdAverageCorrelationObligation
      D C q cell hcell selectedCells hmass hactive S
        actualThirdAverage correlationLoss)
    (hDensity : DensityPowerBudgetObligation
      D C q cell hcell selectedCells hmass hactive S eta)
    (hBase : BaseBudgetObligation
      D C q cell hcell selectedCells hmass hactive S eta)
    (hCross : ∀ selected : Finset (Unit × PropertyReadyRowOccurrence
        D C q cell hcell selectedCells hmass hactive S),
      CrossRowAggregationObligation
        D C q cell hcell selectedCells hmass hactive S epsilon beta M
          correlationLoss selected) :
    Nonempty (PropertyReadyRowProp66Eq66Composer
      D C q cell hcell selectedCells hmass hactive S
        epsilon beta eta M actualThirdAverage correlationLoss) := by
  let P := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selectedCells hmass hactive theta S
  let occurrence := ActiveSelectedOwnerRowOccurrence
    D C q cell hcell selectedCells hmass hactive theta S
  let source := centeredPlankLongTubeActualDatum P
  let canonicalC := canonicalFrostmanConstant P.family P.ambient
  let sourceC := plankLongTubeGlobalKatzTaoConstant P canonicalC
  let threshold := Nat.ceil ((480000 * (128 * sourceC) : ENNReal).toReal)
  let freshLoss : ENNReal := ((threshold + 1 : Nat) : ENNReal)
  obtain ⟨selected, hselected, hadmissible, hcard, hmassRetained,
      hselectedKT, hrowAverage⟩ :=
    exists_activeSelectedOwnerRow_fresh_admissible
      D C q cell hcell selectedCells hmass hactive theta S hrow hbHalf
  have hloss0 : freshLoss ≠ 0 := by
    simp [freshLoss]
  have hlossTop : freshLoss ≠ ∞ := by
    simp [freshLoss]
  have hsourceFrostman : source.shading.averageMultiplicity ≤
      freshLoss * frostmanMultiplicityRHS (b / 8)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) selected).actualFamilyVolume
        epsilon beta := by
    apply source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS
      hF source selected freshLoss (128 * sourceC)
      hloss0 hlossTop hdelta0 hadmissible
    · simpa only [freshLoss, threshold] using hcard
    · simpa only [freshLoss, source, threshold] using hmassRetained
    · exact hselectedKT
    · simpa only [DensityPowerBudgetObligation,
        propertyReadyRowFreshLoss, propertyReadyRowFreshThreshold,
        propertyReadyRowSourceKatzTaoConstant,
        propertyReadyRowCanonicalFrostmanConstant,
        PropertyReadyRowSource, PropertyReadyRowDatum,
        freshLoss, threshold, sourceC, canonicalC, source, P] using hDensity
    · simpa only [BaseBudgetObligation,
        propertyReadyRowFreshLoss, propertyReadyRowFreshThreshold,
        propertyReadyRowSourceKatzTaoConstant,
        propertyReadyRowCanonicalFrostmanConstant,
        PropertyReadyRowOccurrence, PropertyReadyRowDatum,
        freshLoss, threshold, sourceC, canonicalC, P] using hBase
  have hrowFrostman : P.shading.averageMultiplicity ≤
      freshLoss * frostmanMultiplicityRHS (b / 8)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) selected).actualFamilyVolume
        epsilon beta :=
    (source_averageMultiplicity_le_centeredPlankLongTubeActualDatum P).trans
      hsourceFrostman
  refine ⟨{
    hrow := hrow
    actualThirdAverage_correlation := hActual
    densityPowerBudget := hDensity
    baseBudget := hBase
    selected := selected
    selected_nonempty := hselected
    selected_admissible := hadmissible
    fresh_card_retained := ?_
    fresh_mass_retained := ?_
    selected_katzTao := ?_
    row_average_fresh_retained := ?_
    row_average_le_frostman := ?_
    row_mass_identity := activeSelectedOwnerRowPlankDatum_shadingMass
      D C q cell hcell selectedCells hmass hactive theta S
    occurrence_card_identity := activeSelectedOwnerRowOccurrence_card
      D C q cell hcell selectedCells hmass hactive theta S
    row_mass_floor := activeSelectedOwnerRow_card_mul_floor_le_shadingMass
      D C q cell hcell selectedCells hmass hactive theta S
    occurrence_card_bounds := activeSelectedOwnerRowOccurrence_card_bounds
      D C q cell hcell selectedCells hmass hactive theta S
    occurrence_nonempty := activeSelectedOwnerRowOccurrence_nonempty
      D C q cell hcell selectedCells hmass hactive theta S hrow
    inherited_thick_control :=
      activeSelectedOwnerRowPlankDatum_frostmanThickenedPlankControl
        D C q cell hcell selectedCells hmass hactive theta S M hthick
    branching_le_M_mul_theta :=
      activeSelectedOwnerRow_branching_le_M_mul_theta
        D C q cell hcell selectedCells hmass hactive S hrow M hthick
          hratio htheta
    canonical_frostman := activeSelectedOwnerRowPlankDatum_isFrostmanIn_canonical
      D C q cell hcell selectedCells hmass hactive theta S hrow
    canonical_frostman_finite :=
      activeSelectedOwnerRowPlankDatum_canonicalFrostmanConstant_ne_top
        D C q cell hcell selectedCells hmass hactive theta S hrow
    crossRowAggregation := hCross selected }⟩
  · simpa only [propertyReadyRowFreshLoss,
      propertyReadyRowFreshThreshold, propertyReadyRowSourceKatzTaoConstant,
      propertyReadyRowCanonicalFrostmanConstant,
      PropertyReadyRowOccurrence, PropertyReadyRowDatum,
      freshLoss, threshold, sourceC, canonicalC, P, occurrence] using hcard
  · simpa only [propertyReadyRowFreshLoss,
      propertyReadyRowFreshThreshold, propertyReadyRowSourceKatzTaoConstant,
      propertyReadyRowCanonicalFrostmanConstant,
      PropertyReadyRowSource, PropertyReadyRowDatum,
      freshLoss, threshold, sourceC, canonicalC, source, P] using hmassRetained
  · simpa only [propertyReadyRowSourceKatzTaoConstant,
      propertyReadyRowCanonicalFrostmanConstant,
      PropertyReadySelectedRowDatum, PropertyReadyRowSource,
      PropertyReadyRowDatum, sourceC, canonicalC, source, P] using hselectedKT
  · simpa only [propertyReadyRowFreshLoss,
      propertyReadyRowFreshThreshold, propertyReadyRowSourceKatzTaoConstant,
      propertyReadyRowCanonicalFrostmanConstant,
      PropertyReadySelectedRowDatum, PropertyReadyRowSource,
      PropertyReadyRowDatum, freshLoss, threshold, sourceC, canonicalC,
      source, P] using hrowAverage
  · simpa only [propertyReadyRowFreshLoss,
      propertyReadyRowFreshThreshold, propertyReadyRowSourceKatzTaoConstant,
      propertyReadyRowCanonicalFrostmanConstant,
      PropertyReadySelectedRowDatum, PropertyReadyRowSource,
      PropertyReadyRowDatum, freshLoss, threshold, sourceC, canonicalC,
      source, P] using hrowFrostman

namespace PropertyReadyRowProp66Eq66Composer

/-- Conditional Prop. 6.6 scalar endpoint.  The proof visibly factors
through the same selected row and then invokes the named aggregation field. -/
theorem actualThirdAverage_le_prop66Factor
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {cellIndex : Type v} {cell : cellIndex → Set Space}
    {hcell : ∀ p, MeasurableSet (cell p)} {selectedCells : Finset cellIndex}
    {hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0}
    {hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty}
    {S : ConvexBody Space} {epsilon beta eta : Real} {M : NNReal}
    {actualThirdAverage correlationLoss : ENNReal}
    (Z : PropertyReadyRowProp66Eq66Composer
      D C q cell hcell selectedCells hmass hactive S
        epsilon beta eta M actualThirdAverage correlationLoss) :
    actualThirdAverage ≤ propertyReadyRowProp66Factor
      D C q cell hcell selectedCells hmass hactive S epsilon beta M := by
  calc
    actualThirdAverage ≤ correlationLoss *
        (PropertyReadyRowDatum
          D C q cell hcell selectedCells hmass hactive S).shading.averageMultiplicity := by
      simpa only [ActualThirdAverageCorrelationObligation] using
        Z.actualThirdAverage_correlation
    _ ≤ correlationLoss *
        (propertyReadyRowFreshLoss
            D C q cell hcell selectedCells hmass hactive S *
          frostmanMultiplicityRHS (b / 8)
            (PropertyReadySelectedRowDatum
              D C q cell hcell selectedCells hmass hactive S
                Z.selected).actualFamilyVolume epsilon beta) := by
      gcongr
      exact Z.row_average_le_frostman
    _ ≤ propertyReadyRowProp66Factor
        D C q cell hcell selectedCells hmass hactive S epsilon beta M := by
      simpa only [CrossRowAggregationObligation] using Z.crossRowAggregation

end PropertyReadyRowProp66Eq66Composer

#print axioms PropertyReadyRowProp66Eq66Composer
#print axioms exists_propertyReadyRowProp66Eq66Composer
#print axioms PropertyReadyRowProp66Eq66Composer.actualThirdAverage_le_prop66Factor

end
end Family8PlankHeavyActiveSelectedOwnerProp66Eq66ComposerV1
