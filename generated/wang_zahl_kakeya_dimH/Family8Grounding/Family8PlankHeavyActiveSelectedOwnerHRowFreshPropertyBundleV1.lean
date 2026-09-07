import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerHRowProducerV1
import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8CanonicalCertifiedPlankFineAngleRowsV1
open Family8PlankHeavyRetainedOwnerCellRestrictedCanonicalSlabV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerRepresentativeDatumV2
open Family8PlankHeavyActiveSelectedOwnerFlatPrismCountV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1
open Family8PlankHeavyActiveSelectedOwnerHRowProducerV1
open Family8PlankLongTubeGlobalKatzTaoV3
open Family8PlankLongTubeCenteredFreshV4

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# A tau-generalized selected-row fresh/Frostman property bundle

The certified-incidence producer first chooses one genuine `tau`, one slab,
and one nonempty selected-owner row.  The raw fresh theorem is then called
exactly once on that row.  Every retained card, mass, average, Katz--Tao, and
Frostman statement below refers to that same selected finset.
-/

abbrev HRowFreshOccurrence
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :=
  ActiveSelectedOwnerRowOccurrence
    D C q cell hcell selectedCells hmass hactive tau S

abbrev HRowFreshPlankDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :=
  activeSelectedOwnerRowPlankDatum
    D C q cell hcell selectedCells hmass hactive tau S

abbrev HRowFreshSource
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :=
  centeredPlankLongTubeActualDatum
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive tau S)

def hRowFreshCanonicalFrostmanConstant
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) : ENNReal :=
  let P := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive tau S
  canonicalFrostmanConstant P.family P.ambient

def hRowFreshSourceKatzTaoConstant
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) : ENNReal :=
  let P := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive tau S
  plankLongTubeGlobalKatzTaoConstant P
    (hRowFreshCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive tau S)

def hRowFreshThreshold
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) : Nat :=
  Nat.ceil ((480000 * (128 * hRowFreshSourceKatzTaoConstant
    D C q cell hcell selectedCells hmass hactive tau S) : ENNReal).toReal)

def hRowFreshLoss
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) : ENNReal :=
  ((hRowFreshThreshold
    D C q cell hcell selectedCells hmass hactive tau S + 1 : Nat) : ENNReal)

abbrev HRowFreshSelectedDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (freshSelected : Finset (Unit × HRowFreshOccurrence
      D C q cell hcell selectedCells hmass hactive tau S)) :=
  restrictActualTubeDatum
    (eighthNormalizedDatum (HRowFreshSource
      D C q cell hcell selectedCells hmass hactive tau S)) freshSelected

def HRowFreshDensityPowerBudget
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) (eta : Real) : Prop :=
  (((b / 8 : NNReal) : ENNReal) ^ eta) ≤
    (eighthNormalizedDatum (HRowFreshSource
      D C q cell hcell selectedCells hmass hactive tau S)).shading.shadingDensity /
      hRowFreshLoss
        D C q cell hcell selectedCells hmass hactive tau S

def HRowFreshBaseBudget
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) (eta : Real) : Prop :=
  hRowFreshLoss
      D C q cell hcell selectedCells hmass hactive tau S *
      ((128 * hRowFreshSourceKatzTaoConstant
          D C q cell hcell selectedCells hmass hactive tau S) *
        volume (unitBallBody : Set Space)) ≤
    ((b / 8 : NNReal) : ENNReal) ^ (-eta) *
      ((Fintype.card (Unit × HRowFreshOccurrence
        D C q cell hcell selectedCells hmass hactive tau S) : ENNReal) *
        (((b / 8 : NNReal) : ENNReal) ^ 2 / 2))

structure HRowFreshPropertyBundle
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (epsilon beta eta : Real) where
  tau : NNReal
  S : ConvexBody Space
  slab : IsSlab 1 tau S
  ratio_le_tau : a / b ≤ tau
  tau_le_one : tau ≤ 1
  hrow : (activeSelectedOwnersInCertifiedSlab
    D C q cell hcell selectedCells hmass hactive tau S).Nonempty
  row_angle_count :
    (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selectedCells hmass hactive tau S).card ≤
        canonicalCertifiedFineAngleOccupancy
          (heavyRetainedOwnerCellRestrictedCanonicalUnitSlabIncidence
            D C q cell hcell selectedCells hmass) 2 tau
  row_flatPrism_count :
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive tau S).card : ENNReal) *
        (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) ≤
      maximalConcentration D.family *
        (((tau : ENNReal) + 4 * ((theta : ENNReal) * (b : ENNReal))) *
          (((1 : ENNReal) + 4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2))
  row_owner_mass_floor :
    ∀ s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive tau S},
      retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s.1.1
  occurrence_nonempty : Nonempty (HRowFreshOccurrence
    D C q cell hcell selectedCells hmass hactive tau S)
  canonical_frostman : IsFrostmanIn
    (hRowFreshCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive tau S)
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive tau S).family
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive tau S).ambient
  canonical_frostman_finite :
    hRowFreshCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive tau S ≠ ∞
  densityPowerBudget : HRowFreshDensityPowerBudget
    D C q cell hcell selectedCells hmass hactive tau S eta
  baseBudget : HRowFreshBaseBudget
    D C q cell hcell selectedCells hmass hactive tau S eta
  freshSelected : Finset (Unit × HRowFreshOccurrence
    D C q cell hcell selectedCells hmass hactive tau S)
  freshSelected_nonempty : freshSelected.Nonempty
  freshSelected_admissible : (HRowFreshSelectedDatum
    D C q cell hcell selectedCells hmass hactive tau S
      freshSelected).IsAdmissible
  fresh_card_retained :
    (Fintype.card (Unit × HRowFreshOccurrence
      D C q cell hcell selectedCells hmass hactive tau S) : ENNReal) ≤
      hRowFreshLoss
        D C q cell hcell selectedCells hmass hactive tau S *
          (freshSelected.card : ENNReal)
  fresh_mass_retained :
    (eighthNormalizedDatum (HRowFreshSource
      D C q cell hcell selectedCells hmass hactive tau S)).shading.shadingMass ≤
      hRowFreshLoss
          D C q cell hcell selectedCells hmass hactive tau S *
        (HRowFreshSelectedDatum
          D C q cell hcell selectedCells hmass hactive tau S
            freshSelected).shading.shadingMass
  fresh_selected_katzTao : IsKatzTao
    (128 * hRowFreshSourceKatzTaoConstant
      D C q cell hcell selectedCells hmass hactive tau S)
    (HRowFreshSelectedDatum
      D C q cell hcell selectedCells hmass hactive tau S
        freshSelected).family.bodyFamily
  row_average_fresh_retained :
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive tau S).shading.averageMultiplicity ≤
      hRowFreshLoss
          D C q cell hcell selectedCells hmass hactive tau S *
        (HRowFreshSelectedDatum
          D C q cell hcell selectedCells hmass hactive tau S
            freshSelected).shading.averageMultiplicity
  source_average_le_frostman :
    (HRowFreshSource
      D C q cell hcell selectedCells hmass hactive tau S).shading.averageMultiplicity ≤
      hRowFreshLoss
          D C q cell hcell selectedCells hmass hactive tau S *
        frostmanMultiplicityRHS (b / 8)
          (HRowFreshSelectedDatum
            D C q cell hcell selectedCells hmass hactive tau S
              freshSelected).actualFamilyVolume epsilon beta
  row_average_le_frostman :
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive tau S).shading.averageMultiplicity ≤
      hRowFreshLoss
          D C q cell hcell selectedCells hmass hactive tau S *
        frostmanMultiplicityRHS (b / 8)
          (HRowFreshSelectedDatum
            D C q cell hcell selectedCells hmass hactive tau S
              freshSelected).actualFamilyVolume epsilon beta

theorem exists_hRowFreshPropertyBundle
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
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hdelta0 : b / 8 ≤ delta0)
    (hDensity : ∀ (tau : NNReal) (S : ConvexBody Space),
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive tau S).Nonempty →
      HRowFreshDensityPowerBudget
        D C q cell hcell selectedCells hmass hactive tau S eta)
    (hBase : ∀ (tau : NNReal) (S : ConvexBody Space),
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive tau S).Nonempty →
      HRowFreshBaseBudget
        D C q cell hcell selectedCells hmass hactive tau S eta) :
    Nonempty (HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) := by
  obtain ⟨tau, S, hS, hratio, htau, hrow, hangle, hflat, hfloor⟩ :=
    exists_activeSelectedOwnersInCertifiedSlab_propertyRow
      D C q cell hcell selectedCells hmass hactive
  let P := activeSelectedOwnerRowPlankDatum
    D C q cell hcell selectedCells hmass hactive tau S
  let occurrence := ActiveSelectedOwnerRowOccurrence
    D C q cell hcell selectedCells hmass hactive tau S
  let source := centeredPlankLongTubeActualDatum P
  let canonicalC := canonicalFrostmanConstant P.family P.ambient
  let sourceC := plankLongTubeGlobalKatzTaoConstant P canonicalC
  let threshold := Nat.ceil ((480000 * (128 * sourceC) : ENNReal).toReal)
  let freshLoss : ENNReal := ((threshold + 1 : Nat) : ENNReal)
  have hDensitySelected := hDensity tau S hrow
  have hBaseSelected := hBase tau S hrow
  obtain ⟨freshSelected, hselected, hadmissible, hcard, hmassRetained,
      hselectedKT, hrowAverage⟩ :=
    exists_activeSelectedOwnerRow_fresh_admissible
      D C q cell hcell selectedCells hmass hactive tau S hrow hbHalf
  have hloss0 : freshLoss ≠ 0 := by
    simp [freshLoss]
  have hlossTop : freshLoss ≠ ∞ := by
    simp [freshLoss]
  have hsourceFrostman : source.shading.averageMultiplicity ≤
      freshLoss * frostmanMultiplicityRHS (b / 8)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) freshSelected).actualFamilyVolume
        epsilon beta := by
    apply source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS
      hF source freshSelected freshLoss (128 * sourceC)
      hloss0 hlossTop hdelta0 hadmissible
    · simpa only [freshLoss, threshold] using hcard
    · simpa only [freshLoss, source, threshold] using hmassRetained
    · exact hselectedKT
    · simpa only [HRowFreshDensityPowerBudget, hRowFreshLoss,
        hRowFreshThreshold, hRowFreshSourceKatzTaoConstant,
        hRowFreshCanonicalFrostmanConstant, HRowFreshSource,
        HRowFreshPlankDatum, freshLoss, threshold, sourceC, canonicalC,
        source, P] using hDensitySelected
    · simpa only [HRowFreshBaseBudget, hRowFreshLoss,
        hRowFreshThreshold, hRowFreshSourceKatzTaoConstant,
        hRowFreshCanonicalFrostmanConstant, HRowFreshOccurrence,
        HRowFreshPlankDatum, freshLoss, threshold, sourceC, canonicalC,
        P] using hBaseSelected
  have hrowFrostman : P.shading.averageMultiplicity ≤
      freshLoss * frostmanMultiplicityRHS (b / 8)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) freshSelected).actualFamilyVolume
        epsilon beta :=
    (source_averageMultiplicity_le_centeredPlankLongTubeActualDatum P).trans
      hsourceFrostman
  refine ⟨{
    tau := tau
    S := S
    slab := hS
    ratio_le_tau := hratio
    tau_le_one := htau
    hrow := hrow
    row_angle_count := hangle
    row_flatPrism_count := hflat
    row_owner_mass_floor := hfloor
    occurrence_nonempty := activeSelectedOwnerRowOccurrence_nonempty
      D C q cell hcell selectedCells hmass hactive tau S hrow
    canonical_frostman := activeSelectedOwnerRowPlankDatum_isFrostmanIn_canonical
      D C q cell hcell selectedCells hmass hactive tau S hrow
    canonical_frostman_finite :=
      activeSelectedOwnerRowPlankDatum_canonicalFrostmanConstant_ne_top
        D C q cell hcell selectedCells hmass hactive tau S hrow
    densityPowerBudget := hDensitySelected
    baseBudget := hBaseSelected
    freshSelected := freshSelected
    freshSelected_nonempty := hselected
    freshSelected_admissible := hadmissible
    fresh_card_retained := ?_
    fresh_mass_retained := ?_
    fresh_selected_katzTao := ?_
    row_average_fresh_retained := ?_
    source_average_le_frostman := ?_
    row_average_le_frostman := ?_ }⟩
  · simpa only [hRowFreshLoss, hRowFreshThreshold,
      hRowFreshSourceKatzTaoConstant, hRowFreshCanonicalFrostmanConstant,
      HRowFreshOccurrence, HRowFreshPlankDatum, freshLoss, threshold,
      sourceC, canonicalC, P, occurrence] using hcard
  · simpa only [hRowFreshLoss, hRowFreshThreshold,
      hRowFreshSourceKatzTaoConstant, hRowFreshCanonicalFrostmanConstant,
      HRowFreshSource, HRowFreshPlankDatum, HRowFreshSelectedDatum,
      freshLoss, threshold, sourceC, canonicalC, source, P] using hmassRetained
  · simpa only [hRowFreshSourceKatzTaoConstant,
      hRowFreshCanonicalFrostmanConstant, HRowFreshSource,
      HRowFreshPlankDatum, HRowFreshSelectedDatum,
      sourceC, canonicalC, source, P] using hselectedKT
  · simpa only [hRowFreshLoss, hRowFreshThreshold,
      hRowFreshSourceKatzTaoConstant, hRowFreshCanonicalFrostmanConstant,
      HRowFreshSource, HRowFreshPlankDatum, HRowFreshSelectedDatum,
      freshLoss, threshold, sourceC, canonicalC, source, P] using hrowAverage
  · simpa only [hRowFreshLoss, hRowFreshThreshold,
      hRowFreshSourceKatzTaoConstant, hRowFreshCanonicalFrostmanConstant,
      HRowFreshSource, HRowFreshPlankDatum, HRowFreshSelectedDatum,
      freshLoss, threshold, sourceC, canonicalC, source, P] using hsourceFrostman
  · simpa only [hRowFreshLoss, hRowFreshThreshold,
      hRowFreshSourceKatzTaoConstant, hRowFreshCanonicalFrostmanConstant,
      HRowFreshSource, HRowFreshPlankDatum, HRowFreshSelectedDatum,
      freshLoss, threshold, sourceC, canonicalC, source, P] using hrowFrostman

#print axioms HRowFreshPropertyBundle
#print axioms exists_hRowFreshPropertyBundle

end
end Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
