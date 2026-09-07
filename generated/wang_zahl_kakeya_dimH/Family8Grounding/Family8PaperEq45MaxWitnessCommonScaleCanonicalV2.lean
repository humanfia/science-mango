import Family8Grounding.Family8SelectedOccurrenceMaxWitnessCommonScaleOwnerV4
import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# Canonical Equation (45) input on the actual common-scale max witnesses

This is the same-object successor to the max-owner-hull route.  The family
consumed by Family 6 is literally the common scalar image of the actual
maximal-shading witness tube in every retained occurrence.  On that one
object we have:

* the automatic common `IsPlank 2 w w` certificate;
* exact affine transport of the selected witness shading and Frostman data;
* actual-parent unique ownership and owner-fibre local Delta control;
* the source-average bridge with the explicit extra fibre-cardinality loss.

The numerical `Delta` is chosen canonically as the finite product of the
refined Frostman constant and the actual ambient family-volume density.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCommonScaleCanonicalV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6AffineConvexVolumeCoreV1
open Family8AmbientFamilyVolumeDensityV2
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleOwnerV4
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- The callback-free Frostman constant on the common-scale witness family. -/
def maxWitnessRefinedFrostmanConstant (CF : ENNReal) (M : Nat) : ENNReal :=
  CF * (16 * (M : ENNReal))

/-- Paper-facing data on the one actual common-scale witness object. -/
structure PaperEq45MaxWitnessCommonScaleInput
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss) where
  delta_pos : 0 < delta
  delta_le_half : delta ≤ (2 : NNReal)⁻¹
  two_delta_le_rho : 2 * delta ≤ rho
  fibreCardCap : Nat
  fibreCard_le : ∀ k ∈ R0,
    (blockAt fine.bodyFamily P k).fiber.card ≤ fibreCardCap
  sourceAmbient : ConvexBody Space
  ambientComparisonConstant : NNReal
  ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
    (affineImageConvexBody (maxWitnessCommonScaleEquiv delta) sourceAmbient)
  contained_in_sourceAmbient : ∀ q,
    (selectedOccurrenceMaxWitnessFamily C Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected) q : Set Space) ⊆
      (sourceAmbient : Set Space)
  frostmanConstant : ENNReal
  refined_frostman : IsFrostmanIn frostmanConstant
    (selectedOccurrenceMaxWitnessCommonScaleFamily C Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
    (affineImageConvexBody (maxWitnessCommonScaleEquiv delta) sourceAmbient)
  ambientDensity : ENNReal
  ambient_mass_upper : containedMass
    (selectedOccurrenceMaxWitnessCommonScaleFamily C Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
    (affineImageConvexBody (maxWitnessCommonScaleEquiv delta) sourceAmbient) ≤
      ambientDensity * volume
        (affineImageConvexBody (maxWitnessCommonScaleEquiv delta)
          sourceAmbient : Set Space)
  Delta : NNReal
  Delta_dominates : frostmanConstant * ambientDensity ≤ (Delta : ENNReal)

namespace PaperEq45MaxWitnessCommonScaleInput

variable {Y : Shading fine.bodyFamily}
  {R0 : Finset (Fin (blocks fine.bodyFamily P).length)}
  {loss : ENNReal}
  {W : DoubledParentConflictWeightedSelection C
    (occurrenceMaxOwnerMass C P Y R0) loss}

abbrev selected
    (_I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :=
  occurrencesMaxOwnedBy C P Y R0 W.selected

abbrev datum (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P (selected C I)}
      (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta) :=
  selectedOccurrenceMaxWitnessCommonScaleDatum C Y (selected C I)
    I.delta_pos I.delta_le_half I.sourceAmbient
    I.ambientComparisonConstant I.ambient_is_unit_scale
    I.contained_in_sourceAmbient

abbrev owner (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :=
  selectedOccurrenceMaxOwner C P Y (selected C I)

def thickM (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    NNReal :=
  uniqueOwnerLocalDeltaThickM 2 I.Delta
    (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta)

def plankCount
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) : Nat :=
  Fintype.card {q // q ∈ selectedOccurrenceIndices P (selected C I)}

def rhs (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W)
    (delta0 : NNReal) (epsilon beta : Real) : ENNReal :=
  proposition66AOuterFactor delta0 (maxWitnessCommonWidth delta)
    (maxWitnessCommonWidth delta) (plankCount C I) I.frostmanConstant
    epsilon beta

def family6Factor
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W)
    (epsilon beta : Real) : ENNReal :=
  convexPlankFrostmanFactor (datum C I) epsilon beta I.frostmanConstant
    (thickM C I)

def ScaleAbsorption
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W)
    (delta0 : NNReal) (lemmaEpsilon epsilon beta : Real) : Prop :=
  family6Factor C I lemmaEpsilon beta ≤ rhs C I delta0 epsilon beta

@[simp] theorem datum_family
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    (datum C I).family = selectedOccurrenceMaxWitnessCommonScaleFamily C Y
      (selected C I) := rfl

@[simp] theorem datum_shading
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    (datum C I).shading = selectedOccurrenceMaxWitnessCommonScaleShading C Y
      (selected C I) := rfl

theorem plankCount_eq_selected_card
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    plankCount C I = (selected C I).card := by
  exact selectedOccurrenceOuterCount_eq_card P (selected C I)

/-- Unique ownership is proved on the exact datum consumed below. -/
theorem uniqueOwner
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    ThickenedPlankUniqueOwner (datum C I) (owner C I) := by
  exact thickenedPlankUniqueOwner_maxWitnessCommonScale_ownedOccurrences C
    I.delta_pos I.two_delta_le_rho Y R0 loss W (datum C I) rfl

/-- The canonical ambient data controls the actual owner-fibre supremum. -/
theorem ownerFiberDeltaMax_le
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    ownerFiberDeltaMax (datum C I) (owner C I) ≤ (I.Delta : ENNReal) := by
  exact ownerFiberDeltaMax_le_of_ambientFrostman (datum C I) (owner C I)
      I.refined_frostman I.ambient_mass_upper I.Delta_dominates

theorem frostmanThickenedPlankControl_thickM
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    FrostmanThickenedPlankControl (datum C I) (thickM C I) := by
  exact frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax
    (datum C I) (owner C I) (uniqueOwner C I) (ownerFiberDeltaMax_le C I)

/-- Exact source-average bridge.  Compared with the max-owner hull adapter,
the literal one-witness refinement pays one additional `fibreCardCap`. -/
theorem sourceAverage_le_refined
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W) :
    (selectedOccurrenceOuterShading P Y R0).averageMultiplicity ≤
      (((I.fibreCardCap : ENNReal) * loss) *
        (I.fibreCardCap : ENNReal)) *
          (datum C I).shading.averageMultiplicity := by
  exact selectedOccurrenceOuter_average_le_card_conflict_card_mul_witness
    C Y R0 loss W I.fibreCardCap I.fibreCard_le

theorem exists_family6Parameters_refinedAverage_le
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W)
    {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P (selected C I)} beta)
    (lemmaEpsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hw : 0 < maxWitnessCommonWidth delta),
        maxWitnessCommonWidth delta ≤ b0 →
        (maxWitnessCommonWidth delta : ENNReal) ^ eta ≤
          (datum C I).shading.shadingDensity →
        (datum C I).shading.averageMultiplicity ≤
          family6Factor C I lemmaEpsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    H.bound lemmaEpsilon hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hw hwb0 hdensity
  exact hbound {q // q ∈ selectedOccurrenceIndices P (selected C I)}
    (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta) (datum C I)
    I.frostmanConstant (thickM C I) hw le_rfl hwb0 I.refined_frostman
      hdensity (frostmanThickenedPlankControl_thickM C I)

theorem exists_family6Parameters_sourceAverage_le_eq45
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W)
    {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P (selected C I)} beta)
    (delta0 : NNReal) (lemmaEpsilon epsilon : Real)
    (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : ScaleAbsorption C I delta0 lemmaEpsilon epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hw : 0 < maxWitnessCommonWidth delta),
        maxWitnessCommonWidth delta ≤ b0 →
        (maxWitnessCommonWidth delta : ENNReal) ^ eta ≤
          (datum C I).shading.shadingDensity →
        (selectedOccurrenceOuterShading P Y R0).averageMultiplicity ≤
          (((I.fibreCardCap : ENNReal) * loss) *
            (I.fibreCardCap : ENNReal)) *
              rhs C I delta0 epsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hrefined⟩ :=
    exists_family6Parameters_refinedAverage_le C I H lemmaEpsilon
      hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hw hwb0 hdensity
  exact (sourceAverage_le_refined C I).trans (by
    gcongr
    exact (hrefined hw hwb0 hdensity).trans habsorb)

end PaperEq45MaxWitnessCommonScaleInput

/-! ## Callback-free canonical input producer -/

/-- The canonical local concentration coefficient for any finite refined
family and positive ambient body. -/
def canonicalMaxWitnessDelta
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space) :
    NNReal :=
  (CF * ambientFamilyVolumeDensity F ambient).toNNReal

theorem maxWitnessRefinedFrostmanConstant_ne_top
    (CF : ENNReal) (M : Nat) (hCF : CF ≠ ∞) :
    maxWitnessRefinedFrostmanConstant CF M ≠ ∞ := by
  unfold maxWitnessRefinedFrostmanConstant
  exact ENNReal.mul_ne_top hCF (by finiteness)

theorem canonicalMaxWitnessDelta_coe
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞) (hambientVolume : volume (ambient : Set Space) ≠ 0) :
    (canonicalMaxWitnessDelta CF F ambient : ENNReal) =
      CF * ambientFamilyVolumeDensity F ambient := by
  unfold canonicalMaxWitnessDelta
  rw [ENNReal.coe_toNNReal]
  exact ENNReal.mul_ne_top hCF
    (ambientFamilyVolumeDensity_ne_top F ambient hambientVolume)

/-- Assemble all structural, Frostman, owner and canonical-Delta data on the
same actual common-scale witness family. -/
noncomputable def paperEq45MaxWitnessCommonScaleInput_of_sourceFine_canonicalDelta
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (M : Nat)
    (hcard : ∀ k ∈ R0, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (h2delta : 2 * delta ≤ rho)
    (sourceAmbient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody (maxWitnessCommonScaleEquiv delta) sourceAmbient))
    (contained_in_sourceAmbient : ∀ q,
      (selectedOccurrenceMaxWitnessFamily C Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected) q : Set Space) ⊆
        (sourceAmbient : Set Space))
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) sourceAmbient) :
    PaperEq45MaxWitnessCommonScaleInput C Y R0 loss W := by
  let R := occurrencesMaxOwnedBy C P Y R0 W.selected
  let F := selectedOccurrenceMaxWitnessCommonScaleFamily C Y R
  let ambient := affineImageConvexBody (maxWitnessCommonScaleEquiv delta)
    sourceAmbient
  let refinedCF := maxWitnessRefinedFrostmanConstant CF M
  let ambientDensity := ambientFamilyVolumeDensity F ambient
  let Delta := canonicalMaxWitnessDelta refinedCF F ambient
  have hcardR : ∀ k ∈ R,
      (blockAt fine.bodyFamily P k).fiber.card ≤ M := by
    intro k hk
    exact hcard k ((mem_occurrencesMaxOwnedBy C P Y R0 W.selected k).mp hk).1
  have hFrostman : IsFrostmanIn refinedCF F ambient := by
    exact selectedOccurrenceMaxWitnessCommonScale_isFrostmanIn C Y R M
      hcardR sourceAmbient source_frostman hdeltaHalf
  have hcontained : ∀ q, (F q : Set Space) ⊆ (ambient : Set Space) := by
    intro q
    exact Set.image_mono (contained_in_sourceAmbient q)
  have hambientVolume : volume (ambient : Set Space) ≠ 0 :=
    ne_of_gt ambient_is_unit_scale.volume_pos
  have hambientTop : volume (ambient : Set Space) ≠ ∞ :=
    ambient.isCompact.measure_lt_top.ne
  have hmass : containedMass F ambient =
      ambientDensity * volume (ambient : Set Space) := by
    exact containedMass_eq_ambientFamilyVolumeDensity_mul F ambient hcontained
      hambientVolume hambientTop
  have hrefinedTop : refinedCF ≠ ∞ :=
    maxWitnessRefinedFrostmanConstant_ne_top CF M hCF
  have hDelta : refinedCF * ambientDensity ≤ (Delta : ENNReal) := by
    rw [canonicalMaxWitnessDelta_coe refinedCF F ambient hrefinedTop
      hambientVolume]
  exact
    { delta_pos := hdelta
      delta_le_half := hdeltaHalf
      two_delta_le_rho := h2delta
      fibreCardCap := M
      fibreCard_le := hcard
      sourceAmbient := sourceAmbient
      ambientComparisonConstant := ambientComparisonConstant
      ambient_is_unit_scale := ambient_is_unit_scale
      contained_in_sourceAmbient := contained_in_sourceAmbient
      frostmanConstant := refinedCF
      refined_frostman := hFrostman
      ambientDensity := ambientDensity
      ambient_mass_upper := hmass.le
      Delta := Delta
      Delta_dominates := hDelta }

#print axioms PaperEq45MaxWitnessCommonScaleInput.datum_family
#print axioms PaperEq45MaxWitnessCommonScaleInput.uniqueOwner
#print axioms PaperEq45MaxWitnessCommonScaleInput.ownerFiberDeltaMax_le
#print axioms PaperEq45MaxWitnessCommonScaleInput.sourceAverage_le_refined
#print axioms PaperEq45MaxWitnessCommonScaleInput.exists_family6Parameters_sourceAverage_le_eq45
#print axioms canonicalMaxWitnessDelta_coe
#print axioms paperEq45MaxWitnessCommonScaleInput_of_sourceFine_canonicalDelta

end
end Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
