import Family8Grounding.Family8SelectedOccurrenceMaxOwnerAverageRetentionV3
import Family8Grounding.Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# Generalized Equation (45) bundle for genuine max-owner occurrence hulls

The datum is the actual parent-specific max-owner hull family.  Unique owner
and local owner-fibre `Delta_max` are theorems from actual parent geometry,
ambient Frostman data, and actual ambient density.  The source-average bridge
pays exactly `fibreCardCap * conflictLoss`.

Common plank dimensions and refined ambient Frostman data remain explicit
structural inputs: a convex subhull does not inherit the larger winning
hull's `a x b x 1` certificate automatically.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxOwnerRefinedBundleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerAverageRetentionV3
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho a b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- Stable Family 6 datum on the actual max-owner refinement. -/
def selectedOccurrenceMaxOwnerHullPlankDatum
    (Y : Shading fine.bodyFamily)
    (S : Finset (Fin (blocks fine.bodyFamily P).length))
    (comparisonConstant : NNReal)
    (all_isPlank : ∀ q, IsPlank comparisonConstant a b
      (selectedOccurrenceMaxOwnerHullFamily C P Y S q))
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1 ambient)
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceMaxOwnerHullFamily C P Y S q : Set Space) ⊆
        (ambient : Set Space)) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P S} a b where
  family := selectedOccurrenceMaxOwnerHullFamily C P Y S
  shading := selectedOccurrenceMaxOwnerHullShading C P Y S
  comparisonConstant := comparisonConstant
  all_isPlank := all_isPlank
  ambient := ambient
  ambientComparisonConstant := ambientComparisonConstant
  ambient_is_unit_scale := ambient_is_unit_scale
  contained_in_ambient := contained_in_ambient

/-- Paper-facing max-owner refined data, with no owner conclusion callback. -/
structure PaperEq45MaxOwnerRefinedInput
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (a b : NNReal) where
  rho_pos : 0 < rho
  b_le_rho : b ≤ rho
  fibreCardCap : Nat
  fibreCard_le : ∀ k ∈ R0,
    (blockAt fine.bodyFamily P k).fiber.card ≤ fibreCardCap
  comparisonConstant : NNReal
  all_isPlank : ∀ q, IsPlank comparisonConstant a b
    (selectedOccurrenceMaxOwnerHullFamily C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected) q)
  ambient : ConvexBody Space
  ambientComparisonConstant : NNReal
  ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1 ambient
  contained_in_ambient : ∀ q,
    (selectedOccurrenceMaxOwnerHullFamily C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected) q : Set Space) ⊆
      (ambient : Set Space)
  frostmanConstant : ENNReal
  refined_frostman : IsFrostmanIn frostmanConstant
    (selectedOccurrenceMaxOwnerHullFamily C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected)) ambient
  ambientDensity : ENNReal
  ambient_mass_upper :
    containedMass
      (selectedOccurrenceMaxOwnerHullFamily C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) ambient ≤
      ambientDensity * volume (ambient : Set Space)
  Delta : NNReal
  Delta_dominates : frostmanConstant * ambientDensity ≤ (Delta : ENNReal)

namespace PaperEq45MaxOwnerRefinedInput

variable {Y : Shading fine.bodyFamily}
  {R0 : Finset (Fin (blocks fine.bodyFamily P).length)}
  {loss : ENNReal}
  {W : DoubledParentConflictWeightedSelection C
    (occurrenceMaxOwnerMass C P Y R0) loss}

abbrev selected
    (_I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :=
  occurrencesMaxOwnedBy C P Y R0 W.selected

abbrev datum (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P (selected C I)} a b :=
  selectedOccurrenceMaxOwnerHullPlankDatum C Y (selected C I)
    I.comparisonConstant I.all_isPlank I.ambient
    I.ambientComparisonConstant I.ambient_is_unit_scale I.contained_in_ambient

abbrev owner (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :=
  selectedOccurrenceMaxOwner C P Y (selected C I)

def thickM (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) : NNReal :=
  uniqueOwnerLocalDeltaThickM I.comparisonConstant I.Delta a b

def plankCount
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) : Nat :=
  Fintype.card {q // q ∈ selectedOccurrenceIndices P (selected C I)}

def rhs (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b)
    (delta0 : NNReal) (epsilon beta : Real) : ENNReal :=
  proposition66AOuterFactor delta0 a b (plankCount C I)
    I.frostmanConstant epsilon beta

def family6Factor (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b)
    (epsilon beta : Real) : ENNReal :=
  convexPlankFrostmanFactor (datum C I) epsilon beta I.frostmanConstant
    (thickM C I)

def ScaleAbsorption
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b)
    (delta0 : NNReal) (lemmaEpsilon epsilon beta : Real) : Prop :=
  family6Factor C I lemmaEpsilon beta ≤ rhs C I delta0 epsilon beta

@[simp] theorem datum_family
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    (datum C I).family = selectedOccurrenceMaxOwnerHullFamily C P Y
      (selected C I) := rfl

@[simp] theorem datum_shading
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    (datum C I).shading = selectedOccurrenceMaxOwnerHullShading C P Y
      (selected C I) := rfl

theorem plankCount_eq_selected_card
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    plankCount C I = (selected C I).card := by
  exact selectedOccurrenceOuterCount_eq_card P (selected C I)

/-- Actual parent geometry and selected conflict-freeness produce unique
ownership on this exact datum. -/
theorem uniqueOwner
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    ThickenedPlankUniqueOwner (datum C I) (owner C I) := by
  exact thickenedPlankUniqueOwner_maxOwnerHull_ownedOccurrences C
    I.rho_pos I.b_le_rho Y R0 loss W (datum C I) rfl

/-- Ambient Frostman and actual ambient density produce the local owner-fibre
concentration bound. -/
theorem ownerFiberDeltaMax_le
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    ownerFiberDeltaMax (datum C I) (owner C I) ≤ (I.Delta : ENNReal) := by
  exact ownerFiberDeltaMax_le_of_ambientFrostman (datum C I) (owner C I)
    I.refined_frostman I.ambient_mass_upper I.Delta_dominates

theorem frostmanThickenedPlankControl_thickM
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    FrostmanThickenedPlankControl (datum C I) (thickM C I) := by
  exact frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax
    (datum C I) (owner C I) (uniqueOwner C I) (ownerFiberDeltaMax_le C I)

/-- Proven source-average loss into the same datum consumed by Family 6. -/
theorem sourceAverage_le_refined
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b) :
    (selectedOccurrenceOuterShading P Y R0).averageMultiplicity ≤
      ((I.fibreCardCap : ENNReal) * loss) *
        (datum C I).shading.averageMultiplicity := by
  exact
    selectedOccurrenceOuterShading_average_le_card_mul_conflict_mul_maxOwner
      C P Y R0 I.fibreCardCap I.fibreCard_le loss W

theorem exists_family6Parameters_refinedAverage_le
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b)
    {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P (selected C I)} beta)
    (lemmaEpsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b → b ≤ b0 →
        (a : ENNReal) ^ eta ≤ (datum C I).shading.shadingDensity →
        (datum C I).shading.averageMultiplicity ≤
          family6Factor C I lemmaEpsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    H.bound lemmaEpsilon hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro ha hab hbb0 hdensity
  exact hbound {q // q ∈ selectedOccurrenceIndices P (selected C I)}
    a b (datum C I) I.frostmanConstant (thickM C I) ha hab hbb0
      I.refined_frostman hdensity (frostmanThickenedPlankControl_thickM C I)

theorem exists_family6Parameters_refinedAverage_le_eq45
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b)
    {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P (selected C I)} beta)
    (delta0 : NNReal) (lemmaEpsilon epsilon : Real)
    (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : ScaleAbsorption C I delta0 lemmaEpsilon epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b → b ≤ b0 →
        (a : ENNReal) ^ eta ≤ (datum C I).shading.shadingDensity →
        (datum C I).shading.averageMultiplicity ≤
          rhs C I delta0 epsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    exists_family6Parameters_refinedAverage_le C I H lemmaEpsilon
      hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro ha hab hbb0 hdensity
  exact (hbound ha hab hbb0 hdensity).trans habsorb

/-- Combined source-average Equation (45) statement with the explicit
refinement/selection loss. -/
theorem exists_family6Parameters_sourceAverage_le_eq45
    (I : PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b)
    {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P (selected C I)} beta)
    (delta0 : NNReal) (lemmaEpsilon epsilon : Real)
    (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : ScaleAbsorption C I delta0 lemmaEpsilon epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b → b ≤ b0 →
        (a : ENNReal) ^ eta ≤ (datum C I).shading.shadingDensity →
        (selectedOccurrenceOuterShading P Y R0).averageMultiplicity ≤
          ((I.fibreCardCap : ENNReal) * loss) *
            rhs C I delta0 epsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hrefined⟩ :=
    exists_family6Parameters_refinedAverage_le_eq45 C I H delta0
      lemmaEpsilon epsilon hlemmaEpsilon habsorb
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro ha hab hbb0 hdensity
  exact (sourceAverage_le_refined C I).trans (by
    gcongr
    exact hrefined ha hab hbb0 hdensity)

#print axioms datum_family
#print axioms plankCount_eq_selected_card
#print axioms uniqueOwner
#print axioms ownerFiberDeltaMax_le
#print axioms frostmanThickenedPlankControl_thickM
#print axioms sourceAverage_le_refined
#print axioms exists_family6Parameters_sourceAverage_le_eq45

end PaperEq45MaxOwnerRefinedInput

end

end Family8PaperEq45MaxOwnerRefinedBundleV2
