import Family8Grounding.Family8PaperEq45SelectedOccurrenceBundleV2
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Family8Grounding.Family8UniqueOwnerLocalDeltaMaxThickControlV1
import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1

/-!
# Paper-facing selected-occurrence inputs for Equation (45), honest thick M

This is the comparison-constant-honest successor to Bundle V2.  It does not
store a `FrostmanThickenedPlankControl ... (b/a)` conclusion.  Instead it
stores the mathematical data used by the paper's count:

* an owner of every selected plank;
* the unique-owner property for admissible closed thickenings;
* a numerical `Delta`;
* a bound of the actual owner-fibre `maximalConcentration` by `Delta`.

The derived stable Family 6 count uses

`thickM = max 1 (27 * comparisonConstant^3 * Delta * (b/a))`.

No unrealistic normalization `27 * C^3 * Delta <= 1` is required.  The fixed
comparison loss remains visible in `family6Factor` and is paid only by the
final scalar `ScaleAbsorption`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45SelectedOccurrenceBundleV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8PaperEq45SelectedOccurrenceBundleV2
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Paper-side structural inputs for the actual selected family `W'`, with
the thick-plank hypothesis replaced by its genuine owner/local-concentration
data. -/
structure PaperEq45SelectedOccurrenceInputV3
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (a b : NNReal) (ownerIndex : Type u) [DecidableEq ownerIndex] where
  comparisonConstant : NNReal
  all_isPlank : ∀ q,
    IsPlank comparisonConstant a b (selectedOccurrenceOuterFamily P S q)
  ambient : ConvexBody Space
  ambientComparisonConstant : NNReal
  ambient_is_unit_scale :
    IsPlank ambientComparisonConstant 1 1 ambient
  contained_in_ambient : ∀ q,
    (selectedOccurrenceOuterFamily P S q : Set Space) ⊆
      (ambient : Set Space)
  fiberCard_dyadicUniform : ∀ k ∈ S, ∀ l ∈ S,
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal)
  sourceCF : ENNReal
  lowerDensity : ENNReal
  upperDensity : ENNReal
  lowerDensity_ne_zero : lowerDensity ≠ 0
  lowerDensity_ne_top : lowerDensity ≠ ∞
  source_fine_frostman :
    IsFrostmanOn sourceCF F (selectedOccurrenceFineIndices P S) ambient
  blockMass_lower : ∀ k ∈ S,
    lowerDensity * volume ((blockAt F P k).body : Set Space) ≤
      blockMass F (blockAt F P k)
  blockMass_upper : ∀ k ∈ S,
    blockMass F (blockAt F P k) ≤
      upperDensity * volume ((blockAt F P k).body : Set Space)
  /-- The actual paper parent of each retained plank. -/
  owner : {q // q ∈ selectedOccurrenceIndices P S} -> ownerIndex
  /-- Any retained plank captured by an admissible thickening has the same
  paper parent as its centre. -/
  uniqueOwner : ThickenedPlankUniqueOwner
    (selectedOccurrenceOuterPlankDatum P Y S a b comparisonConstant
      all_isPlank ambient ambientComparisonConstant ambient_is_unit_scale
      contained_in_ambient) owner
  /-- Numerical upper envelope for the actual local owner-fibre
  concentration. -/
  Delta : NNReal
  /-- The stored premise is about the genuine `maximalConcentration` of the
  owner-fibre subfamilies, not a renamed thick-count conclusion. -/
  ownerFiberDeltaMax_le : ownerFiberDeltaMax
    (selectedOccurrenceOuterPlankDatum P Y S a b comparisonConstant
      all_isPlank ambient ambientComparisonConstant ambient_is_unit_scale
      contained_in_ambient) owner ≤ (Delta : ENNReal)

namespace PaperEq45SelectedOccurrenceInputV3

variable {P : GreedyDensityPartition F candidates container active}
  {Y : Shading F} {S : Finset (Fin (blocks F P).length)}
  {a b : NNReal} {ownerIndex : Type u} [DecidableEq ownerIndex]
  {beta : Real}

/-- The exact selected shaded plank datum. -/
abbrev datum (I : PaperEq45SelectedOccurrenceInputV3
    P Y S a b ownerIndex) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P S} a b :=
  selectedOccurrenceOuterPlankDatum P Y S a b I.comparisonConstant
    I.all_isPlank I.ambient I.ambientComparisonConstant
    I.ambient_is_unit_scale I.contained_in_ambient

/-- Remark 3.3(A)'s inherited Frostman constant. -/
def inheritedCF (I : PaperEq45SelectedOccurrenceInputV3
    P Y S a b ownerIndex) : ENNReal :=
  I.sourceCF * I.upperDensity * I.lowerDensity⁻¹

/-- The actual cardinality of the selected occurrence index type. -/
def plankCount (_I : PaperEq45SelectedOccurrenceInputV3
    P Y S a b ownerIndex) : Nat :=
  selectedOccurrenceOuterCount P S

/-- Honest thick-plank parameter derived from the comparison constant, local
`Delta`, and aspect ratio. -/
def thickM (I : PaperEq45SelectedOccurrenceInputV3
    P Y S a b ownerIndex) : NNReal :=
  uniqueOwnerLocalDeltaThickM I.comparisonConstant I.Delta a b

/-- Equation (45)'s displayed target, tied to the actual selected card and
the inherited CF source. -/
def rhs (I : PaperEq45SelectedOccurrenceInputV3
    P Y S a b ownerIndex)
    (delta : NNReal) (epsilon beta : Real) : ENNReal :=
  proposition66AOuterFactor delta a b I.plankCount I.inheritedCF
    epsilon beta

/-- Direct stable Family 6 factor with the honest `thickM`; the fixed
comparison loss is not erased. -/
def family6Factor (I : PaperEq45SelectedOccurrenceInputV3
    P Y S a b ownerIndex)
    (epsilon beta : Real) : ENNReal :=
  convexPlankFrostmanFactor I.datum epsilon beta I.inheritedCF I.thickM

/-- Scalar-only final absorption, including the fixed comparison loss inside
`thickM`. -/
def ScaleAbsorption (I : PaperEq45SelectedOccurrenceInputV3
    P Y S a b ownerIndex)
    (delta : NNReal) (lemmaEpsilon epsilon beta : Real) : Prop :=
  I.family6Factor lemmaEpsilon beta ≤ I.rhs delta epsilon beta

@[simp] theorem datum_family
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex) :
    I.datum.family = selectedOccurrenceOuterFamily P S :=
  rfl

@[simp] theorem datum_shading
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex) :
    I.datum.shading = selectedOccurrenceOuterShading P Y S :=
  rfl

theorem plankCount_eq_index_card
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex) :
    I.plankCount = Fintype.card {q // q ∈ selectedOccurrenceIndices P S} :=
  rfl

@[simp] theorem plankCount_eq_selected_card
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex) :
    I.plankCount = S.card :=
  selectedOccurrenceOuterCount_eq_card P S

theorem fiberCard_dyadicUniform_on_selected
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex)
    (k : Fin (blocks F P).length) (hk : k ∈ S)
    (l : Fin (blocks F P).length) (hl : l ∈ S) :
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal) :=
  I.fiberCard_dyadicUniform k hk l hl

/-- Remark 3.3(A) on the exact selected datum. -/
theorem isFrostmanIn_inheritedCF
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex) :
    IsFrostmanIn I.inheritedCF I.datum.family I.datum.ambient := by
  apply selectedOccurrenceOuterFamily_isFrostmanIn_of_comparable_blockMass
    P S I.ambient I.lowerDensity_ne_zero I.lowerDensity_ne_top
      I.source_fine_frostman
  · intro k hk
    exact I.contained_in_ambient (selectedOccurrenceIndexOf P S k hk)
  · exact I.blockMass_lower
  · exact I.blockMass_upper

/-- The Family 6 thick-plank certificate is derived from actual owner/local
`Delta_max` data with honest `thickM`. -/
theorem frostmanThickenedPlankControl_thickM
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex) :
    FrostmanThickenedPlankControl I.datum I.thickM := by
  exact frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax
    I.datum I.owner I.uniqueOwner I.ownerFiberDeltaMax_le

/-- Stable Family 6 consumer on the honest thick parameter. -/
theorem exists_family6Parameters_selectedAverage_le
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P S} beta)
    (lemmaEpsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b -> b ≤ b0 ->
        (a : ENNReal) ^ eta ≤ I.datum.shading.shadingDensity ->
        I.datum.shading.averageMultiplicity ≤
          I.family6Factor lemmaEpsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    H.bound lemmaEpsilon hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro ha hab hbb0 hdensity
  exact hbound {q // q ∈ selectedOccurrenceIndices P S}
    a b I.datum I.inheritedCF I.thickM ha hab hbb0
      I.isFrostmanIn_inheritedCF hdensity
      I.frostmanThickenedPlankControl_thickM

/-- Eq. (45) consumer.  All fixed geometric losses are retained in the
scalar absorption rather than normalized inside the thick-count theorem. -/
theorem exists_family6Parameters_selectedAverage_le_eq45
    (I : PaperEq45SelectedOccurrenceInputV3 P Y S a b ownerIndex)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P S} beta)
    (delta : NNReal) (lemmaEpsilon epsilon : Real)
    (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : I.ScaleAbsorption delta lemmaEpsilon epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b -> b ≤ b0 ->
        (a : ENNReal) ^ eta ≤ I.datum.shading.shadingDensity ->
        I.datum.shading.averageMultiplicity ≤
          I.rhs delta epsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    I.exists_family6Parameters_selectedAverage_le H lemmaEpsilon
      hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro ha hab hbb0 hdensity
  exact (hbound ha hab hbb0 hdensity).trans habsorb

#print axioms plankCount_eq_index_card
#print axioms plankCount_eq_selected_card
#print axioms isFrostmanIn_inheritedCF
#print axioms frostmanThickenedPlankControl_thickM
#print axioms exists_family6Parameters_selectedAverage_le
#print axioms exists_family6Parameters_selectedAverage_le_eq45

end PaperEq45SelectedOccurrenceInputV3

end

end Family8PaperEq45SelectedOccurrenceBundleV3
