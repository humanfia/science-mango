import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1

/-!
# Paper-facing selected-occurrence inputs for Equation (45)

This is the honest selected-family replacement for the all-occurrence audit
bundle.  A literal `S` of greedy occurrence positions is the refined family
`W'`; its index type contains exactly `S.image some`, its plank count is
proved equal to `S.card`, and its Frostman certificate is *derived* from a
source fine-family Frostman theorem plus two-sided `blockMass` density bounds.

The three structural inputs in the proof of Proposition 6.6(A) remain
visible and separate:

* dyadic uniformity of selected fibre cardinalities;
* Remark 3.3(A) inheritance, now produced from source CF and density bounds;
* the thick-plank count with `M = b / a`.

The Family 6 consumer controls the selected shading itself.  Relating this
selected average multiplicity back to an endpoint that still uses every
greedy occurrence requires a separate selection/retention theorem and is not
asserted here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45SelectedOccurrenceBundleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8Prop66AOuterInnerProductAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Exact stable Family 6 datum on a selected literal occurrence family. -/
def selectedOccurrenceOuterPlankDatum
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (a b comparisonConstant : NNReal)
    (all_isPlank : ∀ q,
      IsPlank comparisonConstant a b (selectedOccurrenceOuterFamily P S q))
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale :
      IsPlank ambientComparisonConstant 1 1 ambient)
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceOuterFamily P S q : Set Space) ⊆
        (ambient : Set Space)) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P S} a b where
  family := selectedOccurrenceOuterFamily P S
  shading := selectedOccurrenceOuterShading P Y S
  comparisonConstant := comparisonConstant
  all_isPlank := all_isPlank
  ambient := ambient
  ambientComparisonConstant := ambientComparisonConstant
  ambient_is_unit_scale := ambient_is_unit_scale
  contained_in_ambient := contained_in_ambient

/-- Paper-side structural inputs for the actual selected `W'` in Eq. (45).
Unlike the earlier audit bundle, there is no `cf_inheritance` field: it is a
theorem derived below from `source_fine_frostman` and the two block-mass
bounds on the same selected occurrence set. -/
structure PaperEq45SelectedOccurrenceInput
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (a b : NNReal) where
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
  /-- The selected fibres occupy a single dyadic cardinality scale.  This is
  a structural paper input, not by itself a producer of coarse CF. -/
  fiberCard_dyadicUniform : ∀ k ∈ S, ∀ l ∈ S,
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal)
  /-- The real source constant `CF(T')`. -/
  sourceCF : ENNReal
  lowerDensity : ENNReal
  upperDensity : ENNReal
  lowerDensity_ne_zero : lowerDensity ≠ 0
  lowerDensity_ne_top : lowerDensity ≠ ∞
  /-- Source non-concentration on exactly the fine fibres underlying `W'`. -/
  source_fine_frostman :
    IsFrostmanOn sourceCF F (selectedOccurrenceFineIndices P S) ambient
  /-- Lower density on every retained occurrence. -/
  blockMass_lower : ∀ k ∈ S,
    lowerDensity * volume ((blockAt F P k).body : Set Space) ≤
      blockMass F (blockAt F P k)
  /-- Upper density on every retained occurrence. -/
  blockMass_upper : ∀ k ∈ S,
    blockMass F (blockAt F P k) ≤
      upperDensity * volume ((blockAt F P k).body : Set Space)
  /-- The exact thick-plank input in the paper, with `M = b / a`. -/
  thick_count :
    FrostmanThickenedPlankControl
      (selectedOccurrenceOuterPlankDatum P Y S a b comparisonConstant
        all_isPlank ambient ambientComparisonConstant
        ambient_is_unit_scale contained_in_ambient)
      (b / a)

namespace PaperEq45SelectedOccurrenceInput

variable {P : GreedyDensityPartition F candidates container active}
  {Y : Shading F} {S : Finset (Fin (blocks F P).length)}
  {a b : NNReal} {beta : Real}

/-- The exact selected shaded plank datum. -/
abbrev datum (I : PaperEq45SelectedOccurrenceInput P Y S a b) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P S} a b :=
  selectedOccurrenceOuterPlankDatum P Y S a b I.comparisonConstant
    I.all_isPlank I.ambient I.ambientComparisonConstant
    I.ambient_is_unit_scale I.contained_in_ambient

/-- The inherited Frostman constant delivered by Remark 3.3(A). -/
def inheritedCF (I : PaperEq45SelectedOccurrenceInput P Y S a b) : ENNReal :=
  I.sourceCF * I.upperDensity * I.lowerDensity⁻¹

/-- The actual cardinality of the selected occurrence index type. -/
def plankCount (_I : PaperEq45SelectedOccurrenceInput P Y S a b) : Nat :=
  selectedOccurrenceOuterCount P S

/-- Eq. (45)'s displayed right-hand side, tied to the actual selected card and
the derived inherited CF constant. -/
def rhs (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (delta : NNReal) (epsilon beta : Real) : ENNReal :=
  proposition66AOuterFactor delta a b I.plankCount I.inheritedCF
    epsilon beta

/-- Direct factor delivered by the stable Family 6 hypothesis. -/
def family6Factor (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (epsilon beta : Real) : ENNReal :=
  convexPlankFrostmanFactor I.datum epsilon beta I.inheritedCF (b / a)

/-- The scalar-only final scale absorption; it contains no multiplicity
conclusion and is not an `houter` callback. -/
def ScaleAbsorption (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (delta : NNReal) (lemmaEpsilon epsilon beta : Real) : Prop :=
  I.family6Factor lemmaEpsilon beta ≤ I.rhs delta epsilon beta

@[simp] theorem datum_family
    (I : PaperEq45SelectedOccurrenceInput P Y S a b) :
    I.datum.family = selectedOccurrenceOuterFamily P S :=
  rfl

@[simp] theorem datum_shading
    (I : PaperEq45SelectedOccurrenceInput P Y S a b) :
    I.datum.shading = selectedOccurrenceOuterShading P Y S :=
  rfl

/-- The RHS count is the index subtype cardinality. -/
theorem plankCount_eq_index_card
    (I : PaperEq45SelectedOccurrenceInput P Y S a b) :
    I.plankCount = Fintype.card {q // q ∈ selectedOccurrenceIndices P S} :=
  rfl

/-- More concretely, the RHS count is exactly the selected occurrence card. -/
@[simp] theorem plankCount_eq_selected_card
    (I : PaperEq45SelectedOccurrenceInput P Y S a b) :
    I.plankCount = S.card :=
  selectedOccurrenceOuterCount_eq_card P S

/-- The selected-fibre dyadic cardinality input remains available explicitly;
it is not consumed by the CF proof below. -/
theorem fiberCard_dyadicUniform_on_selected
    (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (k : Fin (blocks F P).length) (hk : k ∈ S)
    (l : Fin (blocks F P).length) (hl : l ∈ S) :
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal) :=
  I.fiberCard_dyadicUniform k hk l hl

/-- Remark 3.3(A) is now a theorem on the exact selected datum, not a stored
callback. -/
theorem isFrostmanIn_inheritedCF
    (I : PaperEq45SelectedOccurrenceInput P Y S a b) :
    IsFrostmanIn I.inheritedCF I.datum.family I.datum.ambient := by
  apply selectedOccurrenceOuterFamily_isFrostmanIn_of_comparable_blockMass
    P S I.ambient I.lowerDensity_ne_zero I.lowerDensity_ne_top
      I.source_fine_frostman
  · intro k hk
    exact I.contained_in_ambient (selectedOccurrenceIndexOf P S k hk)
  · exact I.blockMass_lower
  · exact I.blockMass_upper

/-- The thick-plank certificate is on the same selected datum and uses
exactly `M = b / a`. -/
theorem frostmanThickenedPlankControl_ratio
    (I : PaperEq45SelectedOccurrenceInput P Y S a b) :
    FrostmanThickenedPlankControl I.datum (b / a) :=
  I.thick_count

/-- Stable Family 6 consumer for the selected paper family `W'`. -/
theorem exists_family6Parameters_selectedAverage_le
    (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P S} beta)
    (lemmaEpsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b → b ≤ b0 →
        (a : ENNReal) ^ eta ≤ I.datum.shading.shadingDensity →
        I.datum.shading.averageMultiplicity ≤
          I.family6Factor lemmaEpsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    H.bound lemmaEpsilon hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro ha hab hbb0 hdensity
  exact hbound {q // q ∈ selectedOccurrenceIndices P S}
    a b I.datum I.inheritedCF (b / a) ha hab hbb0
      I.isFrostmanIn_inheritedCF hdensity
      I.frostmanThickenedPlankControl_ratio

/-- Eq. (45) consumer on the exact selected family.  Only the scalar scale
absorption remains after the three structural paper inputs and Family 6. -/
theorem exists_family6Parameters_selectedAverage_le_eq45
    (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P S} beta)
    (delta : NNReal) (lemmaEpsilon epsilon : Real)
    (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : I.ScaleAbsorption delta lemmaEpsilon epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b → b ≤ b0 →
        (a : ENNReal) ^ eta ≤ I.datum.shading.shadingDensity →
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
#print axioms fiberCard_dyadicUniform_on_selected
#print axioms isFrostmanIn_inheritedCF
#print axioms frostmanThickenedPlankControl_ratio
#print axioms exists_family6Parameters_selectedAverage_le
#print axioms exists_family6Parameters_selectedAverage_le_eq45

end PaperEq45SelectedOccurrenceInput

end

end Family8PaperEq45SelectedOccurrenceBundleV2
