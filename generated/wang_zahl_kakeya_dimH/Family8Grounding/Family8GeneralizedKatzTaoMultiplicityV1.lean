import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8GeneralizedKatzTaoMultiplicityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# The honest random-subfamily front end for generalized Katz--Tao

The proof of `genKKT` in the paper samples about
`#T / maximalConcentration(T)` tubes.  This file formalizes the part of that
argument which is already justified by the repository:

* the sampled family is a literal subtype of the original actual tube datum;
* admissibility is inherited without changing the tubes or their shadings;
* cardinality, shading mass, and the mass in every *fixed* convex test body
  have the exact first moments predicted by independent zero-colour sampling.

The fixed-test quantifier is intentional.  Passing from these first moments
to one outcome which controls all convex test bodies simultaneously needs a
uniform concentration/VC-type extraction theorem.  The finite canonical-hull
reduction has exponentially many tests, so an elementary union bound does not
give the polynomial loss required by `genKKT`.  No such simultaneous event is
recorded as a structure field here.
-/

/-- The paper's generalized Katz--Tao target, before any sampling loss is
absorbed by shrinking the terminal scale. -/
def generalizedKatzTaoMultiplicityRHS (delta : NNReal)
    (maxConcentration : ENNReal) (tubeCount : Nat)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) *
    maxConcentration ^ (1 - beta) *
      (tubeCount : ENNReal) ^ beta

/-- Restrict an actual tube datum to a genuine finite subtype.  The uniform
certificate on the subtype is the existing loss-one, scale-empty refinement;
no quantitative retention is hidden in this definition. -/
def restrictActualTubeDatum
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (selected : Finset ι) :
    ActualTubeDatum delta {i // i ∈ selected} where
  family := D.family.restrictTo selected
  shading :=
    { carrier := fun i => D.shading.carrier i.1
      measurable_carrier := fun i => D.shading.measurable_carrier i.1
      carrier_subset := fun i => by
        change D.shading.carrier i.1 ⊆
          (D.family.bodyFamily i.1 : Set Space)
        exact D.shading.carrier_subset i.1 }

@[simp]
theorem restrictActualTubeDatum_family_tubes
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (selected : Finset ι)
    (i : {i // i ∈ selected}) :
    (restrictActualTubeDatum D selected).family.tubes i =
      D.family.tubes i.1 :=
  rfl

@[simp]
theorem restrictActualTubeDatum_shading_carrier
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (selected : Finset ι)
    (i : {i // i ∈ selected}) :
    (restrictActualTubeDatum D selected).shading.carrier i =
      D.shading.carrier i.1 :=
  rfl

/-- Passing to a sampled subtype preserves every geometric admissibility
condition literally. -/
theorem ActualTubeDatum.IsAdmissible.restrictTo
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    {D : ActualTubeDatum delta ι} (hD : D.IsAdmissible)
    (selected : Finset ι) :
    (restrictActualTubeDatum D selected).IsAdmissible := by
  refine
    { delta_pos := hD.delta_pos
      delta_le_half := hD.delta_le_half
      contained_in_unit_ball := fun i => by
        simpa using hD.contained_in_unit_ball i.1
      pairwise_essentiallyDistinct := ?_ }
  intro i _hi j _hj hij
  apply hD.pairwise_essentiallyDistinct (Set.mem_univ i.1)
    (Set.mem_univ j.1)
  exact fun hij' => hij (Subtype.ext hij')

/-- The subtype shading mass is exactly the selected finite subsum. -/
theorem restrictActualTubeDatum_shadingMass
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (selected : Finset ι) :
    (restrictActualTubeDatum D selected).shading.shadingMass =
      ∑ i ∈ selected, volume (D.shading.carrier i) := by
  unfold Shading.shadingMass
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach selected fun i => volume (D.shading.carrier i)

/-- The sampled shaded union is a literal subset of the original shaded
union.  This is the denominator monotonicity used in the multiplicity
comparison step of the paper. -/
theorem restrictActualTubeDatum_shadedUnion_subset
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (selected : Finset ι) :
    (restrictActualTubeDatum D selected).shading.shadedUnion ⊆
      D.shading.shadedUnion := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i.1, hi⟩

/-- A real-valued finite weight of the selected zero-colour indices. -/
def zeroColorSampleRealWeight
    {α : Type} [Fintype α] [DecidableEq α]
    (k : Nat) [NeZero k] (weight : α → Real)
    (omega : α → Fin k) : Real :=
  ∑ a ∈ zeroColorSample k omega, weight a

/-- Selected weight is the sum of the coordinate indicators. -/
theorem zeroColorSampleRealWeight_eq_sum_indicator
    {α : Type} [Fintype α] [DecidableEq α]
    (k : Nat) [NeZero k] (weight : α → Real)
    (omega : α → Fin k) :
    zeroColorSampleRealWeight k weight omega =
      ∑ a : α, if omega a = 0 then weight a else 0 := by
  change (∑ a ∈ (Finset.univ.filter fun a => omega a = 0), weight a) = _
  rw [Finset.sum_filter]

/-- One coordinate contributes exactly `weight a / k` in expectation. -/
theorem expect_zeroColor_weightedIndicator
    {α : Type} [Fintype α] [DecidableEq α]
    (k : Nat) [NeZero k] (weight : α → Real) (a : α) :
    (𝔼 omega : α → Fin k,
        if omega a = 0 then weight a else 0) =
      weight a / (k : Real) := by
  classical
  calc
    (𝔼 omega : α → Fin k,
        if omega a = 0 then weight a else 0) =
        𝔼 omega : α → Fin k,
          weight a * (if omega a = 0 then (1 : Real) else 0) := by
            apply Finset.expect_congr rfl
            intro omega _homega
            split_ifs <;> ring
    _ = weight a *
        (𝔼 omega : α → Fin k,
          if omega a = 0 then (1 : Real) else 0) := by
          exact (Finset.mul_expect _ _ _).symm
    _ = weight a * (1 / (k : Real)) := by
          rw [expect_zeroColor_indicator]
    _ = weight a / (k : Real) := by simp [div_eq_mul_inv]

/-- Exact first moment of an arbitrary real weight under independent
zero-colour sampling. -/
theorem expect_zeroColorSample_realWeight
    {α : Type} [Fintype α] [DecidableEq α]
    (k : Nat) [NeZero k] (weight : α → Real) :
    (𝔼 omega : α → Fin k,
        zeroColorSampleRealWeight k weight omega) =
      (∑ a : α, weight a) / (k : Real) := by
  classical
  calc
    (𝔼 omega : α → Fin k,
        zeroColorSampleRealWeight k weight omega) =
        𝔼 omega : α → Fin k,
          ∑ a : α, if omega a = 0 then weight a else 0 := by
            apply Finset.expect_congr rfl
            intro omega _homega
            exact zeroColorSampleRealWeight_eq_sum_indicator k weight omega
    _ = ∑ a : α,
          𝔼 omega : α → Fin k,
            if omega a = 0 then weight a else 0 := by
          exact Finset.expect_sum_comm _ _ _
    _ = ∑ a : α, weight a / (k : Real) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact expect_zeroColor_weightedIndicator k weight a
    _ = (∑ a : α, weight a) / (k : Real) := by
          exact (Finset.sum_div _ _ _).symm

/-- In particular, one actual colouring retains at least the expected amount
of any real weight.  The witness is a colouring, not a postulated good
subfamily. -/
theorem exists_zeroColorSample_realWeight_ge_expect
    {α : Type} [Fintype α] [DecidableEq α]
    (k : Nat) [NeZero k] (weight : α → Real) :
    ∃ omega : α → Fin k,
      (∑ a : α, weight a) / (k : Real) ≤
        zeroColorSampleRealWeight k weight omega := by
  classical
  have hOmega : (Finset.univ : Finset (α → Fin k)).Nonempty :=
    ⟨fun _ => 0, Finset.mem_univ _⟩
  have hmean : (∑ a : α, weight a) / (k : Real) ≤
      𝔼 omega : α → Fin k,
        zeroColorSampleRealWeight k weight omega := by
    rw [expect_zeroColorSample_realWeight]
  obtain ⟨omega, _homega, homega⟩ :=
    Finset.exists_le_of_le_expect hOmega hmean
  exact ⟨omega, homega⟩

/-- The actual datum obtained from one literal zero-colour sample. -/
def zeroColorActualDatum
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (k : Nat) [NeZero k]
    (omega : ι → Fin k) :
    ActualTubeDatum delta {i // i ∈ zeroColorSample k omega} :=
  restrictActualTubeDatum D (zeroColorSample k omega)

/-- Exact expected sampled cardinality, stated for the actual subtype datum. -/
theorem expect_zeroColorActualDatum_card
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (_D : ActualTubeDatum delta ι) (k : Nat) [NeZero k] :
    (𝔼 omega : ι → Fin k,
        (Fintype.card {i // i ∈ zeroColorSample k omega} : Real)) =
      (Fintype.card ι : Real) / (k : Real) := by
  simpa using (expect_zeroColorSample_card (alpha := ι) k)

/-- Real weight of one shaded piece.  Finiteness follows from compact
containment and is already proved by `shadingPiece_volume_lt_top`. -/
def shadingPieceRealWeight
    {ι : Type} {F : ConvexFamily ι} (Y : Shading F) (i : ι) : Real :=
  (shadingWeight Y i : Real)

/-- Total real shaded mass is the sum of the finite real piece weights. -/
theorem shadingMass_toReal_eq_sum_shadingPieceRealWeight
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F) :
    Y.shadingMass.toReal = ∑ i : ι, shadingPieceRealWeight Y i := by
  unfold Shading.shadingMass
  rw [ENNReal.toReal_sum]
  · rfl
  · intro i _hi
    exact (shadingPiece_volume_lt_top Y i).ne

/-- Exact first moment of the shading mass of the literal sampled actual
datum. -/
theorem expect_zeroColorActualDatum_shadingMass_toReal
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (k : Nat) [NeZero k] :
    (𝔼 omega : ι → Fin k,
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal) =
      D.shading.shadingMass.toReal / (k : Real) := by
  classical
  calc
    (𝔼 omega : ι → Fin k,
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal) =
        𝔼 omega : ι → Fin k,
          zeroColorSampleRealWeight k
            (shadingPieceRealWeight D.shading) omega := by
              apply Finset.expect_congr rfl
              intro omega _homega
              change
                (restrictActualTubeDatum D
                    (zeroColorSample k omega)).shading.shadingMass.toReal = _
              rw [restrictActualTubeDatum_shadingMass,
                ENNReal.toReal_sum]
              · rfl
              · intro i hi
                exact (shadingPiece_volume_lt_top D.shading i).ne
    _ = (∑ i : ι, shadingPieceRealWeight D.shading i) /
        (k : Real) := expect_zeroColorSample_realWeight k _
    _ = D.shading.shadingMass.toReal / (k : Real) := by
          rw [shadingMass_toReal_eq_sum_shadingPieceRealWeight]

/-- The real weight contributed by one member to one fixed convex test body. -/
noncomputable def containedBodyRealWeight
    {ι : Type} [Fintype ι] (F : ConvexFamily ι)
    (K : ConvexBody Space) (i : ι) : Real := by
  classical
  exact if (F i : Set Space) ⊆ (K : Set Space) then
      (volume (F i : Set Space)).toReal
    else 0

/-- Active contained mass, converted to `Real`, is the corresponding selected
sum of fixed-test weights. -/
theorem containedMassOn_toReal_eq_sum_containedBodyRealWeight
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (selected : Finset ι)
    (K : ConvexBody Space) :
    (containedMassOn F selected K).toReal =
      ∑ i ∈ selected, containedBodyRealWeight F K i := by
  classical
  unfold containedMassOn containedBodyRealWeight
  rw [ENNReal.toReal_sum]
  · conv_rhs => rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i
      simp [mem_containedIndices]
    · intro i _hi
      rfl
  · intro i _hi
    exact (F i).isCompact.measure_lt_top.ne

/-- Full contained mass is the full sum of fixed-test real weights. -/
theorem containedMass_toReal_eq_sum_containedBodyRealWeight
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) :
    (containedMass F K).toReal =
      ∑ i : ι, containedBodyRealWeight F K i := by
  rw [← containedMassOn_univ]
  simpa using
    containedMassOn_toReal_eq_sum_containedBodyRealWeight
      F (Finset.univ : Finset ι) K

/-- For each *fixed* convex body, sampled contained mass has the exact first
moment `1/k` of the original contained mass.  The theorem deliberately does
not exchange the expectation with the supremum over all convex bodies. -/
theorem expect_zeroColorSample_containedMassOn_toReal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (K : ConvexBody Space)
    (k : Nat) [NeZero k] :
    (𝔼 omega : ι → Fin k,
        (containedMassOn F (zeroColorSample k omega) K).toReal) =
      (containedMass F K).toReal / (k : Real) := by
  classical
  calc
    (𝔼 omega : ι → Fin k,
        (containedMassOn F (zeroColorSample k omega) K).toReal) =
        𝔼 omega : ι → Fin k,
          zeroColorSampleRealWeight k (containedBodyRealWeight F K) omega := by
            apply Finset.expect_congr rfl
            intro omega _homega
            exact containedMassOn_toReal_eq_sum_containedBodyRealWeight
              F (zeroColorSample k omega) K
    _ = (∑ i : ι, containedBodyRealWeight F K i) /
        (k : Real) := expect_zeroColorSample_realWeight k _
    _ = (containedMass F K).toReal / (k : Real) := by
          rw [containedMass_toReal_eq_sum_containedBodyRealWeight]

#print axioms ActualTubeDatum.IsAdmissible.restrictTo
#print axioms restrictActualTubeDatum_shadingMass
#print axioms restrictActualTubeDatum_shadedUnion_subset
#print axioms expect_zeroColorSample_realWeight
#print axioms exists_zeroColorSample_realWeight_ge_expect
#print axioms expect_zeroColorActualDatum_card
#print axioms expect_zeroColorActualDatum_shadingMass_toReal
#print axioms expect_zeroColorSample_containedMassOn_toReal

end

end Family8GeneralizedKatzTaoMultiplicityV1
