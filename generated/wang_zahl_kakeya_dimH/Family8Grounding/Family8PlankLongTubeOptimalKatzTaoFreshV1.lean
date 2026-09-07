import Family8Grounding.Family8PlankLongTubeCanonicalGlobalKatzTaoBoundV1
import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1
import Family8Grounding.Family8FixedJohnAutomaticRepetitionUpperV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankLongTubeOptimalKatzTaoFreshV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeFrostmanTransferV3
open Family8PlankLongTubeGlobalKatzTaoV3
open Family8PlankLongTubeCenteredFreshV4
open Family8PlankLongTubeCanonicalGlobalKatzTaoBoundV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1
open Family8FixedJohnAutomaticRepetitionUpperV1
open Family8ActiveCoarseCanonicalFrostmanXLowerV3

noncomputable section

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The best coefficient available without a new geometric estimate: the
minimum of the canonical long-tube coefficient and the exact source index
cardinality. -/
def plankLongTubeOptimalKatzTaoConstant
    (D : ShadedConvexPlankFamily iota a b) : ENNReal :=
  min
    (plankLongTubeGlobalKatzTaoConstant D
      (canonicalFrostmanConstant D.family D.ambient))
    (Fintype.card (Unit × iota) : ENNReal)

theorem plankLongTubeOptimalKatzTaoConstant_le_canonical
    (D : ShadedConvexPlankFamily iota a b) :
    plankLongTubeOptimalKatzTaoConstant D ≤
      plankLongTubeGlobalKatzTaoConstant D
        (canonicalFrostmanConstant D.family D.ambient) := by
  exact min_le_left _ _

theorem plankLongTubeOptimalKatzTaoConstant_le_card
    (D : ShadedConvexPlankFamily iota a b) :
    plankLongTubeOptimalKatzTaoConstant D ≤
      (Fintype.card (Unit × iota) : ENNReal) := by
  exact min_le_right _ _

theorem plankLongTubeOptimalKatzTaoConstant_ne_top
    (D : ShadedConvexPlankFamily iota a b) :
    plankLongTubeOptimalKatzTaoConstant D ≠ ∞ := by
  exact ne_of_lt ((plankLongTubeOptimalKatzTaoConstant_le_card D).trans_lt
    (ENNReal.natCast_lt_top _))

/-- Both available certificates apply to the literal same centered source,
so their minimum is again an honest Katz--Tao coefficient. -/
theorem centeredPlankLongTubeActualDatum_isKatzTao_optimal
    [Nonempty iota]
    (D : ShadedConvexPlankFamily iota a b)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hfamily0 : familyVolume D.family ≠ 0) :
    IsKatzTao (plankLongTubeOptimalKatzTaoConstant D)
      (centeredPlankLongTubeActualDatum D).family.bodyFamily := by
  have hF : IsFrostmanIn
      (canonicalFrostmanConstant D.family D.ambient)
      D.family D.ambient := by
    apply canonicalFrostmanConstant_isFrostmanIn
      D.family D.ambient D.contained_in_ambient
    · rw [containedMass_eq_familyVolume_of_contained
        D.family D.ambient D.contained_in_ambient]
      exact hfamily0
    · rw [containedMass_eq_familyVolume_of_contained
        D.family D.ambient D.contained_in_ambient]
      exact familyVolume_ne_top D.family
  have hcanonical :
      IsKatzTao
        (plankLongTubeGlobalKatzTaoConstant D
          (canonicalFrostmanConstant D.family D.ambient))
        (centeredPlankLongTubeActualDatum D).family.bodyFamily :=
    centeredPlankLongTubeActualDatum_isKatzTao D hbHalf hF
  have hcard :
      IsKatzTao (Fintype.card (Unit × iota) : ENNReal)
        (centeredPlankLongTubeActualDatum D).family.bodyFamily :=
    isKatzTao_cardinality
      (centeredPlankLongTubeActualDatum D).family.bodyFamily
  unfold plankLongTubeOptimalKatzTaoConstant
  rcases le_total
      (plankLongTubeGlobalKatzTaoConstant D
        (canonicalFrostmanConstant D.family D.ambient))
      (Fintype.card (Unit × iota) : ENNReal) with hle | hle
  · rw [min_eq_left hle]
    exact hcanonical
  · rw [min_eq_right hle]
    exact hcard

/-- The optimal coefficient retains the canonical uniform envelope while
never exceeding the exact source cardinality. -/
theorem plankLongTubeOptimalKatzTaoConstant_le_uniformMin
    (D : ShadedConvexPlankFamily iota a b)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hfamily0 : familyVolume D.family ≠ 0) :
    plankLongTubeOptimalKatzTaoConstant D ≤
      min
        (plankLongTubeFrostmanCopyLoss D.comparisonConstant a b ^ 2 *
          maximalConcentration D.family)
        (Fintype.card (Unit × iota) : ENNReal) := by
  apply min_le_min
  · exact plankLongTubeGlobalKatzTaoConstant_canonical_le
      D hbHalf hfamily0
  · exact le_rfl

/-- Fresh selection driven by the minimum coefficient.  Its threshold and
all retained witnesses use the same `Copt`; there is no fallback to the
larger canonical coefficient after selection. -/
theorem exists_centeredPlankLongTube_fresh_admissible_optimal
    [Nonempty iota]
    (D : ShadedConvexPlankFamily iota a b)
    (hbPos : 0 < b) (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hfamily0 : familyVolume D.family ≠ 0) :
    let source := centeredPlankLongTubeActualDatum D
    let Copt := plankLongTubeOptimalKatzTaoConstant D
    let threshold := Nat.ceil ((480000 * (128 * Copt) : ENNReal).toReal)
    ∃ selected : Finset (Unit × iota),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum source) selected).IsAdmissible ∧
      (Fintype.card (Unit × iota) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum source).shading.shadingMass ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum source) selected).shading.shadingMass ∧
      IsKatzTao (128 * Copt)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) selected).family.bodyFamily ∧
      D.shading.averageMultiplicity ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum source) selected).shading.averageMultiplicity := by
  dsimp only
  let source := centeredPlankLongTubeActualDatum D
  let Copt := plankLongTubeOptimalKatzTaoConstant D
  let threshold := Nat.ceil ((480000 * (128 * Copt) : ENNReal).toReal)
  have hCoptFinite : Copt ≠ ∞ :=
    plankLongTubeOptimalKatzTaoConstant_ne_top D
  have hsourceKT : IsKatzTao Copt source.family.bodyFamily := by
    exact centeredPlankLongTubeActualDatum_isKatzTao_optimal
      D hbHalf hfamily0
  have hconflict : ∀ p,
      (normalizedConflictIndices source p).card ≤ threshold := by
    intro p
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      source hbPos hbHalf hCoptFinite hsourceKT p
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hsourceAverage⟩ :=
    exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
      source hbPos hbHalf
      (centeredPlankLongTubeActualDatum_B2 D hbHalf)
      hconflict hsourceKT
  refine ⟨selected, hselected, hadmissible, hcard, hmass,
    hselectedKT, ?_⟩
  exact (source_averageMultiplicity_le_centeredPlankLongTubeActualDatum D).trans
    hsourceAverage

#print axioms plankLongTubeOptimalKatzTaoConstant_le_canonical
#print axioms plankLongTubeOptimalKatzTaoConstant_le_card
#print axioms plankLongTubeOptimalKatzTaoConstant_ne_top
#print axioms centeredPlankLongTubeActualDatum_isKatzTao_optimal
#print axioms plankLongTubeOptimalKatzTaoConstant_le_uniformMin
#print axioms exists_centeredPlankLongTube_fresh_admissible_optimal

end

end Family8PlankLongTubeOptimalKatzTaoFreshV1
