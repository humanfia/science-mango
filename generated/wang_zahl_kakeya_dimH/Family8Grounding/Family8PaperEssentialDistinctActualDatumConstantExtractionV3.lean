import Family8Grounding.Family8PaperEssentialDistinctConstantExtractionV2
import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8PaperEssentialDistinctActualDatumConstantExtractionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8PaperEssentialDistinctConstantExtractionV2

noncomputable section

/-!
# A genuine actual-datum refinement with paper essential distinctness

The scale-independent conflict-code theorem is applied to the literal tube
map of an admissible `ActualTubeDatum`.  The selected object below is the
existing subtype restriction, not a new abstract family.  Thus its tubes and
shadings are inherited, admissibility is proved by the existing restriction
theorem, and its refinement is literally full.

Both cardinality and actual ENNReal shading mass are retained up to the same
absolute natural-number loss.  No Definition 2.12 hierarchy witness or
rescaled-fibre CWA is assumed or manufactured here.
-/

/-- An admissible actual tube datum has a genuine subtype whose tubes satisfy
the paper full-dilation distinctness convention, at one absolute loss in both
cardinality and shading mass. -/
theorem exists_paperEssentiallyDistinct_actualSubtype
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    ∃ selected : Finset index,
      (Nonempty index → Nonempty {i // i ∈ selected}) ∧
      (restrictActualTubeDatum D selected).IsAdmissible ∧
      (restrictActualTubeDatum D selected).family.refinement.refined =
        Finset.univ ∧
      (Set.Pairwise (Set.univ : Set {i // i ∈ selected}) fun i j =>
        PaperEssentiallyDistinct
          ((restrictActualTubeDatum D selected).family.tubes i)
          ((restrictActualTubeDatum D selected).family.tubes j)) ∧
      (Fintype.card index : ENNReal) ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (Fintype.card {i // i ∈ selected} : ENNReal) ∧
      D.shading.shadingMass ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (restrictActualTubeDatum D selected).shading.shadingMass := by
  classical
  have hsourcePairwise :
      Set.Pairwise (↑(Finset.univ : Finset index) : Set index) fun i j =>
        EssentiallyDistinct (D.family.tubes i) (D.family.tubes j) := by
    intro i _hi j _hj hij
    exact hD.pairwise_essentiallyDistinct (Set.mem_univ i)
      (Set.mem_univ j) hij
  obtain ⟨selected, _hselected, hnonempty, hpaper, hcard, hmass⟩ :=
    exists_paperEssentiallyDistinct_constant_greedyExtraction
      (Finset.univ : Finset index) D.family.tubes hD.delta_pos
      hdeltaSmall hsourcePairwise
      (fun i => volume (D.shading.carrier i))
  refine ⟨selected, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hindex
    rcases hindex with ⟨i⟩
    apply Finset.nonempty_coe_sort.mpr
    exact hnonempty ⟨i, Finset.mem_univ i⟩
  · exact
      Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hD selected
  · exact D.family.restrictTo_refined selected
  · intro i _hi j _hj hij
    change PaperEssentiallyDistinct (D.family.tubes i.1)
      (D.family.tubes j.1)
    apply hpaper i.property j.property
    exact fun hijValue => hij (Subtype.ext hijValue)
  · simpa only [Finset.card_univ, Fintype.card_coe] using hcard
  · rw [restrictActualTubeDatum_shadingMass]
    simpa only [Shading.shadingMass, Finset.sum_filter,
      Finset.mem_univ, if_true] using hmass

#print axioms exists_paperEssentiallyDistinct_actualSubtype

end
end Family8PaperEssentialDistinctActualDatumConstantExtractionV3
