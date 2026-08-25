import FamilyStickyGrounding.FamilyStickyActualPaperSingleLoadProducerV1
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualPaperSingleLoadAutomaticV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid
open FamilyStickyFiniteFamilyMaximalConcentrationV1

noncomputable section

/-!
# Automatic paper single-load cap

The active family is finite by construction, so its maximal concentration is
bounded by its index cardinality.  This discharges the sole source-level
finiteness input of the paper single-load producer without a callback.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

theorem activeFamily_maximalConcentration_lt_top
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    maximalConcentration (activeFamily G) < ∞ :=
  FamilyStickyFiniteFamilyMaximalConcentrationV1.maximalConcentration_lt_top
    (activeFamily G)

/-- The paper's fixed-test cap now follows solely from the actual grid and
the tube-radius hypotheses. -/
theorem singleLoad_real_le_paperSingleLoadCap
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta) :
    (G.singleLoad K g : Real) <= paperSingleLoadCap G K :=
  FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid.singleLoad_real_le_paperSingleLoadCap
    G K g hdelta hdeltaPos (activeFamily_maximalConcentration_lt_top G)

#print axioms activeFamily_maximalConcentration_lt_top
#print axioms singleLoad_real_le_paperSingleLoadCap

end ActualTubeTranslationGrid

end
end FamilyStickyActualPaperSingleLoadAutomaticV1
