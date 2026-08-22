import FamilyStickyGrounding.FamilyStickyActualTubeTranslationGridV1
import Submission.Kakeya.ConvexGeometry.Family
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSingleLoadCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1

noncomputable section

/-!
# Actual single-translation load cap from maximal concentration

This is the deterministic `X_j ≤ M` step in the appendix proof of
`lemrandommotion`.  The load is the literal number of active tubes whose
actual translate lies in the test body.  Uniform tube-volume lower bounds and
the actual maximal concentration bound control that cardinality.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- The active family after one actual grid translation. -/
def translatedActiveFamily
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (g : translation) : ConvexFamily {i // i ∈ G.tubes} :=
  fun i => (translateTube (G.tube i.1) (G.gridVector g)).body

/-- The contained indices of the translated active family have exactly the
literal `singleLoad` cardinality. -/
theorem card_containedIndices_translatedActiveFamily
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation) :
    (containedIndices (translatedActiveFamily G g) (G.testBody K)).card =
      G.singleLoad K g := by
  classical
  unfold containedIndices translatedActiveFamily
    FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid.singleLoad
  rw [Finset.univ_eq_attach G.tubes, Finset.filter_attach']
  rw [Finset.card_map, Finset.card_attach]
  apply congrArg Finset.card
  ext i
  simp [Tube.coe_body]
/-- Every contained translated tube contributes at least `delta²/2` to the
actual contained mass. -/
theorem singleLoad_mul_half_sq_le_containedMass
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation)
    (hdelta : delta <= (2 : NNReal)⁻¹) :
    (G.singleLoad K g : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
      ∑ i ∈ containedIndices (translatedActiveFamily G g) (G.testBody K),
        volume (translatedActiveFamily G g i : Set Space) := by
  rw [← card_containedIndices_translatedActiveFamily G K g]
  rw [← nsmul_eq_mul]
  apply Finset.card_nsmul_le_sum
  intro i _hi
  change (delta : ENNReal) ^ 2 / 2 <=
    volume (translateTube (G.tube i.1) (G.gridVector g)).carrier
  rw [translateTube_volume]
  exact (G.tube i.1).half_sq_le_volume_of_le_half hdelta

/-- Actual `X_j ≤ M` mass inequality.  Finiteness of the maximal
concentration rules out the only `∞ * 0` obstruction when multiplying the
concentration quotient back by the test-body volume. -/
theorem singleLoad_mul_half_sq_le_maximalConcentration_mul_volume
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation)
    (hdelta : delta <= (2 : NNReal)⁻¹)
    (hmax : maximalConcentration (translatedActiveFamily G g) < ∞) :
    (G.singleLoad K g : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
      maximalConcentration (translatedActiveFamily G g) *
        volume (G.testBody K : Set Space) := by
  calc
    (G.singleLoad K g : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
        ∑ i ∈ containedIndices (translatedActiveFamily G g) (G.testBody K),
          volume (translatedActiveFamily G g i : Set Space) :=
      singleLoad_mul_half_sq_le_containedMass G K g hdelta
    _ <= maximalConcentration (translatedActiveFamily G g) *
          volume (G.testBody K : Set Space) := by
      have hconc := concentration_le_maximalConcentration
        (translatedActiveFamily G g) (G.testBody K)
      unfold concentration at hconc
      exact (ENNReal.div_le_iff_le_mul
        (Or.inr hmax.ne) (Or.inl (G.testBody K).isCompact.measure_lt_top.ne)).mp hconc

#print axioms card_containedIndices_translatedActiveFamily
#print axioms singleLoad_mul_half_sq_le_containedMass
#print axioms singleLoad_mul_half_sq_le_maximalConcentration_mul_volume

end ActualTubeTranslationGrid

end

end FamilyStickyActualSingleLoadCapV1
