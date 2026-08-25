import FamilyStickyGrounding.FamilyStickyActualSingleLoadNumericsV1
import FamilyStickyGrounding.FamilyStickyConvexBodyTranslationConcentrationV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualPaperSingleLoadProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualSingleLoadCapV1
open FamilyStickyActualSingleLoadCapV1.ActualTubeTranslationGrid
open FamilyStickyConvexBodyTranslationConcentrationV1

noncomputable section

/-!
# Paper single-load cap from untranslated maximal concentration

For GWZ Appendix lines 2687--2691, `X_j` is the literal contained translated
tube count and

`X_j |T_delta| <= Delta_max(T) |K|`.

This module proves that statement for the actual grid.  Common translation
preserves maximal concentration exactly, so the only source-level finiteness
input is the untranslated active family's `Delta_max < infinity`.  The
test-dependent real cap is then produced canonically by dividing by the
proved lower tube-volume scale `delta^2 / 2`; no mass-budget hypothesis is
accepted.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- The untranslated active tube family, preserving repetitions by subtype
indexing. -/
def activeFamily
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    ConvexFamily {i // i ∈ G.tubes} :=
  fun i => (G.tube i.1).body

/-- The existing actual translated family is exactly common convex-body
translation of the untranslated active family. -/
theorem translatedActiveFamily_eq_translateFamily
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (g : translation) :
    translatedActiveFamily G g =
      translateFamily (activeFamily G) (G.gridVector g) := by
  funext i
  exact translateTube_body_eq_translateConvexBody
    (G.tube i.1) (G.gridVector g)

/-- Maximal concentration is independent of the selected shared translation. -/
theorem maximalConcentration_translatedActiveFamily
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (g : translation) :
    maximalConcentration (translatedActiveFamily G g) =
      maximalConcentration (activeFamily G) := by
  rw [translatedActiveFamily_eq_translateFamily,
    maximalConcentration_translateFamily]

def tubeLowerScale
    (_G : ActualTubeTranslationGrid delta translation tubeIndex) : ENNReal :=
  (delta : ENNReal) ^ 2 / 2

/-- The test-dependent paper cap `Delta_max(T) |K| / (delta^2/2)`. -/
def paperSingleLoadCap
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) : Real :=
  (maximalConcentration (activeFamily G) *
      volume (G.testBody K : Set Space) / tubeLowerScale G).toReal

/-- Literal actual version of `X_j |T_delta| <= Delta_max(T) |K|`. -/
theorem singleLoad_mul_tubeLowerScale_le_baseMaximalConcentration_mul_volume
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation)
    (hdelta : delta <= (2 : NNReal)⁻¹)
    (hbase : maximalConcentration (activeFamily G) < ∞) :
    (G.singleLoad K g : ENNReal) * tubeLowerScale G <=
      maximalConcentration (activeFamily G) *
        volume (G.testBody K : Set Space) := by
  have htranslated :
      maximalConcentration (translatedActiveFamily G g) < ∞ := by
    rwa [maximalConcentration_translatedActiveFamily]
  have h := singleLoad_mul_half_sq_le_maximalConcentration_mul_volume
    G K g hdelta htranslated
  change (G.singleLoad K g : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
    maximalConcentration (activeFamily G) * volume (G.testBody K : Set Space)
  rw [maximalConcentration_translatedActiveFamily G g] at h
  exact h

/-- Canonically produced real single-load bound for one fixed test `K`,
uniform in the translation outcome `g`. -/
theorem singleLoad_real_le_paperSingleLoadCap
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hbase : maximalConcentration (activeFamily G) < ∞) :
    (G.singleLoad K g : Real) <= paperSingleLoadCap G K := by
  have hdeltaENN : (0 : ENNReal) < (delta : ENNReal) :=
    ENNReal.coe_pos.mpr hdeltaPos
  have hlowerPos : 0 < tubeLowerScale G := by
    exact ENNReal.div_pos (ENNReal.pow_pos hdeltaENN 2).ne' (by norm_num)
  have hlowerNeTop : tubeLowerScale G ≠ ∞ := by
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (by norm_num)
  have hmass :=
    singleLoad_mul_tubeLowerScale_le_baseMaximalConcentration_mul_volume
      G K g hdelta hbase
  have hratio :
      (G.singleLoad K g : ENNReal) <=
        maximalConcentration (activeFamily G) *
          volume (G.testBody K : Set Space) / tubeLowerScale G :=
    (ENNReal.le_div_iff_mul_le (Or.inl hlowerPos.ne')
      (Or.inl hlowerNeTop)).2 hmass
  have hratioNeTop :
      maximalConcentration (activeFamily G) *
          volume (G.testBody K : Set Space) / tubeLowerScale G ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top hbase.ne
        (G.testBody K).isCompact.measure_lt_top.ne
    · exact hlowerPos.ne'
  have hreal := ENNReal.toReal_mono hratioNeTop hratio
  simpa only [paperSingleLoadCap, ENNReal.toReal_natCast] using hreal

/-- Uniform source-facing wrapper: one untranslated `Delta_max` finiteness
certificate produces all fixed-test, all-translation single-load caps. -/
theorem singleLoad_real_le_paperSingleLoadCap_all
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hbase : maximalConcentration (activeFamily G) < ∞) :
    forall K, K ∈ G.activeTests -> forall g,
      (G.singleLoad K g : Real) <= paperSingleLoadCap G K := by
  intro K _hK g
  exact singleLoad_real_le_paperSingleLoadCap
    G K g hdelta hdeltaPos hbase

#print axioms maximalConcentration_translatedActiveFamily
#print axioms singleLoad_mul_tubeLowerScale_le_baseMaximalConcentration_mul_volume
#print axioms singleLoad_real_le_paperSingleLoadCap
#print axioms singleLoad_real_le_paperSingleLoadCap_all

end ActualTubeTranslationGrid

end


end FamilyStickyActualPaperSingleLoadProducerV1
