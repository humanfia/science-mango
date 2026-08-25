import FamilyStickyGrounding.FamilyStickyPaperRandomMotionNumericalChoicesV1
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyPaperRandomMotionNondegeneracyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyPaperRandomMotionNumericalChoicesV1.ActualTubeTestData

noncomputable section

/-!
# Nondegeneracy of the canonical repetition count

The safe floor selector can be zero if an input mean exceeds its fixed-test
cap.  This module makes that obstruction explicit.  It proves `J >= 1` once
the source scale inequality puts the paper incidence mean below the cap; thus
no `Fin 0` endpoint is presented as random motion.
-/

namespace ActualTubeTestData

variable {delta : NNReal} {tubeIndex : Type*} [DecidableEq tubeIndex]

/-- Explicit source lower envelope for the fixed-test cap, using only the
inner box-volume certificate and the tube lower-volume scale. -/
def sourceMeanEnvelope
    (D : ActualTubeTestData delta tubeIndex) (Cbox : NNReal)
    (side : Fin D.testCard -> Fin 3 -> NNReal) (K : Fin D.testCard) : Real :=
  (((Cbox⁻¹ : NNReal) : Real) ^ 3 *
      ∏ i, (side K i : Real)) /
    ((delta : Real) ^ 2 / 2)

/-- Cross-multiplied form of the source scale inequality. -/
def SourceMeanScale
    (D : ActualTubeTestData delta tubeIndex) (Cbox : NNReal)
    (side : Fin D.testCard -> Fin 3 -> NNReal) (motionRadius : NNReal)
    (K : Fin D.testCard) : Prop :=
  (297 * (D.tubes.card : Real) * (side K 0 : Real) *
      (side K 1 : Real)) * ((delta : Real) ^ 2 / 2) <=
    (((Cbox⁻¹ : NNReal) : Real) ^ 3 *
      ∏ i, (side K i : Real)) * (motionRadius : Real) ^ 2

theorem paperIncidenceMean_le_sourceMeanEnvelope
    (D : ActualTubeTestData delta tubeIndex)
    {Cbox : NNReal} {side : Fin D.testCard -> Fin 3 -> NNReal}
    {motionRadius : NNReal} (hdeltaPos : 0 < delta)
    (hRadius : 0 < motionRadius) (K : Fin D.testCard)
    (hscale : SourceMeanScale D Cbox side motionRadius K) :
    paperIncidenceMean D side motionRadius K <=
      sourceMeanEnvelope D Cbox side K := by
  have hdeltaReal : (0 : Real) < (delta : Real) := by exact_mod_cast hdeltaPos
  have hRadiusReal : (0 : Real) < (motionRadius : Real) := by
    exact_mod_cast hRadius
  have hdeltaSq : 0 < (delta : Real) ^ 2 / 2 := by positivity
  have hRadiusSq : 0 < (motionRadius : Real) ^ 2 := by positivity
  unfold paperIncidenceMean sourceMeanEnvelope
  exact (div_le_div_iff₀ hRadiusSq hdeltaSq).2 hscale

/-- A nonempty actual tube family has maximal concentration at least one. -/
theorem one_le_activeFamily_maximalConcentration
    (D : ActualTubeTestData delta tubeIndex)
    (hdeltaPos : 0 < delta) (htubes : D.tubes.Nonempty) :
    (1 : ENNReal) <= maximalConcentration (activeFamily D.seedGrid) := by
  classical
  let i : {j // j ∈ D.tubes} := ⟨htubes.choose, htubes.choose_spec⟩
  let F := activeFamily D.seedGrid
  have hi : i ∈ containedIndices F (F i) := by
    exact (mem_containedIndices F (F i) i).2 Set.Subset.rfl
  have hvolPos : 0 < volume (F i : Set Space) := by
    simpa [F, activeFamily, seedGrid, Tube.coe_body] using
      (D.tube i.1).volume_pos hdeltaPos
  have hvolTop : volume (F i : Set Space) < ∞ :=
    (F i).isCompact.measure_lt_top
  have hmass : volume (F i : Set Space) <=
      ∑ j ∈ containedIndices F (F i), volume (F j : Set Space) := by
    exact Finset.single_le_sum
      (fun j _hj => (show (0 : ENNReal) <= volume (F j : Set Space) from bot_le)) hi
  have hconc : (1 : ENNReal) <= concentration F (F i) := by
    unfold concentration
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hvolPos.ne') (Or.inl hvolTop.ne)).2
    simpa using hmass
  exact hconc.trans (concentration_le_maximalConcentration F (F i))

/-- The box lower volume and `Delta_max >= 1` put the explicit source
envelope below the canonical fixed-test cap. -/
theorem sourceMeanEnvelope_le_canonicalPaperSingleLoadCap
    (D : ActualTubeTestData delta tubeIndex)
    {Cbox : NNReal} {side : Fin D.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions Cbox (side K) (D.testBody K))
    (hdeltaPos : 0 < delta) (htubes : D.tubes.Nonempty)
    (K : Fin D.testCard) :
    sourceMeanEnvelope D Cbox side K <=
      D.canonicalPaperSingleLoadCap K := by
  let geom : ENNReal :=
    ((Cbox⁻¹ : NNReal) : ENNReal) ^ 3 *
      ∏ i, (side K i : ENNReal)
  let lower : ENNReal := (delta : ENNReal) ^ 2 / 2
  have hgeom : geom <= volume (D.testBody K : Set Space) := by
    simpa [geom] using (hdim K).volume_lower_bound
  have hDelta : (1 : ENNReal) <=
      maximalConcentration (activeFamily D.seedGrid) :=
    one_le_activeFamily_maximalConcentration D hdeltaPos htubes
  have hnum : geom <= maximalConcentration (activeFamily D.seedGrid) *
      volume (D.testBody K : Set Space) := by
    calc
      geom <= volume (D.testBody K : Set Space) := hgeom
      _ = 1 * volume (D.testBody K : Set Space) := by simp
      _ <= maximalConcentration (activeFamily D.seedGrid) *
          volume (D.testBody K : Set Space) := by gcongr
  have hratio : geom / lower <=
      maximalConcentration (activeFamily D.seedGrid) *
        volume (D.testBody K : Set Space) / lower :=
    ENNReal.div_le_div_right hnum lower
  have hdeltaENN : (0 : ENNReal) < (delta : ENNReal) :=
    ENNReal.coe_pos.mpr hdeltaPos
  have hlowerPos : 0 < lower := by
    exact ENNReal.div_pos (ENNReal.pow_pos hdeltaENN 2).ne' (by norm_num)
  have hrightTop :
      maximalConcentration (activeFamily D.seedGrid) *
          volume (D.testBody K : Set Space) / lower ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top
        (FamilyStickyFiniteFamilyMaximalConcentrationV1.maximalConcentration_lt_top
          (activeFamily D.seedGrid)).ne
        (D.testBody K).isCompact.measure_lt_top.ne
    · exact hlowerPos.ne'
  have hreal := ENNReal.toReal_mono hrightTop hratio
  simpa [sourceMeanEnvelope, canonicalPaperSingleLoadCap,
    paperSingleLoadCap, tubeLowerScale, seedGrid, geom, lower] using hreal

/-- The paper incidence mean is below its cap under the explicit source scale
condition.  Empty tube families are handled separately and give zero mean. -/
theorem paperIncidenceMean_le_canonicalPaperSingleLoadCap
    (D : ActualTubeTestData delta tubeIndex)
    {Cbox : NNReal} {side : Fin D.testCard -> Fin 3 -> NNReal}
    {motionRadius : NNReal}
    (hdim : forall K, HasBoxDimensions Cbox (side K) (D.testBody K))
    (hdeltaPos : 0 < delta) (hRadius : 0 < motionRadius)
    (K : Fin D.testCard)
    (hscale : SourceMeanScale D Cbox side motionRadius K) :
    paperIncidenceMean D side motionRadius K <=
      D.canonicalPaperSingleLoadCap K := by
  by_cases htubes : D.tubes.Nonempty
  · exact (paperIncidenceMean_le_sourceMeanEnvelope D hdeltaPos hRadius K hscale).trans
      (sourceMeanEnvelope_le_canonicalPaperSingleLoadCap
        D hdim hdeltaPos htubes K)
  · have hempty : D.tubes = ∅ := Finset.not_nonempty_iff_eq_empty.mp htubes
    have hmeanZero : paperIncidenceMean D side motionRadius K = 0 := by
      simp [paperIncidenceMean, hempty]
    rw [hmeanZero]
    unfold canonicalPaperSingleLoadCap
    exact ENNReal.toReal_nonneg

/-- The floor/inf repetition selector is nonzero once every active mean is
below its cap. -/
theorem one_le_paperRepetitions_of_mean_le_cap
    (D : ActualTubeTestData delta tubeIndex)
    (mean : Fin D.testCard -> Real)
    (hunit : forall K, K ∈ D.activeTests ->
      mean K <= D.canonicalPaperSingleLoadCap K) :
    1 <= paperRepetitions D mean := by
  by_cases hpositive : (positiveMeanTests D mean).Nonempty
  · rw [paperRepetitions, dif_pos hpositive]
    apply Nat.le_floor
    apply Finset.le_inf' hpositive
    intro K hK
    have hKactive : K ∈ D.activeTests := (Finset.mem_filter.mp hK).1
    have hKpos : 0 < mean K := (Finset.mem_filter.mp hK).2
    exact (le_div_iff₀ hKpos).2 (by simpa using hunit K hKactive)
  · simp [paperRepetitions, hpositive]

/-- Fully automatic nondegeneracy from the explicit source scale. -/
theorem one_le_paperRepetitions_of_sourceScales
    (D : ActualTubeTestData delta tubeIndex)
    {Cbox : NNReal} {side : Fin D.testCard -> Fin 3 -> NNReal}
    {motionRadius : NNReal}
    (hdim : forall K, HasBoxDimensions Cbox (side K) (D.testBody K))
    (hdeltaPos : 0 < delta) (hRadius : 0 < motionRadius)
    (hscale : forall K, K ∈ D.activeTests ->
      SourceMeanScale D Cbox side motionRadius K) :
    1 <= paperRepetitions D (paperIncidenceMean D side motionRadius) := by
  apply one_le_paperRepetitions_of_mean_le_cap D
  intro K hK
  exact paperIncidenceMean_le_canonicalPaperSingleLoadCap
    D hdim hdeltaPos hRadius K (hscale K hK)

#print axioms paperIncidenceMean_le_sourceMeanEnvelope
#print axioms one_le_activeFamily_maximalConcentration
#print axioms sourceMeanEnvelope_le_canonicalPaperSingleLoadCap
#print axioms paperIncidenceMean_le_canonicalPaperSingleLoadCap
#print axioms one_le_paperRepetitions_of_sourceScales

end ActualTubeTestData

end
end FamilyStickyPaperRandomMotionNondegeneracyV1
