import FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1

noncomputable section

universe u v

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- Forget the internal types of the same local Q/P witnesses while retaining
their literal ENNReal right-hand side.  This is a one-way projection of the
fully actual conclusion, not a new local-bound premise. -/
theorem exists_positiveCenterHighPayload_baseSampledLensRHS_of_conclusion
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) :
    exists rhs : ENNReal,
      volume base *
          ((pyzE2DegreeLower H.payload.finalLabel *
            (pyzE2DegreeLower H.payload.finalLabel -
              automaticCanonicalNearCap
                (positiveCenterHighPayloadGlobalNormData H) ballRadius) :
            Nat) : ENNReal) <= rhs := by
  unfold PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion at h
  dsimp only at h
  obtain ⟨Q, P, hQP⟩ := h
  exact ⟨_, hQP⟩

/-- The concrete local right-hand side chosen from the exact Q/P conclusion.
The accompanying theorem below is the only interface used by the finite sum,
so no finiteness or cancellation assumption is introduced. -/
noncomputable def positiveCenterHighPayload_baseChosenSampledLensRHS
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) : ENNReal :=
  Classical.choose
    (exists_positiveCenterHighPayload_baseSampledLensRHS_of_conclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh ballRadius h)

theorem positiveCenterHighPayload_base_mul_degree_le_chosenSampledLensRHS
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) :
    volume base *
        ((pyzE2DegreeLower H.payload.finalLabel *
          (pyzE2DegreeLower H.payload.finalLabel -
            automaticCanonicalNearCap
              (positiveCenterHighPayloadGlobalNormData H) ballRadius) :
          Nat) : ENNReal) <=
      positiveCenterHighPayload_baseChosenSampledLensRHS
        base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
          globalCenter tangencyExponent normExponent logCount H mesh
            ballRadius h :=
  Classical.choose_spec
    (exists_positiveCenterHighPayload_baseSampledLensRHS_of_conclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh ballRadius h)

/-- Sum the fully actual, same-Q-per-cell high-payload conclusions over an
arbitrary finite family of high cells.  Every local conclusion is constructed
by the concrete Family 7 theorem in this proof.  The only remaining inputs
are its explicit scalar geometry hypotheses, supplied pointwise because the
dyadic tangency label and normalized coarse fibre vary with the cell. -/
theorem exists_actualAllHighCenters_baseSampledLens_sum
    {center : Type v} [Fintype center] [DecidableEq center]
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (base : center -> Set (Real × Real))
    (hbase : forall c, MeasurableSet (base c))
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (htGlobal : 0 < tGlobal)
    (globalCenter : center -> Tube radius)
    (hglobalCenter : forall c,
      globalCenter c ∈ finiteMetricCoverCenters
        (activeTubeImage fine ambient) projectedTubePairCoefficientDistance
        tGlobal (fun T U => projectedTubePairCoefficientDistance_comm T U))
    (bucket : Int)
    (hbucket : forall i, i ∈ ambient ->
      actualProjectedTubeCBucket ((radius : Real) / 2) (fine.tubes i) =
        bucket)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (HAt : forall c,
      ActualHighPayloadWithNormNonconcentration volume (base c) (hbase c)
        fine
        (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
        f f1 f2 outerA outerB hOuter hf hf1 tGlobal (globalCenter c)
          tangencyExponent normExponent logCount)
    (mesh ballRadius : center -> Real)
    (hmesh : forall c, 0 < mesh c)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (sharp : forall c, ActualY1SharpFineScaleNumerics
      (radius : Real) (dyadicCeilUpper (HAt c).payload.tangencyLabel) tGlobal
        (outerB - outerA))
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (hmeshBase : forall c, mesh c <= Real.sqrt ((radius : Real) /
      prop41Y1PaperFineT (radius : Real)
        (dyadicCeilUpper (HAt c).payload.tangencyLabel) tGlobal) / 2)
    (hroom : forall c, automaticCanonicalNearCap
      (positiveCenterHighPayloadGlobalNormData (HAt c)) (ballRadius c) <
        pyzE2DegreeLower (HAt c).payload.finalLabel)
    (hnearRadiusLower : forall c,
      (positiveCenterHighPayloadGlobalNormData (HAt c)).delta <=
        10 * ballRadius c)
    (hnearRadiusUpper : forall c,
      10 * ballRadius c <=
        (positiveCenterHighPayloadGlobalNormData (HAt c)).ceiling)
    (hballRadiusLower : forall c,
      (positiveCenterHighPayloadGlobalNormData (HAt c)).delta <= ballRadius c)
    (hballRadiusUpper : forall c,
      ballRadius c <=
        (positiveCenterHighPayloadGlobalNormData (HAt c)).ceiling)
    (hsmall : forall c,
      ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
        (radius : Real) (dyadicCeilUpper (HAt c).payload.tangencyLabel)
          tGlobal (4 * ballRadius c))
    (hcount : forall c,
      ActualY1PaperFineCNormalizedSelectedCountingSmallness
        (radius : Real) (dyadicCeilUpper (HAt c).payload.tangencyLabel)
          tGlobal (4 * ballRadius c))
    (sourceMass : ENNReal)
    (hhalf : sourceMass / 2 <= ∑ c, volume (base c)) :
    exists hlocal : forall c,
      PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
        (base c) (hbase c) fine
        (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
        f f1 f2 outerA outerB hOuter hf hf1 tGlobal (globalCenter c)
          tangencyExponent normExponent logCount (HAt c) (mesh c)
            (ballRadius c),
      sourceMass / 2 <= ∑ c,
        positiveCenterHighPayload_baseChosenSampledLensRHS
          (base c) (hbase c) fine
          (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
            physicalBase hphysicalBase f hfContinuous outerA outerB)
          f f1 f2 outerA outerB hOuter hf hf1 tGlobal (globalCenter c)
            tangencyExponent normExponent logCount (HAt c) (mesh c)
              (ballRadius c) (hlocal c) := by
  let hlocal : forall c,
      PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
        (base c) (hbase c) fine
        (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
        f f1 f2 outerA outerB hOuter hf hf1 tGlobal (globalCenter c)
          tangencyExponent normExponent logCount (HAt c) (mesh c)
            (ballRadius c) := fun c =>
    positiveCenterHighPayload_baseWeightedGlobalSampledLens
      (base c) (hbase c) fine ambient physicalBase hphysicalBase f
        hfContinuous f1 f2 outerA outerB hOuter hf hf1 tGlobal htGlobal
          (globalCenter c) (hglobalCenter c) bucket hbucket tangencyExponent
            normExponent logCount (HAt c) (mesh c) (hmesh c) hparameter
              (sharp c) hft hf1Lower hf1Upper hf2 hf2Continuous (hmeshBase c)
                (ballRadius c) (hroom c) (hnearRadiusLower c)
                  (hnearRadiusUpper c) (hballRadiusLower c)
                    (hballRadiusUpper c) (hsmall c) (hcount c)
  refine ⟨hlocal, ?_⟩
  have hhalf' : sourceMass / 2 <=
      ∑ c ∈ (Finset.univ : Finset center), volume (base c) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using hhalf
  have hsum := half_sourceMass_le_sum_rhs_of_degreeGap
    (high := (Finset.univ : Finset center))
    (weight := fun c => volume (base c))
    (rhs := fun c =>
      positiveCenterHighPayload_baseChosenSampledLensRHS
        (base c) (hbase c) fine
        (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
        f f1 f2 outerA outerB hOuter hf hf1 tGlobal (globalCenter c)
          tangencyExponent normExponent logCount (HAt c) (mesh c)
            (ballRadius c) (hlocal c))
    (degreeGap := fun c =>
      pyzE2DegreeLower (HAt c).payload.finalLabel *
        (pyzE2DegreeLower (HAt c).payload.finalLabel -
          automaticCanonicalNearCap
            (positiveCenterHighPayloadGlobalNormData (HAt c))
              (ballRadius c)))
    sourceMass hhalf'
    (by
      intro c _hc
      have hc := hroom c
      have hd : 1 <= pyzE2DegreeLower (HAt c).payload.finalLabel := by
        omega
      have hdiff : 1 <= pyzE2DegreeLower (HAt c).payload.finalLabel -
          automaticCanonicalNearCap
            (positiveCenterHighPayloadGlobalNormData (HAt c))
              (ballRadius c) := by
        omega
      calc
        1 = 1 * 1 := by norm_num
        _ <= pyzE2DegreeLower (HAt c).payload.finalLabel *
            (pyzE2DegreeLower (HAt c).payload.finalLabel -
              automaticCanonicalNearCap
                (positiveCenterHighPayloadGlobalNormData (HAt c))
                  (ballRadius c)) := Nat.mul_le_mul hd hdiff
      )
    (by
      intro c _hc
      exact
        positiveCenterHighPayload_base_mul_degree_le_chosenSampledLensRHS
          (base c) (hbase c) fine
          (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
            physicalBase hphysicalBase f hfContinuous outerA outerB)
          f f1 f2 outerA outerB hOuter hf hf1 tGlobal (globalCenter c)
            tangencyExponent normExponent logCount (HAt c) (mesh c)
              (ballRadius c) (hlocal c))
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using hsum

#print axioms exists_positiveCenterHighPayload_baseSampledLensRHS_of_conclusion
#print axioms positiveCenterHighPayload_baseChosenSampledLensRHS
#print axioms positiveCenterHighPayload_base_mul_degree_le_chosenSampledLensRHS
#print axioms exists_actualAllHighCenters_baseSampledLens_sum

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
