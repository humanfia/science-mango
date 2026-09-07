import Family8Grounding.Family8StickyActiveCoarseFullDatumV1
import Family8Grounding.Family8StickyActiveCoarseB2SupportV5
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalFullCoarseDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8StickyActiveCoarseFullDatumV1
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness

noncomputable section

/-!
# The canonical full-shaded coarse datum at the buffered global scale

This is the literal paper object `T_b`: its index type is the actual active
coarse subtype of the canonical global cover and its shading is every full
coarse tube carrier.  Active sticky parents are automatically B2-supported.
One honest eighth-normalization therefore gives a unit-ball-supported datum
without changing average multiplicity.  The subsequent fresh endpoint uses
one more eighth-normalization, so its final fixed scale is recorded as
`b / 64`.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

def canonicalBufferedGlobalFullCoarseDatum
    (D : ActualTubeDatum delta index)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    ActualTubeDatum (canonicalBufferedRadius W)
      {k // k ∈ (canonicalBufferedGlobalCover W hdelta
        hepsilon hepsilonHalf).activeCoarse} :=
  activeCoarseFullDatum
    (canonicalBufferedGlobalCover W hdelta hepsilon hepsilonHalf)

def canonicalBufferedGlobalUnitCoarseDatum
    (D : ActualTubeDatum delta index)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    ActualTubeDatum (canonicalBufferedRadius W / 8)
      {k // k ∈ (canonicalBufferedGlobalCover W hdelta
        hepsilon hepsilonHalf).activeCoarse} :=
  eighthNormalizedDatum
    (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
      hdelta hepsilon hepsilonHalf)

@[simp]
theorem canonicalBufferedGlobalFullCoarseDatum_card
    (D : ActualTubeDatum delta index)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    Fintype.card {k // k ∈ (canonicalBufferedGlobalCover W hdelta
      hepsilon hepsilonHalf).activeCoarse} =
      (canonicalBufferedGlobalCover W hdelta
        hepsilon hepsilonHalf).activeCoarse.card := by
  simp

theorem canonicalBufferedGlobalFullCoarseDatum_B2
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal)) :
    forall k,
      ((canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos hepsilon hepsilonHalf).family.tubes k).carrier ⊆
          Metric.closedBall (0 : Space) 2 := by
  intro k
  simpa only [canonicalBufferedGlobalFullCoarseDatum,
    activeCoarseFullDatum_family_tubes,
    StickyScaleCover.activeCoarseFamily,
    UniformTubeFamily.bodyFamily_apply,
    Tube.coe_body] using
      (Family8StickyActiveCoarseB2SupportV5.activeCoarseFamily_body_subset_closedBall_two
        D hD
        (canonicalBufferedGlobalCover W hD.delta_pos
          hepsilon hepsilonHalf)
        hbufferedSixteenth k)

theorem canonicalBufferedGlobalUnitCoarseDatum_contained_in_unit_ball
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal)) :
    forall k,
      ((canonicalBufferedGlobalUnitCoarseDatum D Cmulti Sseq W
        hD.delta_pos hepsilon hepsilonHalf).family.tubes k).carrier ⊆
          Metric.closedBall (0 : Space) 1 := by
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) <= 16 by norm_num)))
  exact eighthNormalizedDatum_contained_in_unit_ball
    (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
      hD.delta_pos hepsilon hepsilonHalf)
    hrhoHalf
    (canonicalBufferedGlobalFullCoarseDatum_B2 D hD Cmulti Sseq W
      hepsilon hepsilonHalf hbufferedSixteenth)

theorem canonicalBufferedGlobalUnitCoarseDatum_averageMultiplicity
    (D : ActualTubeDatum delta index)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2) :
    (canonicalBufferedGlobalUnitCoarseDatum D Cmulti Sseq W
      hdelta hepsilon hepsilonHalf).shading.averageMultiplicity =
    (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
      hdelta hepsilon hepsilonHalf).shading.averageMultiplicity :=
  eighthNormalized_activeCoarseFullDatum_averageMultiplicity _

theorem canonicalBufferedGlobalUnitCoarseDatum_density_lower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal)) :
    (1 / 128 : ENNReal) <=
      (canonicalBufferedGlobalUnitCoarseDatum D Cmulti Sseq W
        hD.delta_pos hepsilon hepsilonHalf).shading.shadingDensity := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon hepsilonHalf
  have hcoarse : G.activeCoarse.Nonempty :=
    canonicalBufferedGlobalCover_activeCoarse_nonempty W hD.delta_pos
      hepsilon hepsilonHalf hfine
  let _ : Nonempty {k // k ∈ G.activeCoarse} :=
    Finset.nonempty_coe_sort.mpr hcoarse
  have hrho : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hepsilon
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) <= 16 by norm_num)))
  exact eighthNormalized_activeCoarseFullDatum_density_lower
    G hrho hrhoHalf

theorem canonicalBufferedGlobalUnitCoarseDatum_isKatzTao
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT) :
    IsKatzTao (128 * CKT)
      (canonicalBufferedGlobalUnitCoarseDatum D Cmulti Sseq W
        hD.delta_pos hepsilon hepsilonHalf).family.bodyFamily := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon hepsilonHalf
  have hscale : delta <= canonicalBufferedRadius W :=
    (Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon)
  have hrhoOne : canonicalBufferedRadius W <= 1 :=
    hbufferedSixteenth.trans (by
      simpa only [one_div, inv_one] using
        (inv_anti₀ (show (0 : NNReal) < 1 by norm_num)
          (show (1 : NNReal) <= 16 by norm_num)))
  have hGKT : G.IsKatzTaoAtScale CKT :=
    hKTEvery (canonicalBufferedRadius W) hscale hrhoOne
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) <= 16 by norm_num)))
  exact eighthNormalized_activeCoarseFullDatum_isKatzTao
    G hrhoHalf hGKT

theorem canonicalBufferedGlobal_doubleEighthScale_eq
    (D : ActualTubeDatum delta index)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilon eta Sseq) :
    (canonicalBufferedRadius W / 8) / 8 =
      canonicalBufferedRadius W / 64 := by
  ring

#print axioms canonicalBufferedGlobalFullCoarseDatum
#print axioms canonicalBufferedGlobalUnitCoarseDatum
#print axioms canonicalBufferedGlobalFullCoarseDatum_card
#print axioms canonicalBufferedGlobalFullCoarseDatum_B2
#print axioms canonicalBufferedGlobalUnitCoarseDatum_contained_in_unit_ball
#print axioms canonicalBufferedGlobalUnitCoarseDatum_averageMultiplicity
#print axioms canonicalBufferedGlobalUnitCoarseDatum_density_lower
#print axioms canonicalBufferedGlobalUnitCoarseDatum_isKatzTao
#print axioms canonicalBufferedGlobal_doubleEighthScale_eq

end Witness
end
end Family8CanonicalBufferedGlobalFullCoarseDatumV1
