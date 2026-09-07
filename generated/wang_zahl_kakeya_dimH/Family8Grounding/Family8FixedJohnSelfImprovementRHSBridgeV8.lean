import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWATailConnectorV5
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnSelfImprovementRHSBridgeV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWATailConnectorV5
open Family8AllFrostmanStickyUnionProducerV1

noncomputable section

/-!
# Mechanical RHS bridge after the automatic fixed-John refinement

This file does not assert a one-step self-improvement theorem.  It isolates
the exact algebra which follows from the existing fixed-John endpoint.  In
particular, it proves that the selected normalized family costs at most one
quarter of the source volume per rigid copy.  The remaining loss is then a
finite scalar power budget, rather than a hidden final-multiplicity callback.
-/

/-- Eighth normalization (including the unit-axis extension) costs at most
one quarter of the summed source tube volume. -/
theorem eighthNormalizedDatum_actualFamilyVolume_le_quarter
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    (eighthNormalizedDatum D).actualFamilyVolume <=
      (1 / 4 : ENNReal) * D.actualFamilyVolume := by
  unfold ActualTubeDatum.actualFamilyVolume familyVolume
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body,
    eighthNormalizedDatum_family, eighthNormalizedTubeFamily_tubes]
  calc
    (∑ i : iota, volume (eighthNormalizedTube (D.family.tubes i)).carrier) <=
        ∑ i : iota, (1 / 4 : ENNReal) *
          volume (D.family.tubes i).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      exact eighthNormalizedTube_volume_le_quarter
        (D.family.tubes i) hdeltaHalf
    _ = (1 / 4 : ENNReal) *
        ∑ i : iota, volume (D.family.tubes i).carrier := by
      rw [Finset.mul_sum]

#print axioms eighthNormalizedDatum_actualFamilyVolume_le_quarter

end
end Family8FixedJohnSelfImprovementRHSBridgeV8
