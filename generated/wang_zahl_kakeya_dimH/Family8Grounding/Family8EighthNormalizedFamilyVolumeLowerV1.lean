import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizedDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EighthNormalizedFamilyVolumeLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizationCarrierV1
open Family8FiniteRandomRigidMotionB2DilationVolumeV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1

noncomputable section

/-!
# Lower family-volume transport under the honest eighth normalization

The normalized tube is an extension of the literal eighth-dilation of the
source tube.  Thus its volume is at least the exact three-dimensional
Jacobian factor `1 / 512` times the source volume, tube by tube and hence
after summing over the family.
-/

/-- Eighth normalization retains at least the literal eighth-dilated family
volume. -/
theorem one_div_512_mul_familyVolume_le_eighthNormalized
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) :
    (1 / 512 : ENNReal) * familyVolume D.family.bodyFamily ≤
      familyVolume (eighthNormalizedDatum D).family.bodyFamily := by
  unfold familyVolume
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _hi => by
    rw [← volume_image_eighthDilationPoint]
    apply measure_mono
    simpa only [eighthNormalizedDatum, eighthNormalizedTubeFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body] using
      image_eighthDilation_tube_carrier_subset_normalizedTube
        (D.family.tubes i)

#print axioms one_div_512_mul_familyVolume_le_eighthNormalized

end
end Family8EighthNormalizedFamilyVolumeLowerV1
