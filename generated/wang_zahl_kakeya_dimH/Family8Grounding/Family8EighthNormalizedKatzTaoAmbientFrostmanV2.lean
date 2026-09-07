import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Mathlib.Tactic

/-!
# Canonical ambient Frostman control after honest eighth normalization

Global Katz--Tao control alone does not imply an ambient Frostman estimate:
one must also normalize by the mass captured in the ambient body.  For an
eighth-normalized nonempty B2-supported actual datum, every normalized tube
lies in the unit ball and the captured mass is the full, positive, finite
family volume.  The literal quotient below therefore supplies exactly the
missing normalization, with no callback and no change of family.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EighthNormalizedKatzTaoAmbientFrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-- The exact unit-ball normalization of the transported Katz--Tao
constant.  The denominator is the literal normalized family volume. -/
def eighthNormalizedKatzTaoAmbientFrostmanConstant
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (C : ENNReal) (D : ActualTubeDatum delta iota) : ENNReal :=
  (128 * C) * volume (unitBallBody : Set Space) /
    familyVolume (eighthNormalizedDatum D).family.bodyFamily

/-- Honest eighth normalization turns global Katz--Tao control into a
unit-ball Frostman certificate with the exact ambient-density quotient.

The only geometric hypotheses are the ones used by the normalization
itself: positive half-scale tubes, a nonempty index type, and B2 support.
-/
theorem eighthNormalizedDatum_isFrostmanIn_of_isKatzTao
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hB2 : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily) :
    IsFrostmanIn
      (eighthNormalizedKatzTaoAmbientFrostmanConstant C D)
      (eighthNormalizedDatum D).family.bodyFamily unitBallBody := by
  have hcontained : ∀ i,
      ((eighthNormalizedDatum D).family.bodyFamily i : Set Space) ⊆
        (unitBallBody : Set Space) := by
    intro i
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body,
      coe_unitBallBody] using
        eighthNormalizedDatum_contained_in_unit_ball
          D hdeltaHalf hB2 i
  have hfamilyZero :
      familyVolume (eighthNormalizedDatum D).family.bodyFamily ≠ 0 :=
    (actualDatum_familyVolume_pos_of_scale
      (eighthNormalizedDatum D)
      (div_pos hdeltaPos (by norm_num))).ne'
  have hfamilyTop :
      familyVolume (eighthNormalizedDatum D).family.bodyFamily ≠ ∞ :=
    familyVolume_ne_top (eighthNormalizedDatum D).family.bodyFamily
  have hmass : containedMass
      (eighthNormalizedDatum D).family.bodyFamily unitBallBody =
        familyVolume (eighthNormalizedDatum D).family.bodyFamily :=
    containedMass_eq_familyVolume_of_contained
      (eighthNormalizedDatum D).family.bodyFamily unitBallBody hcontained
  have hKTNormalized : IsKatzTao (128 * C)
      (eighthNormalizedDatum D).family.bodyFamily :=
    eighthNormalizedDatum_isKatzTao D hdeltaHalf hKT
  apply IsKatzTao.isFrostmanIn hKTNormalized hcontained
  rw [hmass]
  unfold eighthNormalizedKatzTaoAmbientFrostmanConstant
  rw [ENNReal.div_mul_cancel hfamilyZero hfamilyTop]

#print axioms eighthNormalizedKatzTaoAmbientFrostmanConstant
#print axioms eighthNormalizedDatum_isFrostmanIn_of_isKatzTao

end
end Family8EighthNormalizedKatzTaoAmbientFrostmanV2
