import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionNormalizedBodyLoadCapScaleOnlyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FiniteRigidMotionOrthogonalNormalizationV4
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalTranslationV2
open Family8FiniteRigidMotionOrthogonalTranslationCWAProductMeanV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RigidCopyPolynomialJohnKatzTaoV1

noncomputable section

/-!
# Scale-only cap for one normalized rotation--translation body load

The raw source need not be admissible.  Katz--Tao control is assumed only
for its honest eighth normalization.  Normalization commutes exactly with
an orthogonal rotation and divides the translation by eight, so rigid
invariance transports that Katz--Tao certificate to every one-motion copy.
Every counted radius-`delta / 8` tube then contributes its literal
half-square volume inside the test body.

This is the pointwise-cap half of the common conflict/CWA selector.  It uses
only the half-scale inequality; in particular it does not assume source
essential distinctness, a selected tuple, or any Family 7 conclusion.
-/

/-- A one-motion arbitrary-body load is controlled by the normalized source
Katz--Tao constant, with the exact uniform tube-volume floor. -/
theorem normalizedOrthogonalTranslationBodyLoadNat_mul_halfSq_le
    {motionChoice sourceIndex testIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal}
    (rotation : motionChoice → OrthogonalThree)
    (translation : motionChoice → Space)
    (source : ActualTubeDatum delta sourceIndex)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (eighthNormalizedDatum source).family.bodyFamily)
    (testBody : testIndex → ConvexBody Space)
    (K : testIndex) (g : motionChoice) :
    (normalizedRigidBodyLoadNat
        (fun u ↦ orthogonalTranslationRigidMotion
          (rotation u) (translation u))
        source testBody K g : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≤
      C * volume (testBody K : Set Space) := by
  classical
  let R : RigidMotion :=
    orthogonalTranslationRigidMotion
      (rotation g) (eighthTranslationVector (translation g))
  let hits : Finset sourceIndex :=
    (Finset.univ : Finset sourceIndex).filter fun i ↦
      (eighthNormalizedTube
        (rigidTube
          (orthogonalTranslationRigidMotion
            (rotation g) (translation g))
          (source.family.tubes i))).carrier ⊆
        (testBody K : Set Space)
  have hload :
      normalizedRigidBodyLoadNat
          (fun u ↦ orthogonalTranslationRigidMotion
            (rotation u) (translation u))
          source testBody K g = hits.card := by
    rfl
  have hsubset :
      hits ⊆ containedIndices
        (fixedRigidCopyBodyFamily R
          (eighthNormalizedDatum source).family)
        (testBody K) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [mem_containedIndices]
    change
      (rigidTube R
        ((eighthNormalizedDatum source).family.tubes i)).carrier ⊆
          (testBody K : Set Space)
    simpa only [R, eighthNormalizedDatum_family,
      eighthNormalizedTubeFamily_tubes,
      eighthNormalizedTube_orthogonalTranslation] using hi.2
  have hrhoHalf : delta / 8 ≤ (2 : NNReal)⁻¹ :=
    (div_le_self (show 0 ≤ delta from bot_le)
      (by norm_num : (1 : NNReal) ≤ 8)).trans hdeltaHalf
  have hlower :
      (hits.card : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≤
        containedMass
          (fixedRigidCopyBodyFamily R
            (eighthNormalizedDatum source).family)
          (testBody K) := by
    calc
      (hits.card : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) =
          ∑ _i ∈ hits,
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) := by
              simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ hits,
          volume
            ((fixedRigidCopyBodyFamily R
              (eighthNormalizedDatum source).family i :
                ConvexBody Space) : Set Space) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact
          (rigidTube R
            ((eighthNormalizedDatum source).family.tubes i)).half_sq_le_volume_of_le_half
              hrhoHalf
      _ ≤ ∑ i ∈ containedIndices
          (fixedRigidCopyBodyFamily R
            (eighthNormalizedDatum source).family)
          (testBody K),
          volume
            ((fixedRigidCopyBodyFamily R
              (eighthNormalizedDatum source).family i :
                ConvexBody Space) : Set Space) :=
        Finset.sum_le_sum_of_subset hsubset
      _ = containedMass
          (fixedRigidCopyBodyFamily R
            (eighthNormalizedDatum source).family)
          (testBody K) := by rfl
  have hmovedKT :
      IsKatzTao C
        (fixedRigidCopyBodyFamily R
          (eighthNormalizedDatum source).family) :=
    fixedRigidCopyBodyFamily_isKatzTao R
      (eighthNormalizedDatum source).family hKT
  calc
    (normalizedRigidBodyLoadNat
        (fun u ↦ orthogonalTranslationRigidMotion
          (rotation u) (translation u))
        source testBody K g : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) =
      (hits.card : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) := by rw [hload]
    _ ≤ containedMass
        (fixedRigidCopyBodyFamily R
          (eighthNormalizedDatum source).family)
        (testBody K) := hlower
    _ ≤ C * volume (testBody K : Set Space) := hmovedKT (testBody K)

#print axioms normalizedOrthogonalTranslationBodyLoadNat_mul_halfSq_le

end
end Family8FiniteRigidMotionNormalizedBodyLoadCapScaleOnlyV1
