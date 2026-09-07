import Family8Grounding.Family8CardinalCWAFrostmanInV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

/-!
# Definition 2.12 rescaled CWA supplies source Frostman control

Inside one occupied parent, John normalization sends the parent into the
unit ball and applies one common affine Jacobian to every fine tube.  The
uniform tube-volume sandwich therefore survives the normalization with the
same factor sixteen.  Cardinal CWA then gives a fixed-loss Frostman bound,
which is pulled back through the affine equivalence without determinant
loss.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Def212RescaledCWASourceFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CardinalCWAFrostmanInV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u

/-- Concentration is unchanged when both the indexed family and the test
body are sent through one affine equivalence. -/
theorem concentration_affineImageFamily_affineImageConvexBody
    {index : Type u} [Fintype index]
    (e : Space ≃ᵃ[Real] Space) (F : ConvexFamily index)
    (K : ConvexBody Space) :
    concentration (affineImageFamily e F)
        (affineImageConvexBody e K) = concentration F K := by
  rw [concentration_eq_containedMass_div,
    Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1.containedMass_affineImageFamily,
    Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1.affinePreimageConvexBody_affineImageConvexBody,
    volume_affineImageConvexBody]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos e).ne'
  · exact affineJacobian_ne_top e

namespace ScaleCover

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Rescaled-fibre CWA gives the original fibre a Frostman constant
`16 * C * vol(B(0,1))`.  The factor sixteen is only the common-radius tube
volume sandwich; it is independent of `delta` and of the fibre mass. -/
theorem isFrostmanAtScale_of_rescaledFibresCWA
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (R : UnitRescalingGeometry S)
    {C : ENNReal} (hCWA : R.FibresSatisfyCWA C) :
    S.IsFrostmanAtScale
      (C * 16 * volume (unitBallBody : Set Space)) := by
  intro k hk K hK
  let kk : {q // q ∈ S.activeCoarse} := ⟨k, hk⟩
  let e : Space ≃ᵃ[Real] Space := R.unitRescaling kk
  let F : ConvexFamily {i // i ∈ S.fiber k} := S.fiberFamily k
  let ambient : ConvexBody Space := S.coarse.tubes k |>.body
  let F' : ConvexFamily {i // i ∈ S.fiber k} :=
    affineImageFamily e F
  let ambient' : ConvexBody Space := affineImageConvexBody e ambient
  have hrescaled :
      IsFrostmanIn (C * 16 * volume (unitBallBody : Set Space))
        F' ambient' := by
    apply isFrostmanIn_of_cwa_volume_bounds
      (C := C)
      (lower := affineJacobian e * ((delta : ENNReal) ^ 2 / 2))
      (upper := affineJacobian e * (8 * (delta : ENNReal) ^ 2))
      (comparison := 16)
      (ambientVolume := volume (unitBallBody : Set Space))
    · simpa only [F', F, e, kk,
        UnitRescalingGeometry.rescaledFiberFamily] using hCWA kk
    · intro i
      change e '' (fine.tubes i.1).carrier ⊆
        e '' (S.coarse.tubes k).carrier
      exact Set.image_mono (S.fiber_carrier_subset_parent k i)
    · intro i
      change affineJacobian e * ((delta : ENNReal) ^ 2 / 2) ≤
        volume (affineImageConvexBody e (fine.tubes i.1).body : Set Space)
      rw [volume_affineImageConvexBody]
      gcongr
      exact (fine.tubes i.1).half_sq_le_volume_of_le_half hdeltaHalf
    · intro i
      change volume (affineImageConvexBody e (fine.tubes i.1).body : Set Space) ≤
        affineJacobian e * (8 * (delta : ENNReal) ^ 2)
      rw [volume_affineImageConvexBody]
      gcongr
      exact (fine.tubes i.1).volume_le_eight_mul_sq_of_le_half hdeltaHalf
    · have h16 : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
        rw [show (16 : ENNReal) = 8 * 2 by norm_num,
          mul_assoc, ENNReal.mul_inv_cancel] <;> norm_num
      rw [ENNReal.div_eq_inv_mul, ← h16]
      apply le_of_eq
      ring
    · change volume (e '' (S.coarse.tubes k).carrier) ≤
        volume (Metric.closedBall (0 : Space) 1)
      exact measure_mono (R.parent_image_subset_unitBall kk)
  have hKimage :
      (affineImageConvexBody e K : Set Space) ⊆
        (ambient' : Set Space) := by
    exact Set.image_mono hK
  have hq :=
    (isFrostmanIn_iff_concentration_le.mp hrescaled).2
      (affineImageConvexBody e K) hKimage
  change concentration (affineImageFamily e F)
      (affineImageConvexBody e K) ≤
    (C * 16 * volume (unitBallBody : Set Space)) *
      concentration (affineImageFamily e F)
        (affineImageConvexBody e ambient) at hq
  simpa only [concentration_affineImageFamily_affineImageConvexBody,
    F, ambient] using hq

end ScaleCover

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The exact-scale Definition 2.12 package already contains enough data to
produce one fixed source Frostman constant at every scale. -/
theorem ExactScaleDef212Inputs.isFrostmanAtEveryScale
    {M : StickyMultiscaleCover fine} {C : NNReal}
    (H : ExactScaleDef212Inputs M C)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    M.IsFrostmanAtEveryScale
      ((C : ENNReal) * 16 * volume (unitBallBody : Set Space)) := by
  intro rho hdelta hrho
  exact ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
    (M.cover rho hdelta hrho) hdeltaHalf
    (H.unitRescalingGeometry rho hdelta hrho)
    (H.rescaled_fibres_cwa rho hdelta hrho)

#print axioms concentration_affineImageFamily_affineImageConvexBody
#print axioms ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
#print axioms ExactScaleDef212Inputs.isFrostmanAtEveryScale

end
end Family8Def212RescaledCWASourceFrostmanV1
