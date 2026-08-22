import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Submission.Kakeya.ConvexFactoring.TubeSpecificLocalGrowth
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Submission.Kakeya.ConvexFactoring.NeighborhoodInducedShading

/-!
# Tube-parent induced density assembly

This module combines the tube-specific G2--G4 packing estimate with a genuine
dense witness in each selected parent fiber.  It proves a local parent
inequality, sums it on the selected coarse subtype, and then divides by the
positive finite selected family volume to obtain a density bound.

The argument does not assume the local parent inequality.  It chooses the fine
witness supplied by `HasDenseFiberWitness`, invokes the actual tube packing
theorem, and uses the explicit tube-volume comparison at radii at most one
half.  This remains a parent-level assembly; no further global refinement or
mass-retention conclusion is asserted here.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open HeavyParentSelection

noncomputable section

namespace TubeParentInducedDensity

variable {delta rho : NNReal} {ι κ : Type*}
  [DecidableEq ι] [DecidableEq κ]
variable {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}

/-- A selected dense witness gives the explicit parent inequality after the
tube-specific G4 estimate and tube-volume comparison. -/
theorem parent_volume_le_neighborhoodCarrier
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily)
    (parents : Finset κ) (lambda loss : ℝ≥0∞)
    (hwitness : HasDenseFiberWitness P.asConvexFactorization Y
      parents lambda loss)
    (hdeltaPos : 0 < delta) (hrhoPos : 0 < rho)
    (hscale : delta ≤ rho) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    {k : κ} (hk : k ∈ parents) :
    lambda * volume (coarseFamily.tubes k).carrier ≤
      768 * loss *
        volume ((P.asConvexFactorization.neighborhoodInducedShading
          Y (rho : ℝ)).carrier k) := by
  obtain ⟨i, hiFiber, hiDense⟩ := hwitness k hk
  change i ∈ P.index.fiber k at hiFiber
  change lambda * volume (fineFamily.tubes i).carrier ≤
    loss * volume (Y.carrier i) at hiDense
  have hiFine : i ∈ P.index.fine :=
    P.index.fiber_subset_fine k hiFiber
  have hiParent : P.index.parent i = k :=
    (P.index.mem_fiber i k).1 hiFiber |>.2
  have hAfine : Y.carrier i ⊆ (fineFamily.tubes i).carrier := by
    intro x hx
    exact Y.carrier_subset i hx
  have hAcoarse : Y.carrier i ⊆ (coarseFamily.tubes k).carrier := by
    intro x hx
    have hx' := P.carrier_subset i hiFine (Y.carrier_subset i hx)
    simpa [hiParent] using hx'
  obtain ⟨_packing, _hcapture, hg4⟩ :=
    exists_packingCertificate_with_explicit_tubeCrossGrowth
      (A := Y.carrier i) (fineFamily.tubes i) (coarseFamily.tubes k)
      hAfine hAcoarse hdeltaPos hrhoPos hscale
  have hpieceFiber :
      Y.carrier i ⊆ P.asConvexFactorization.fiberShadedUnion Y k := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨i, hiFiber⟩, hx⟩
  have hlocalSubset :
      (coarseFamily.tubes k).carrier ∩
          Metric.thickening (rho : ℝ) (Y.carrier i) ⊆
        (P.asConvexFactorization.neighborhoodInducedShading
          Y (rho : ℝ)).carrier k := by
    intro x hx
    exact ⟨hx.1,
      Metric.thickening_subset_of_subset (rho : ℝ) hpieceFiber hx.2⟩
  have hgrowth :
      volume (Y.carrier i) * (rho : ℝ≥0∞) ^ 2 ≤
        48 * (delta : ℝ≥0∞) ^ 2 *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k) := by
    exact hg4.trans
      (mul_le_mul_of_nonneg_left (measure_mono hlocalSubset) bot_le)
  have hdeltaHalf : delta ≤ (2 : ℝ≥0)⁻¹ :=
    hscale.trans hrhoHalf
  have hfineLower :=
    (fineFamily.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
  rw [ENNReal.div_eq_inv_mul] at hfineLower
  have hlambdaFine :
      lambda * ((2 : ℝ≥0∞)⁻¹ * (delta : ℝ≥0∞) ^ 2) ≤
        loss * volume (Y.carrier i) :=
    (mul_le_mul_of_nonneg_left hfineLower bot_le).trans hiDense
  have hbeforeTwo :
      (lambda * ((2 : ℝ≥0∞)⁻¹ * (delta : ℝ≥0∞) ^ 2)) *
          (rho : ℝ≥0∞) ^ 2 ≤
        loss * (48 * (delta : ℝ≥0∞) ^ 2 *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k)) := by
    calc
      (lambda * ((2 : ℝ≥0∞)⁻¹ * (delta : ℝ≥0∞) ^ 2)) *
          (rho : ℝ≥0∞) ^ 2 ≤
          (loss * volume (Y.carrier i)) * (rho : ℝ≥0∞) ^ 2 :=
        mul_le_mul_of_nonneg_right hlambdaFine bot_le
      _ = loss * (volume (Y.carrier i) * (rho : ℝ≥0∞) ^ 2) := by
        ac_rfl
      _ ≤ loss * (48 * (delta : ℝ≥0∞) ^ 2 *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k)) :=
        mul_le_mul_of_nonneg_left hgrowth bot_le
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hmulTwo := mul_le_mul_of_nonneg_right hbeforeTwo
    (show (0 : ℝ≥0∞) ≤ 2 by exact bot_le)
  have hdeltaFactored :
      (lambda * (rho : ℝ≥0∞) ^ 2) * (delta : ℝ≥0∞) ^ 2 ≤
        (96 * loss *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k)) * (delta : ℝ≥0∞) ^ 2 := by
    calc
      (lambda * (rho : ℝ≥0∞) ^ 2) * (delta : ℝ≥0∞) ^ 2 =
          ((lambda * ((2 : ℝ≥0∞)⁻¹ * (delta : ℝ≥0∞) ^ 2)) *
            (rho : ℝ≥0∞) ^ 2) * 2 := by
        calc
          (lambda * (rho : ℝ≥0∞) ^ 2) * (delta : ℝ≥0∞) ^ 2 =
              (lambda * (rho : ℝ≥0∞) ^ 2) *
                (delta : ℝ≥0∞) ^ 2 * ((2 : ℝ≥0∞)⁻¹ * 2) := by
            rw [htwo, mul_one]
          _ = _ := by ring
      _ ≤ (loss * (48 * (delta : ℝ≥0∞) ^ 2 *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k))) * 2 := hmulTwo
      _ = (96 * loss *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k)) * (delta : ℝ≥0∞) ^ 2 := by
        ring
  have hdelta0 : (delta : ℝ≥0∞) ^ 2 ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.coe_ne_zero.mpr hdeltaPos.ne') 2
  have hdeltaTop : (delta : ℝ≥0∞) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hdeltaCancel :
      (delta : ℝ≥0∞) ^ 2 * ((delta : ℝ≥0∞) ^ 2)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hdelta0 hdeltaTop
  have hlambdaRho :
      lambda * (rho : ℝ≥0∞) ^ 2 ≤
        96 * loss *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k) := by
    calc
      lambda * (rho : ℝ≥0∞) ^ 2 =
          ((lambda * (rho : ℝ≥0∞) ^ 2) * (delta : ℝ≥0∞) ^ 2) *
            ((delta : ℝ≥0∞) ^ 2)⁻¹ := by
        rw [mul_assoc, hdeltaCancel, mul_one]
      _ ≤ ((96 * loss *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k)) * (delta : ℝ≥0∞) ^ 2) *
              ((delta : ℝ≥0∞) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hdeltaFactored bot_le
      _ = 96 * loss *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Y (rho : ℝ)).carrier k) := by
        rw [mul_assoc, hdeltaCancel, mul_one]
  have hcoarseUpper :=
    (coarseFamily.tubes k).volume_le_eight_mul_sq_of_le_half hrhoHalf
  calc
    lambda * volume (coarseFamily.tubes k).carrier ≤
        lambda * (8 * (rho : ℝ≥0∞) ^ 2) :=
      mul_le_mul_of_nonneg_left hcoarseUpper bot_le
    _ = 8 * (lambda * (rho : ℝ≥0∞) ^ 2) := by ring
    _ ≤ 8 * (96 * loss *
        volume ((P.asConvexFactorization.neighborhoodInducedShading
          Y (rho : ℝ)).carrier k)) :=
      mul_le_mul_of_nonneg_left hlambdaRho bot_le
    _ = 768 * loss *
        volume ((P.asConvexFactorization.neighborhoodInducedShading
          Y (rho : ℝ)).carrier k) := by ring

/-- Summing the genuine parent inequalities gives the selected active subtype
mass inequality. -/
theorem selected_familyVolume_le_neighborhoodShadingMass
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily)
    (parents : Finset κ) (lambda loss : ℝ≥0∞)
    (hwitness : HasDenseFiberWitness P.asConvexFactorization Y
      parents lambda loss)
    (hdeltaPos : 0 < delta) (hrhoPos : 0 < rho)
    (hscale : delta ≤ rho) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    lambda *
        familyVolume (selectedCoarseFamily coarseFamily.bodyFamily parents) ≤
      (768 * loss) *
        (selectedCoarseShading
          (P.asConvexFactorization.neighborhoodInducedShading Y (rho : ℝ))
          parents).shadingMass := by
  rw [selectedCoarseFamily_volume, selectedCoarseShading_mass,
    Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk => by
    simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      parent_volume_le_neighborhoodCarrier
        P Y parents lambda loss hwitness hdeltaPos hrhoPos
          hscale hrhoHalf hk

/-- A nonempty selected subtype has positive coarse family volume, so the
summed cross inequality yields an actual density comparison. -/
theorem lambda_le_selected_neighborhoodDensity
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily)
    (parents : Finset κ) (hparents : parents.Nonempty)
    (lambda loss : ℝ≥0∞)
    (hwitness : HasDenseFiberWitness P.asConvexFactorization Y
      parents lambda loss)
    (hdeltaPos : 0 < delta) (hrhoPos : 0 < rho)
    (hscale : delta ≤ rho) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    lambda ≤ (768 * loss) *
      (selectedCoarseShading
        (P.asConvexFactorization.neighborhoodInducedShading Y (rho : ℝ))
        parents).shadingDensity := by
  let Wsel := selectedCoarseFamily coarseFamily.bodyFamily parents
  let Zsel := selectedCoarseShading
    (P.asConvexFactorization.neighborhoodInducedShading Y (rho : ℝ)) parents
  have hcross : lambda * familyVolume Wsel ≤
      (768 * loss) * Zsel.shadingMass := by
    exact selected_familyVolume_le_neighborhoodShadingMass
      P Y parents lambda loss hwitness hdeltaPos hrhoPos hscale hrhoHalf
  have hvolumePos : 0 < familyVolume Wsel := by
    rw [show familyVolume Wsel =
        ∑ k ∈ parents, volume (coarseFamily.bodyFamily k : Set Space) by
      exact selectedCoarseFamily_volume coarseFamily.bodyFamily parents]
    rw [Finset.sum_pos_iff]
    obtain ⟨k, hk⟩ := hparents
    exact ⟨k, hk, by
      simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
        (coarseFamily.tubes k).volume_pos hrhoPos⟩
  have hvolume0 : familyVolume Wsel ≠ 0 := hvolumePos.ne'
  have hvolumeTop : familyVolume Wsel ≠ ∞ := familyVolume_ne_top Wsel
  calc
    lambda ≤ ((768 * loss) * Zsel.shadingMass) / familyVolume Wsel :=
      (ENNReal.le_div_iff_mul_le
        (Or.inl hvolume0) (Or.inl hvolumeTop)).2 hcross
    _ = (768 * loss) * Zsel.shadingDensity := by
      unfold Shading.shadingDensity
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Safe quotient form of the selected subtype density conclusion. -/
theorem lambda_div_loss_le_selected_neighborhoodDensity
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily)
    (parents : Finset κ) (hparents : parents.Nonempty)
    (lambda loss : ℝ≥0∞)
    (hwitness : HasDenseFiberWitness P.asConvexFactorization Y
      parents lambda loss)
    (hdeltaPos : 0 < delta) (hrhoPos : 0 < rho)
    (hscale : delta ≤ rho) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    lambda / (768 * loss) ≤
      (selectedCoarseShading
        (P.asConvexFactorization.neighborhoodInducedShading Y (rho : ℝ))
        parents).shadingDensity := by
  apply ENNReal.div_le_of_le_mul'
  exact lambda_le_selected_neighborhoodDensity
    P Y parents hparents lambda loss hwitness
      hdeltaPos hrhoPos hscale hrhoHalf

/-- The coarse-tube partition's occupied-fiber certificate discharges the
nonempty-fiber premise in the uniform dense-witness constructor. -/
theorem hasDenseFiberWitness_on_active_of_uniform
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily) (lambda : ℝ≥0∞)
    (huniform : ∀ i ∈ P.fineIndices,
      lambda * volume (fineFamily.tubes i).carrier ≤ volume (Y.carrier i)) :
    HasDenseFiberWitness P.asConvexFactorization Y
      P.coarseIndices lambda 1 := by
  apply hasDenseFiberWitness_of_uniform
  · intro k hk
    change (P.fiber k).Nonempty
    exact P.fiber_nonempty hk
  · intro i hi
    change i ∈ P.fineIndices at hi
    change lambda * volume (fineFamily.tubes i).carrier ≤ volume (Y.carrier i)
    exact huniform i hi

/-- The same occupied-fiber certificate discharges the fiber premise in the
heavy-parent witness theorem. -/
theorem heavyParents_haveDenseFiberWitness
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily) (lambda L : ℝ≥0∞) :
    HasDenseFiberWitness P.asConvexFactorization Y
      (heavyParents P.asConvexFactorization Y lambda L) lambda (2 * L) := by
  apply heavyParents_hasDenseFiberWitness
  intro k hk
  change k ∈ P.coarseIndices at hk
  change (P.fiber k).Nonempty
  exact P.fiber_nonempty hk

end TubeParentInducedDensity

end

end Submission.Kakeya.ConvexFactoring
