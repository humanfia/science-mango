import «Family4MinimalJoint»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4SourceDensity

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open TubeSelectedFamilyRatioPrototype
open Family4FrozenDensityAdapter
open Family4MinimalJoint

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

theorem activeFineFamilyVolume_le_full :
    familyVolume (activeFineBodyFamily P) ≤
      familyVolume fineFamily.bodyFamily := by
  rw [activeFineBodyFamily, HeavyParentSelection.selectedCoarseFamily_volume, familyVolume]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => bot_le)

/-- Mass retention through the active index set also controls density: the
active family has no larger denominator than the full source family. -/
theorem sourceDensity_le_activeLoss_mul
    (activeLoss : ℕ)
    (hactive : WithinFactor activeLoss Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass)
    (hdeltaPos : 0 < delta) :
    Y.shadingDensity ≤ (activeLoss : ℝ≥0∞) *
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity := by
  have hfull0 : familyVolume fineFamily.bodyFamily ≠ 0 :=
    (((FrozenTubeDensityMasterPrototype.Assembly.activeFineFamilyVolume_pos P hdeltaPos).trans_le
      activeFineFamilyVolume_le_full)).ne'
  apply (ENNReal.mul_le_mul_iff_left hfull0
    (familyVolume_ne_top fineFamily.bodyFamily)).mp
  calc
    Y.shadingDensity * familyVolume fineFamily.bodyFamily = Y.shadingMass :=
      InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume _
    _ ≤ activeLoss •
        (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass :=
      hactive
    _ = activeLoss •
        ((FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity *
          familyVolume (activeFineBodyFamily P)) := by
      rw [InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume]
    _ ≤ activeLoss •
        ((FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity *
          familyVolume fineFamily.bodyFamily) :=
      nsmul_le_nsmul_right (mul_le_mul' le_rfl activeFineFamilyVolume_le_full) _
    _ = ((activeLoss : ℝ≥0∞) *
        (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity) *
          familyVolume fineFamily.bodyFamily := by
      simp only [nsmul_eq_mul]
      ac_rfl

/-- Source-to-active retention plus the minimal joint normalization gives the
density lower bound for the literal same stored `frozenCoarse`. -/
theorem sourceDensity_lower_sameFrozen {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r)
    (activeLoss : ℕ)
    (hactive : WithinFactor activeLoss Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass)
    (Q : ℝ≥0∞) (hdeltaPos : 0 < delta)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    (hjoint : WZJointNormalization A Q) :
    Y.shadingDensity ≤
      (activeLoss : ℝ≥0∞) *
        (16 * ((ofFrozenNeighborhoodAssembly A).loss : ℝ≥0∞) *
          (P.branchingLoss : ℝ≥0∞) * Q) *
        (FrozenTubeDensityMasterPrototype.activeFrozenShading P
          (ofFrozenNeighborhoodAssembly A).frozenCoarse).shadingDensity := by
  calc
    Y.shadingDensity ≤ (activeLoss : ℝ≥0∞) *
        (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity :=
      sourceDensity_le_activeLoss_mul activeLoss hactive hdeltaPos
    _ ≤ (activeLoss : ℝ≥0∞) *
        (16 * ((ofFrozenNeighborhoodAssembly A).loss : ℝ≥0∞) *
          (P.branchingLoss : ℝ≥0∞) * Q *
          (FrozenTubeDensityMasterPrototype.activeFrozenShading P
            (ofFrozenNeighborhoodAssembly A).frozenCoarse).shadingDensity) :=
      mul_le_mul' le_rfl
        ((family4_items_one_to_six A activeLoss hactive Q hdeltaPos
          hrhoHalf hjoint).2.2.2.2.2)
    _ = _ := by ac_rfl

end
end Family4SourceDensity

#print axioms Family4SourceDensity.sourceDensity_le_activeLoss_mul
#print axioms Family4SourceDensity.sourceDensity_lower_sameFrozen
