import «Family4LambdaUniform»
import «Family4ExtremalConstruction»
import «CubeWeightExactRadiusMaster»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4SevenItemsMaster

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Submission.Kakeya.ConvexFactoring.CubeWeightMaster
open Submission.Kakeya.ConvexFactoring.CubeWeightExactRadiusMaster
open Family4FinalMaster
open Family4LambdaUniform
open Family4ExtremalConstruction
open Family4PublishedInputs

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

/-- Restrict the final fine shading and the independently stored coarse
shading to one common measurable region.  This is again a genuine frozen
assembly.  Its loss is exactly the old assembly loss times the spatial-slice
loss, and its fiber/outer bucket labels are unchanged. -/
def restrictAssembly {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (sliceLoss : ℕ)
    (hslice : WithinFactor sliceLoss A.refinement.shading.shadingMass
      (A.refinement.shading.restrictSet Ω hΩ).shadingMass) :
    Assembly P.asConvexFactorization Y r where
  refinement := {
    indices := A.refinement.indices
    shading := A.refinement.shading.restrictSet Ω hΩ
    carrier_subset := fun i x hx => A.refinement.carrier_subset i hx.1
    carrier_eq_empty_of_not_mem := by
      intro i hi
      rw [Shading.restrictSet_carrier, A.refinement.carrier_eq_empty_of_not_mem i hi]
      simp }
  frozenCoarse := A.frozenCoarse.restrictSet Ω hΩ
  fiberLabel := A.fiberLabel
  outerLabel := A.outerLabel
  loss := A.loss * sliceLoss
  indices_subset_fine := A.indices_subset_fine
  retained := A.retained.trans hslice
  covers := by
    intro i x hx
    exact ⟨A.covers i x hx.1, hx.2⟩
  fiber_comparable := by
    intro k hk x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hxΩ : x ∈ Ω := hxi.2
    have hxOld : x ∈ P.asConvexFactorization.fiberShadedUnion
        A.refinement.shading k :=
      Set.mem_iUnion.mpr ⟨i, hxi.1⟩
    rw [fiberMultiplicity_restrictSet, if_pos hxΩ]
    exact A.fiber_comparable k hk x hxOld
  outer_comparable := by
    intro x hx
    rw [Shading.restrictSet_shadedUnion] at hx
    rw [Shading.pointMultiplicity_restrictSet, if_pos hx.2]
    exact A.outer_comparable x hx.1

@[simp] theorem restrictAssembly_fine {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (sliceLoss : ℕ)
    (hslice : WithinFactor sliceLoss A.refinement.shading.shadingMass
      (A.refinement.shading.restrictSet Ω hΩ).shadingMass) :
    (restrictAssembly A Ω hΩ sliceLoss hslice).refinement.shading =
      A.refinement.shading.restrictSet Ω hΩ := rfl

@[simp] theorem restrictAssembly_coarse {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (sliceLoss : ℕ)
    (hslice : WithinFactor sliceLoss A.refinement.shading.shadingMass
      (A.refinement.shading.restrictSet Ω hΩ).shadingMass) :
    (restrictAssembly A Ω hΩ sliceLoss hslice).frozenCoarse =
      A.frozenCoarse.restrictSet Ω hΩ := rfl

/-- Lambda-uniformity on the active source, positivity of lambda and delta,
and the actual assembly retention imply the nonzero fine mass required by
the finite weighted-cell pigeonhole theorem. -/
theorem fineMass_toNNReal_pos_of_lambdaUniform {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r)
    (S : LambdaUniformShadingData P Y)
    (hlambda : 0 < S.lambda) (hdeltaPos : 0 < delta) :
    0 < A.refinement.shading.shadingMass.toNNReal := by
  obtain ⟨i, hi⟩ := P.fineIndices_nonempty
  have hproduct : 0 <
      S.lambda * volume (fineFamily.tubes i).carrier :=
    ENNReal.mul_pos hlambda.ne' ((fineFamily.tubes i).volume_pos hdeltaPos).ne'
  have hYi : 0 < volume (Y.carrier i) :=
    hproduct.trans_le (S.refined_lower i hi)
  have hactive : 0 <
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass := by
    unfold FrozenTubeDensityMasterPrototype.activeFineShading Shading.shadingMass
    rw [Finset.sum_pos_iff]
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, by simpa using hYi⟩
  have hmass : 0 < A.refinement.shading.shadingMass := by
    by_contra hnot
    have hz : A.refinement.shading.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have hret := A.retained
    unfold WithinFactor at hret
    rw [hz, nsmul_zero] at hret
    have hretActive :
        (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass ≤ 0 := by
      rw [Family4FrozenDensityAdapter.activeFineShading_mass_eq_restrictTo]
      exact hret
    exact (not_le_of_gt hactive) hretActive
  exact ENNReal.toNNReal_pos hmass.ne'
    (CubeWeightUniformization.shadingMass_ne_top _)

/-- One post-cell object carrying all seven conclusions.  Items 1--6 are the
literal `Conclusion` for `finalAssembly`; item 7 uses the same
`finalAssembly.refinement.shading` and the same stored
`finalAssembly.frozenCoarse`. -/
structure SevenConclusion {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r)
    (activeLoss : ℕ) (Q : ℝ≥0∞)
    (cellSliceLoss : ℕ) (weight : NNReal) : Prop where
  firstSix : Conclusion A activeLoss Q
  sliceLoss_pos : 0 < cellSliceLoss
  exactRadiusBand : ∀ x ∈ A.frozenCoarse.shadedUnion,
    (weight : ℝ≥0∞) ≤ volume (A.refinement.shading.shadedUnion ∩
      Metric.ball x (rho : ℝ)) ∧
    volume (A.refinement.shading.shadedUnion ∩ Metric.ball x (rho : ℝ)) ≤
      2000 * (weight : ℝ≥0∞)

/-- Single seven-item theorem.  All CubeWeight hypotheses are discharged from
the preceding assembly and published inputs:

* `hpoint` is the assembly's comparable-product bound (with `+1` for a
  manifestly positive natural bound);
* `hcover` is the assembly cover;
* `hpositive` follows from positive lambda, positive delta, and assembly
  retention;
* `hD` is the tautological zero lower bound, since total source retention is
  recorded more sharply in the rebuilt assembly.

The common cell restriction is applied to both fine and stored coarse
shadings, then items 1--6 are re-proved on that restricted assembly. -/
theorem exists_family4_seven_items_same_object {r : ℝ}
    (A : Assembly P.asConvexFactorization Y r)
    (S : LambdaUniformShadingData P Y)
    (E : ExtremalTubeFamily A)
    (hlambda : 0 < S.lambda)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : ℝ≥0)⁻¹)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    ∃ finalAssembly : Assembly P.asConvexFactorization Y r,
      ∃ sliceLoss : ℕ, ∃ weight : NNReal,
        SevenConclusion finalAssembly
          (fineFamily.refinement.loss * (16 * S.densityLoss))
          E.jointLoss sliceLoss weight ∧
        finalAssembly.loss = A.loss * sliceLoss := by
  have hrhoPos : 0 < rho := hdeltaPos.trans_le P.scale_le
  let region : Set Space :=
    familyUnion fineFamily.bodyFamily ∪ familyUnion coarseFamily.bodyFamily
  have hregion : MeasurableSet region :=
    (familyUnion_isCompact fineFamily.bodyFamily).measurableSet.union
      (familyUnion_isCompact coarseFamily.bodyFamily).measurableSet
  obtain ⟨C⟩ := exists_finiteFamily_halfRadius_packingCertificate
    fineFamily.bodyFamily coarseFamily.bodyFamily hrhoPos
  let K : ℕ :=
    (2 * comparableBase A.outerLabel) *
      (2 * comparableBase A.fiberLabel) + 1
  have hK : 0 < K := by simp [K]
  have hpoint : ∀ x, A.refinement.shading.pointMultiplicity x ≤ K := by
    intro x
    exact (A.pointMultiplicity_le_comparableProduct x).trans
      (Nat.le_add_right _ _)
  have hFineRegion : A.refinement.shading.shadedUnion ⊆ region := by
    intro x hx
    exact Or.inl (A.refinement.shading.shadedUnion_subset_familyUnion hx)
  have hpositive : 0 < A.refinement.shading.shadingMass.toNNReal :=
    fineMass_toNNReal_pos_of_lambdaUniform A S hlambda hdeltaPos
  obtain ⟨n, _hn, hcube⟩ :=
    exists_common_weightedPackingLevel_exactRadius
      A.refinement.shading A.frozenCoarse hregion C hrhoPos hFineRegion
      K hK hpoint hpositive A.shadedUnion_subset_frozenCoarse 0 bot_le
  dsimp only at hcube
  let cell := packingCellFin C
  let hcell := measurableSet_packingCellFin hregion C
  let mass := fun q ↦ cellMass A.refinement.shading cell hcell q
  let loc := fun q ↦ localCellVolume A.refinement.shading cell q
  let selected := (highCells mass loc K).filter fun q ↦
    cubeBucket (dominanceCutoff mass K)
      (cubeExponent (a := Fin C.centers.card) K) (loc q) = n
  let finalFine := restrictToCells A.refinement.shading cell hcell selected
  let finalCoarse := restrictToCells A.frozenCoarse cell hcell selected
  let sliceLoss := 2 * (cubeExponent (a := Fin C.centers.card) K + 1)
  let w := 2 ^ n * dominanceCutoff mass K
  rcases hcube with
    ⟨hretain, hfinalCover, _hmass, _hzero, _hcellBand, hexact⟩
  let Ω := selectedRegion cell selected
  let hΩ : MeasurableSet Ω := measurableSet_selectedRegion cell hcell selected
  have hslice : WithinFactor sliceLoss A.refinement.shading.shadingMass
      (A.refinement.shading.restrictSet Ω hΩ).shadingMass := by
    unfold WithinFactor
    simpa [sliceLoss, finalFine, restrictToCells, Ω, hΩ] using hretain
  let B := restrictAssembly A Ω hΩ sliceLoss hslice
  have hBfine : B.refinement.shading = finalFine := by
    simp [B, finalFine, restrictToCells, Ω]
  have hBcoarse : B.frozenCoarse = finalCoarse := by
    simp [B, finalCoarse, restrictToCells, Ω]
  have hjointB : Family4MinimalJoint.WZJointNormalization B E.jointLoss := by
    change Family4MinimalJoint.WZJointNormalization A E.jointLoss
    exact E.wzJointNormalization
  have hfirstSix : Conclusion B
      (fineFamily.refinement.loss * (16 * S.densityLoss)) E.jointLoss := by
    exact family4_items_one_to_six_same_object B
      (fineFamily.refinement.loss * (16 * S.densityLoss))
      (S.withinFactor_active hdeltaHalf) E.jointLoss hdeltaPos hrhoHalf
      hjointB
  refine ⟨B, sliceLoss, w, ⟨{
    firstSix := hfirstSix
    sliceLoss_pos := by simp [sliceLoss]
    exactRadiusBand := ?_ }, by rfl⟩⟩
  intro x hx
  rw [hBcoarse] at hx
  have hxband := hexact x hx
  simpa [hBfine, w] using hxband

end
end Family4SevenItemsMaster

#print axioms Family4SevenItemsMaster.restrictAssembly
#print axioms Family4SevenItemsMaster.fineMass_toNNReal_pos_of_lambdaUniform
#print axioms Family4SevenItemsMaster.exists_family4_seven_items_same_object
