import TubeSelectedFamilyRatioPrototype
import Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity

open scoped ENNReal NNReal
open MeasureTheory Set

namespace FrozenTubeDensityMasterPrototype

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity
open TubeSelectedFamilyRatioPrototype

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
def ZeroOrComparable (B n : ℕ) : Prop :=
  (B = 0 ∧ n = 0) ∨ (0 < B ∧ B ≤ n ∧ n < 2 * B)

def comparableBase (b : ℕ) : ℕ :=
  if b = 0 then 0 else 2 ^ (b - 1)


def activeFineShading
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily) :
    Shading (activeFineBodyFamily P) :=
  selectedCoarseShading Y P.fineIndices

def activeFrozenShading
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Z : Shading coarseFamily.bodyFamily) :
    Shading (activeCoarseBodyFamily P) :=
  selectedCoarseShading Z P.coarseIndices

/-- Minimal paper-facing data: the coarse shading is stored independently,
and all conclusions refer to this same `frozenCoarse`. -/
structure Assembly
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily) where
  refinement : IndexedShadingRefinement Y
  frozenCoarse : Shading coarseFamily.bodyFamily
  loss : ℕ
  fiberBound : ℕ
  outerLabel : ℕ
  indices_subset_fine : refinement.indices ⊆ P.fineIndices
  retained : WithinFactor loss (activeFineShading P Y).shadingMass
    refinement.shading.shadingMass
  covers : ∀ i x, x ∈ refinement.shading.carrier i →
    x ∈ frozenCoarse.carrier (P.index.parent i)
  fiber_bound : ∀ k ∈ P.coarseIndices, ∀ x ∈
      P.asConvexFactorization.fiberShadedUnion refinement.shading k,
    P.asConvexFactorization.fiberMultiplicity refinement.shading k x ≤
      fiberBound
  outer_comparable : ∀ x ∈ frozenCoarse.shadedUnion,
    ZeroOrComparable (comparableBase outerLabel)
      (frozenCoarse.pointMultiplicity x)

namespace Assembly

variable {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

theorem fiberUnion_subset_actualFrozenCarrier
    (A : Assembly P Y) (k : κ) :
    P.asConvexFactorization.fiberShadedUnion A.refinement.shading k ⊆
      A.frozenCoarse.carrier k := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  have hp : P.index.parent i.1 = k :=
    (P.mem_fiber i.1 k).1 i.2 |>.2
  simpa [hp] using A.covers i.1 x hxi

theorem fiberMass_le_actualFrozenCarrier
    (A : Assembly P Y) (k : κ) (hk : k ∈ P.coarseIndices) :
    InducedShadingDensityAlgebra.fiberShadingMass P.asConvexFactorization A.refinement.shading k ≤
      A.fiberBound • volume (A.frozenCoarse.carrier k) := by
  calc
    InducedShadingDensityAlgebra.fiberShadingMass P.asConvexFactorization A.refinement.shading k ≤
        A.fiberBound • volume
          (P.asConvexFactorization.fiberShadedUnion A.refinement.shading k) :=
      fiberShadingMass_le_nsmul_volume_fiberShadedUnion
        P.asConvexFactorization A.refinement.shading k A.fiberBound
          (A.fiber_bound k hk)
    _ ≤ A.fiberBound • volume (A.frozenCoarse.carrier k) :=
      nsmul_le_nsmul_right
        (measure_mono (A.fiberUnion_subset_actualFrozenCarrier k)) _

/-- The final fine mass is controlled by the active reindexing of the same
stored frozen shading.  No neighborhood shading is recomputed. -/
theorem refinementMass_le_fiberBound_mul_activeFrozenMass
    (A : Assembly P Y) :
    A.refinement.shading.shadingMass ≤
      A.fiberBound • (activeFrozenShading P A.frozenCoarse).shadingMass := by
  rw [refinement_shadingMass_eq_sum_fiberShadingMass
    P.asConvexFactorization A.refinement A.indices_subset_fine]
  unfold activeFrozenShading activeCoarseBodyFamily
  rw [selectedCoarseShading_mass]
  calc
    (∑ k ∈ P.coarseIndices,
      InducedShadingDensityAlgebra.fiberShadingMass
        P.asConvexFactorization A.refinement.shading k) ≤
        ∑ k ∈ P.coarseIndices,
          A.fiberBound • volume (A.frozenCoarse.carrier k) :=
      Finset.sum_le_sum fun k hk => A.fiberMass_le_actualFrozenCarrier k hk
    _ = A.fiberBound • ∑ k ∈ P.coarseIndices,
        volume (A.frozenCoarse.carrier k) := by
      simp only [nsmul_eq_mul, Finset.mul_sum]

theorem activeSourceMass_le_loss_mul_activeFrozenMass
    (A : Assembly P Y) :
    (activeFineShading P Y).shadingMass ≤
      (A.loss * A.fiberBound) •
        (activeFrozenShading P A.frozenCoarse).shadingMass := by
  calc
    (activeFineShading P Y).shadingMass ≤
        A.loss • A.refinement.shading.shadingMass := A.retained
    _ ≤ A.loss •
        (A.fiberBound •
          (activeFrozenShading P A.frozenCoarse).shadingMass) :=
      nsmul_le_nsmul_right
        A.refinementMass_le_fiberBound_mul_activeFrozenMass _
    _ = (A.loss * A.fiberBound) •
        (activeFrozenShading P A.frozenCoarse).shadingMass := by
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ac_rfl

theorem activeFineFamilyVolume_pos
    (P : CoarseTubePartition fineFamily coarseFamily)
    (hdeltaPos : 0 < delta) :
    0 < familyVolume (activeFineBodyFamily P) := by
  rw [activeFineBodyFamily, selectedCoarseFamily_volume, Finset.sum_pos_iff]
  obtain ⟨i, hi⟩ := P.fineIndices_nonempty
  refine ⟨i, hi, ?_⟩
  simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
    (fineFamily.tubes i).volume_pos hdeltaPos

theorem density_le_of_mass_and_denominator
    (A : Assembly P Y) (C : ℝ≥0∞)
    (hdeltaPos : 0 < delta)
    (hden : familyVolume (activeCoarseBodyFamily P) ≤
      C * familyVolume (activeFineBodyFamily P)) :
    (activeFineShading P Y).shadingDensity ≤
      ((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) * C *
        (activeFrozenShading P A.frozenCoarse).shadingDensity := by
  have hF0 : familyVolume (activeFineBodyFamily P) ≠ 0 :=
    (activeFineFamilyVolume_pos P hdeltaPos).ne'
  apply (ENNReal.mul_le_mul_iff_left hF0
    (familyVolume_ne_top (activeFineBodyFamily P))).mp
  calc
    (activeFineShading P Y).shadingDensity *
        familyVolume (activeFineBodyFamily P) =
      (activeFineShading P Y).shadingMass :=
        shadingDensity_mul_familyVolume _
    _ ≤ (A.loss * A.fiberBound) •
        (activeFrozenShading P A.frozenCoarse).shadingMass :=
      A.activeSourceMass_le_loss_mul_activeFrozenMass
    _ = (A.loss * A.fiberBound) •
        ((activeFrozenShading P A.frozenCoarse).shadingDensity *
          familyVolume (activeCoarseBodyFamily P)) := by
      rw [shadingDensity_mul_familyVolume]
    _ ≤ (A.loss * A.fiberBound) •
        ((activeFrozenShading P A.frozenCoarse).shadingDensity *
          (C * familyVolume (activeFineBodyFamily P))) :=
      nsmul_le_nsmul_right (mul_le_mul' le_rfl hden) _
    _ = (((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) * C *
        (activeFrozenShading P A.frozenCoarse).shadingDensity) *
          familyVolume (activeFineBodyFamily P) := by
      simp only [nsmul_eq_mul]
      push_cast
      ac_rfl

/-- Item 2(a): explicit tube denominator loss for the same frozen `Z`. -/
theorem density_lower_explicitCtube
    (A : Assembly P Y) (hdeltaPos : 0 < delta)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    (activeFineShading P Y).shadingDensity ≤
      ((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) *
        tubeDenominatorLoss P *
          (activeFrozenShading P A.frozenCoarse).shadingDensity ∧
      (∀ x ∈ A.frozenCoarse.shadedUnion,
        ZeroOrComparable (comparableBase A.outerLabel)
          (A.frozenCoarse.pointMultiplicity x)) := by
  refine ⟨A.density_le_of_mass_and_denominator
    (tubeDenominatorLoss P) hdeltaPos
      (activeCoarseVolume_le_tubeDenominatorLoss_mul
        P hdeltaPos hrhoHalf), A.outer_comparable⟩

theorem tubeDenominatorLoss_le_of_branchingNormalization
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Q : ℝ≥0∞) (hdeltaPos : 0 < delta)
    (hnorm : (rho : ℝ≥0∞) ^ 2 ≤
      Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :
    tubeDenominatorLoss P ≤ 16 * (P.branchingLoss : ℝ≥0∞) * Q := by
  have hbranch0 : (P.branching : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast P.branching_pos.ne'
  have hdelta0 : (delta : ℝ≥0∞) ^ 2 ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.coe_ne_zero.mpr hdeltaPos.ne') 2
  have hden0 :
      (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 ≠ 0 :=
    mul_ne_zero hbranch0 hdelta0
  have hdenTop :
      (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  unfold tubeDenominatorLoss
  apply (ENNReal.div_le_iff hden0 hdenTop).2
  calc
    16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 ≤
        16 * (P.branchingLoss : ℝ≥0∞) *
          (Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :=
      mul_le_mul' le_rfl hnorm
    _ = (16 * (P.branchingLoss : ℝ≥0∞) * Q) *
        ((P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) := by
      ac_rfl

/-- Correct consequence of `rho^2 ≤ Q B delta^2`: the fiber bound remains. -/
theorem density_lower_of_branchingNormalization
    (A : Assembly P Y) (Q : ℝ≥0∞)
    (hdeltaPos : 0 < delta) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    (hnorm : (rho : ℝ≥0∞) ^ 2 ≤
      Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :
    (activeFineShading P Y).shadingDensity ≤
      ((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) *
        (16 * (P.branchingLoss : ℝ≥0∞) * Q) *
          (activeFrozenShading P A.frozenCoarse).shadingDensity := by
  calc
    (activeFineShading P Y).shadingDensity ≤
        ((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) *
          tubeDenominatorLoss P *
            (activeFrozenShading P A.frozenCoarse).shadingDensity :=
      (A.density_lower_explicitCtube hdeltaPos hrhoHalf).1
    _ ≤ ((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) *
        (16 * (P.branchingLoss : ℝ≥0∞) * Q) *
          (activeFrozenShading P A.frozenCoarse).shadingDensity :=
      mul_le_mul' (mul_le_mul' le_rfl
        (tubeDenominatorLoss_le_of_branchingNormalization
          P Q hdeltaPos hnorm)) le_rfl


/-- The paper-normalized coefficient: fiber overlap and scale are controlled
together, exactly matching the denominator `branching * delta^2`. -/
theorem fiberBound_mul_tubeDenominatorLoss_le_of_jointNormalization
    (A : Assembly P Y) (Q : ℝ≥0∞) (hdeltaPos : 0 < delta)
    (hjoint : (rho : ℝ≥0∞) ^ 2 * (A.fiberBound : ℝ≥0∞) ≤
      Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :
    (A.fiberBound : ℝ≥0∞) * tubeDenominatorLoss P ≤
      16 * (P.branchingLoss : ℝ≥0∞) * Q := by
  have hbranch0 : (P.branching : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast P.branching_pos.ne'
  have hdelta0 : (delta : ℝ≥0∞) ^ 2 ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.coe_ne_zero.mpr hdeltaPos.ne') 2
  have hden0 :
      (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 ≠ 0 :=
    mul_ne_zero hbranch0 hdelta0
  have hdenTop :
      (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  rw [show (A.fiberBound : ℝ≥0∞) * tubeDenominatorLoss P =
      (16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
        (A.fiberBound : ℝ≥0∞)) /
          ((P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) by
    unfold tubeDenominatorLoss
    simp only [div_eq_mul_inv]
    ac_rfl]
  apply (ENNReal.div_le_iff hden0 hdenTop).2
  calc
    16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
        (A.fiberBound : ℝ≥0∞) =
      16 * (P.branchingLoss : ℝ≥0∞) *
        ((rho : ℝ≥0∞) ^ 2 * (A.fiberBound : ℝ≥0∞)) := by ac_rfl
    _ ≤ 16 * (P.branchingLoss : ℝ≥0∞) *
        (Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :=
      mul_le_mul' le_rfl hjoint
    _ = (16 * (P.branchingLoss : ℝ≥0∞) * Q) *
        ((P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) := by
      ac_rfl

/-- Paper item 2 under the genuine joint branching/overlap normalization.
The conclusion concerns the same stored frozen shading and retains its actual
outer-comparability certificate. -/
theorem density_lower_of_jointNormalization
    (A : Assembly P Y) (Q : ℝ≥0∞)
    (hdeltaPos : 0 < delta) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    (hjoint : (rho : ℝ≥0∞) ^ 2 * (A.fiberBound : ℝ≥0∞) ≤
      Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :
    (activeFineShading P Y).shadingDensity ≤
      16 * (A.loss : ℝ≥0∞) * (P.branchingLoss : ℝ≥0∞) * Q *
        (activeFrozenShading P A.frozenCoarse).shadingDensity ∧
      (∀ x ∈ A.frozenCoarse.shadedUnion,
        ZeroOrComparable (comparableBase A.outerLabel)
          (A.frozenCoarse.pointMultiplicity x)) := by
  refine ⟨?_, A.outer_comparable⟩
  calc
    (activeFineShading P Y).shadingDensity ≤
        ((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) *
          tubeDenominatorLoss P *
            (activeFrozenShading P A.frozenCoarse).shadingDensity :=
      (A.density_lower_explicitCtube hdeltaPos hrhoHalf).1
    _ = (A.loss : ℝ≥0∞) *
        ((A.fiberBound : ℝ≥0∞) * tubeDenominatorLoss P) *
          (activeFrozenShading P A.frozenCoarse).shadingDensity := by
      push_cast
      ac_rfl
    _ ≤ (A.loss : ℝ≥0∞) *
        (16 * (P.branchingLoss : ℝ≥0∞) * Q) *
          (activeFrozenShading P A.frozenCoarse).shadingDensity :=
      mul_le_mul' (mul_le_mul' le_rfl
        (A.fiberBound_mul_tubeDenominatorLoss_le_of_jointNormalization
          Q hdeltaPos hjoint)) le_rfl
    _ = 16 * (A.loss : ℝ≥0∞) *
        (P.branchingLoss : ℝ≥0∞) * Q *
          (activeFrozenShading P A.frozenCoarse).shadingDensity := by
      ac_rfl
/-- Item 2(b), with the minimal additional overlap input needed to remove
`fiberBound`: `fiberBound ≤ branchingLoss`. -/
theorem density_lower_sixteen_loss_branchingLoss_sq
    (A : Assembly P Y) (Q : ℝ≥0∞)
    (hdeltaPos : 0 < delta) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    (hnorm : (rho : ℝ≥0∞) ^ 2 ≤
      Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2)
    (hfiber : A.fiberBound ≤ P.branchingLoss) :
    (activeFineShading P Y).shadingDensity ≤
      16 * (A.loss : ℝ≥0∞) * (P.branchingLoss : ℝ≥0∞) ^ 2 * Q *
        (activeFrozenShading P A.frozenCoarse).shadingDensity ∧
      (∀ x ∈ A.frozenCoarse.shadedUnion,
        ZeroOrComparable (comparableBase A.outerLabel)
          (A.frozenCoarse.pointMultiplicity x)) := by
  refine ⟨?_, A.outer_comparable⟩
  calc
    (activeFineShading P Y).shadingDensity ≤
        ((A.loss * A.fiberBound : ℕ) : ℝ≥0∞) *
          (16 * (P.branchingLoss : ℝ≥0∞) * Q) *
            (activeFrozenShading P A.frozenCoarse).shadingDensity :=
      A.density_lower_of_branchingNormalization Q hdeltaPos hrhoHalf hnorm
    _ ≤ ((A.loss * P.branchingLoss : ℕ) : ℝ≥0∞) *
          (16 * (P.branchingLoss : ℝ≥0∞) * Q) *
            (activeFrozenShading P A.frozenCoarse).shadingDensity := by
      apply mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      exact_mod_cast Nat.mul_le_mul_left A.loss hfiber
    _ = 16 * (A.loss : ℝ≥0∞) *
        (P.branchingLoss : ℝ≥0∞) ^ 2 * Q *
          (activeFrozenShading P A.frozenCoarse).shadingDensity := by
      push_cast
      rw [pow_two]
      ac_rfl

end Assembly
end
end FrozenTubeDensityMasterPrototype

#print axioms FrozenTubeDensityMasterPrototype.Assembly.density_lower_explicitCtube
#print axioms FrozenTubeDensityMasterPrototype.Assembly.density_lower_of_branchingNormalization
#print axioms FrozenTubeDensityMasterPrototype.Assembly.density_lower_of_jointNormalization
#print axioms FrozenTubeDensityMasterPrototype.Assembly.density_lower_sixteen_loss_branchingLoss_sq
