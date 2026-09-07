import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingAwareProjectedPhysicalLowerBucketV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open Family8ShadingAwareProjectedPhysicalV3

noncomputable section

variable {iota : Type*} {F : ConvexFamily iota}

/-!
# A genuine lower-fibre projected physical datum

The positivity carrier used by the existing shading-aware native core loses
all quantitative information about the one-dimensional fibre.  This additive
successor puts a literal lower level into the carrier itself.  Consequently,
membership in the finite projected active pattern produces the fibre lower
bound by definition; there is no conclusion-valued callback.
-/

/-- Projected physical data whose active indices have actual localized
shading-fibre mass at least `level`. -/
noncomputable def shadingAwareProjectedPhysicalLowerBucket
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal) :
    FiniteProjectedShading ProjectionSpace iota where
  ambient := active
  base := X
  carrier := fun i => X ∩
    {u | level <= shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u}
  measurable_base := hX
  measurable_carrier := by
    intro i _hi
    exact hX.inter (measurableSet_le measurable_const
      (measurable_shadingFiberMass
        (shadingWindowRestriction Y f hf X hX I hI) f hf i))

@[simp]
theorem mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (u : ProjectionSpace) (i : iota) :
    i ∈ (shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level).activeAtPoint u <->
      i ∈ active ∧ u ∈ X ∧
        level <= shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u := by
  rw [FiniteProjectedShading.mem_activeAtPoint]
  rfl

/-- Active membership itself is the quantitative lower-fibre certificate. -/
theorem shadingFiberMass_lower_of_mem_activeAtPoint
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    {u : ProjectionSpace} {i : iota}
    (hi : i ∈ (shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level).activeAtPoint u) :
    level <= shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u :=
  (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI level u i).mp hi |>.2.2

/-- For a positive level, the lower bucket is a literal sub-pattern of the
existing positivity-based projected physical datum. -/
theorem activeAtPoint_lowerBucket_subset_positive
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) {level : ENNReal}
    (hlevel : 0 < level) (u : ProjectionSpace) :
    (shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level).activeAtPoint u ⊆
      (shadingAwareProjectedPhysical Y active f hf X hX I hI).activeAtPoint u := by
  intro i hi
  have hdata :=
    (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level u i).mp hi
  apply (mem_activeAtPoint_shadingAwareProjectedPhysical
    Y active f hf X hX I hI u i).mpr
  exact ⟨hdata.1, hdata.2.1, hlevel.trans_le hdata.2.2⟩

/-- The number of lower-bucket incidences times the bucket level is bounded by
the literal projected multiplicity of the same localized shading. -/
theorem level_mul_activeAtPoint_card_le_projectedActiveMultiplicity
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (u : ProjectionSpace) :
    level * (((shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level).activeAtPoint u).card : ENNReal) <=
      projectedActiveMultiplicity
        (shadingWindowRestriction Y f hf X hX I hI) active f u := by
  classical
  let bucket := (shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI level).activeAtPoint u
  let mass : iota -> ENNReal := fun i => shadingFiberMass
    (shadingWindowRestriction Y f hf X hX I hI) f i u
  rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
    (shadingWindowRestriction Y f hf X hX I hI) active f hf u]
  change level * (bucket.card : ENNReal) <= ∑ i ∈ active, mass i
  calc
    level * (bucket.card : ENNReal) = ∑ _i ∈ bucket, level := by
      simp [mul_comm]
    _ <= ∑ i ∈ bucket, mass i := by
      exact Finset.sum_le_sum fun i hi =>
        shadingFiberMass_lower_of_mem_activeAtPoint
          Y active f hf X hX I hI level hi
    _ <= ∑ i ∈ active, mass i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact ((mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
          Y active f hf X hX I hI level u i).mp hi).1
      · intro _i _hi _hnot
        exact bot_le

#print axioms shadingAwareProjectedPhysicalLowerBucket
#print axioms mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
#print axioms shadingFiberMass_lower_of_mem_activeAtPoint
#print axioms activeAtPoint_lowerBucket_subset_positive
#print axioms level_mul_activeAtPoint_card_le_projectedActiveMultiplicity

end

end Family8ShadingAwareProjectedPhysicalLowerBucketV1
