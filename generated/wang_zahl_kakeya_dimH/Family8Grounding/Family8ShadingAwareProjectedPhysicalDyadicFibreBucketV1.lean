import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import Mathlib.Tactic

/-!
# A two-sided shading-fibre bucket and its weighted-mass ceiling

The carrier uses the literal half-open bucket
`level <= shadingFiberMass < 2 * level`.  Every definition keeps the same
shading, active family, twisted projection, projected window and fibre window.
Thus the weighted multiplicity and its exact-card band share all witnesses.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingAwareProjectedPhysicalDyadicFibreBucketV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

variable {iota : Type*} {F : ConvexFamily iota}

/-- Projected physical data whose active indices have localized shading-fibre
mass in `[level, 2 * level)`. -/
noncomputable def shadingAwareProjectedPhysicalDyadicFibreBucket
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
        (shadingWindowRestriction Y f hf X hX I hI) f i u ∧
      shadingFiberMass
        (shadingWindowRestriction Y f hf X hX I hI) f i u < 2 * level}
  measurable_base := hX
  measurable_carrier := by
    intro i _hi
    have hmass := measurable_shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f hf i
    exact hX.inter
      ((measurableSet_le measurable_const hmass).inter
        (measurableSet_lt hmass measurable_const))

@[simp]
theorem mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (u : ProjectionSpace) (i : iota) :
    i ∈ (shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI level).activeAtPoint u <->
      i ∈ active ∧ u ∈ X ∧
        level <= shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u ∧
        shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u <
            2 * level := by
  rw [FiniteProjectedShading.mem_activeAtPoint]
  rfl

/-- Fibre-mass-weighted multiplicity of the two-sided bucket. -/
noncomputable def dyadicFibreBucketWeightedMultiplicity
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (u : ProjectionSpace) : ENNReal :=
  ∑ i ∈ (shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI level).activeAtPoint u,
    shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u

theorem dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_card
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (u : ProjectionSpace) :
    dyadicFibreBucketWeightedMultiplicity
        Y active f hf X hX I hI level u <=
      (2 * level) *
        (((shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI level).activeAtPoint u).card : ENNReal) := by
  classical
  unfold dyadicFibreBucketWeightedMultiplicity
  calc
    (∑ i ∈ (shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI level).activeAtPoint u,
        shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u) <=
        ∑ _i ∈ (shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI level).activeAtPoint u,
            2 * level := by
      exact Finset.sum_le_sum fun i hi => le_of_lt
        ((mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI level u i).mp hi).2.2.2
    _ = (2 * level) *
        (((shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI level).activeAtPoint u).card : ENNReal) := by
      simp [mul_comm]

theorem dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_exactCard
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (card : Nat) (u : ProjectionSpace)
    (hu : u ∈ (shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI level).multiplicityBand card card) :
    dyadicFibreBucketWeightedMultiplicity
        Y active f hf X hX I hI level u <=
      (2 * level) * (card : ENNReal) := by
  have hdata :=
    (shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI level).mem_multiplicityBand.mp hu
  have hcard :
      ((shadingAwareProjectedPhysicalDyadicFibreBucket
        Y active f hf X hX I hI level).activeAtPoint u).card = card :=
    Nat.le_antisymm hdata.2.2 hdata.2.1
  simpa only [hcard] using
    dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_card
      Y active f hf X hX I hI level u

/-- Integrated fibre-mass-weighted multiplicity over `E`. -/
noncomputable def dyadicFibreBucketWeightedMass
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (E : Set ProjectionSpace) : ENNReal :=
  ∫⁻ u in E,
    dyadicFibreBucketWeightedMultiplicity
      Y active f hf X hX I hI level u
      ∂(volume : Measure ProjectionSpace)

/-- On an exact-card band, weighted mass is bounded by
`2 * level * card * volume`. -/
theorem dyadicFibreBucketWeightedMass_le_two_mul_level_mul_card_mul_volume
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (level : ENNReal)
    (card : Nat) (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E ⊆
      (shadingAwareProjectedPhysicalDyadicFibreBucket
        Y active f hf X hX I hI level).multiplicityBand card card) :
    dyadicFibreBucketWeightedMass
        Y active f hf X hX I hI level E <=
      (2 * level) * (card : ENNReal) * volume E := by
  unfold dyadicFibreBucketWeightedMass
  calc
    (∫⁻ u in E,
        dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI level u
          ∂(volume : Measure ProjectionSpace)) <=
      ∫⁻ _u in E, (2 * level) * (card : ENNReal)
          ∂(volume : Measure ProjectionSpace) := by
        exact setLIntegral_mono' hE fun u hu =>
          dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_exactCard
            Y active f hf X hX I hI level card u (hEband hu)
    _ = (2 * level) * (card : ENNReal) * volume E := by
      rw [setLIntegral_const]

#print axioms shadingAwareProjectedPhysicalDyadicFibreBucket
#print axioms
  mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
#print axioms
  dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_card
#print axioms
  dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_exactCard
#print axioms
  dyadicFibreBucketWeightedMass_le_two_mul_level_mul_card_mul_volume

end
end Family8ShadingAwareProjectedPhysicalDyadicFibreBucketV1
