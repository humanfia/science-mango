import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardV1
import Family8Grounding.Family8CanonicalGraphFrozenZeroFibreMassCapV1
import Mathlib.Tactic

/-!
# Same-graph ceiling for an explicit high-fibre exact-card band

On the literal zero/full-window canonical graph every fibre mass is at most
two.  After the explicit high truncation has selected a region with exactly
`p` active high fibres, its high weighted density is therefore at most
`2 * p`.  Integration gives the required planar-volume ceiling without
returning to the untruncated projected source mass.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardCeilingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardV1
open Family8CanonicalGraphFrozenLowFibreWeightedTailV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CanonicalGraphFrozenZeroFibreMassCapV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u

variable {iota : Type u} [DecidableEq iota]
variable {G : ConvexFamily iota}

/-- The explicit high density is exactly the fibre-mass sum over the active
set of the matching positive-lower projected physical datum. -/
theorem highFibreWeightedMultiplicity_eq_sum_positiveLower_activeAtPoint
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal)
    (u : ProjectionSpace) :
    highFibreWeightedMultiplicity Y active f level u =
      ∑ i ∈ (positiveLowerFibreProjectedPhysical
          Y active f hf level).activeAtPoint u,
        shadingFiberMass Y f i u := by
  classical
  have hactive :
      (positiveLowerFibreProjectedPhysical
        Y active f hf level).activeAtPoint u =
        active.filter fun i ↦
          0 < shadingFiberMass Y f i u ∧
            level ≤ shadingFiberMass Y f i u := by
    ext i
    simp only [Finset.mem_filter,
      mem_activeAtPoint_positiveLowerFibreProjectedPhysical]
  rw [hactive]
  unfold highFibreWeightedMultiplicity
  rw [Finset.sum_filter]

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Pointwise ceiling on one exact-card high-fibre band of the same frozen
canonical graph. -/
theorem sameGraph_zeroWindow_highFibreWeightedMultiplicity_le_two_mul_card
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (level : ENNReal) (p : Nat) (u : ProjectionSpace)
    (hu :
      let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
      let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        VS R.label
      let Z := firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k
      let f0 : Real → Real := fun _ ↦ 0
      let Yw := shadingWindowRestriction Z f0 measurable_const
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
      let highPhysical := positiveLowerFibreProjectedPhysical
        Yw graph f0 measurable_const level
      u ∈ highPhysical.multiplicityBand p p) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    highFibreWeightedMultiplicity Yw graph f0 level u ≤
      2 * (p : ENNReal) := by
  dsimp only at hu ⊢
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let highPhysical := positiveLowerFibreProjectedPhysical
    Yw graph f0 measurable_const level
  have huData := highPhysical.mem_multiplicityBand.mp (by
    simpa only [highPhysical, Yw, f0, Z, graph, VS] using hu)
  have hcard : (highPhysical.activeAtPoint u).card = p := by omega
  rw [show highFibreWeightedMultiplicity Yw graph f0 level u =
      ∑ i ∈ highPhysical.activeAtPoint u,
        shadingFiberMass Yw f0 i u by
    simpa only [highPhysical] using
      highFibreWeightedMultiplicity_eq_sum_positiveLower_activeAtPoint
        Yw graph f0 measurable_const level u]
  calc
    (∑ i ∈ highPhysical.activeAtPoint u,
        shadingFiberMass Yw f0 i u) ≤
        ∑ _i ∈ highPhysical.activeAtPoint u, (2 : ENNReal) := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [Z, f0, Yw] using
        sameGraph_zeroWindow_shadingFiberMass_le_two
          (R := R) htauHalf i u
    _ = 2 * (p : ENNReal) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      ac_rfl

/-- Integrated ceiling on the exact-card band selected after explicit high
truncation.  The density remains the high-fibre density throughout. -/
theorem sameGraph_zeroWindow_highFibreWeightedMass_exactCard_le
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (level : ENNReal) (p : Nat) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    let highPhysical := positiveLowerFibreProjectedPhysical
      Yw graph f0 measurable_const level
    let E := highPhysical.multiplicityBand p p
    highFibreWeightedMass Yw graph f0 level E ≤
      2 * (p : ENNReal) * volume E := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let highPhysical := positiveLowerFibreProjectedPhysical
    Yw graph f0 measurable_const level
  let E := highPhysical.multiplicityBand p p
  have hE : MeasurableSet E :=
    highPhysical.measurableSet_multiplicityBand p p
  unfold highFibreWeightedMass
  calc
    (∫⁻ u in E,
        highFibreWeightedMultiplicity Yw graph f0 level u
          ∂(volume : Measure ProjectionSpace)) ≤
        ∫⁻ _u in E, 2 * (p : ENNReal)
          ∂(volume : Measure ProjectionSpace) := by
      exact setLIntegral_mono' hE fun u hu ↦
        sameGraph_zeroWindow_highFibreWeightedMultiplicity_le_two_mul_card
          (R := R) htauHalf level p u (by
            simpa only [E, highPhysical, Yw, f0, Z, graph, VS] using hu)
    _ = 2 * (p : ENNReal) * volume E := by
      rw [setLIntegral_const]

#print axioms
  highFibreWeightedMultiplicity_eq_sum_positiveLower_activeAtPoint
#print axioms
  sameGraph_zeroWindow_highFibreWeightedMultiplicity_le_two_mul_card
#print axioms sameGraph_zeroWindow_highFibreWeightedMass_exactCard_le

end

end Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardCeilingV1
