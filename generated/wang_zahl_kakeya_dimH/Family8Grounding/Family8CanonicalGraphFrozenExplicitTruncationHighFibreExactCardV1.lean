import Family8Grounding.Family8CanonicalGraphFrozenLowFibreWeightedTailV1
import Family8Grounding.Family8ExplicitTruncationHighFibreExactCardV1
import Mathlib.Tactic

/-!
# Exact-card retention of the explicit high-fibre weighted mass

This is the direct adapter from the explicit high/low truncation to the
finite exact-card selector.  Its selected band belongs to the literal
`positiveLowerFibreProjectedPhysical` built from the same shading, active
family, projection and level.  There is no dyadic fibre bucket and no scale
counter in the conclusion.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenLowFibreWeightedTailV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ExplicitTruncationHighFibreExactCardV1
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

omit [DecidableEq iota] in
/-- The measure with explicit high-fibre density evaluates to the named
`highFibreWeightedMass` on measurable sets. -/
theorem withDensity_highFibreWeightedMultiplicity_apply
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (_hf : Measurable f) (level : ENNReal)
    (E : Set ProjectionSpace) (hE : MeasurableSet E) :
    ((volume : Measure ProjectionSpace).withDensity
      (highFibreWeightedMultiplicity Y active f level)) E =
        highFibreWeightedMass Y active f level E := by
  rw [MeasureTheory.withDensity_apply _ hE]
  rfl

/-- The nonzero support of the explicit high-fibre density is contained in
the nonempty active region of the exact same positive-lower physical datum. -/
theorem highFibreWeightedMultiplicity_supports_same_positiveLower
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal)
    (u : ProjectionSpace)
    (hu : highFibreWeightedMultiplicity Y active f level u ≠ 0) :
    u ∈ (positiveLowerFibreProjectedPhysical
          Y active f hf level).base ∧
      ((positiveLowerFibreProjectedPhysical
          Y active f hf level).activeAtPoint u).Nonempty := by
  classical
  have hsumPos :
      0 < highFibreWeightedMultiplicity Y active f level u :=
    pos_iff_ne_zero.mpr hu
  unfold highFibreWeightedMultiplicity at hsumPos
  obtain ⟨i, hiActive, hiTerm⟩ := Finset.sum_pos_iff.mp hsumPos
  let mass := shadingFiberMass Y f i u
  have hcondition : 0 < mass ∧ level ≤ mass := by
    by_contra hnot
    simp only [mass, if_neg hnot] at hiTerm
    exact (lt_irrefl 0 hiTerm)
  refine ⟨Set.mem_univ u, ⟨i, ?_⟩⟩
  apply (mem_activeAtPoint_positiveLowerFibreProjectedPhysical
    Y active f hf level u i).mpr
  simpa only [mass] using And.intro hiActive hcondition

/-- Exact-card selection after explicit truncation.  The sole loss is the
number of possible positive active-card values, `active.card`.

The hypothesis `1 ≤ active.card` is purely the nonemptiness needed to choose
a label even when the retained high mass happens to be zero.  In the frozen
canonical application it follows from the already fixed nonzero graph mass.
-/
theorem exists_positiveLower_exactCard_highFibreWeightedMass_ge_average
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal)
    (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hactive : 1 ≤ active.card) :
    let highPhysical :=
      positiveLowerFibreProjectedPhysical Y active f hf level
    ∃ p : Nat, 1 ≤ p ∧ p ≤ active.card ∧
      highFibreWeightedMass Y active f level E ≤
        (active.card : ENNReal) *
          highFibreWeightedMass Y active f level
            (E ∩ highPhysical.multiplicityBand p p) := by
  dsimp only
  let highPhysical :=
    positiveLowerFibreProjectedPhysical Y active f hf level
  let highWeight := highFibreWeightedMultiplicity Y active f level
  have hsupport : ∀ u ∈ E, highWeight u ≠ 0 →
      u ∈ highPhysical.base ∧
        (highPhysical.activeAtPoint u).Nonempty := by
    intro u _huE hu
    simpa only [highWeight, highPhysical] using
      highFibreWeightedMultiplicity_supports_same_positiveLower
        Y active f hf level u hu
  obtain ⟨p, hpLower, hpUpper, hpMass⟩ :=
    exists_exactCard_weightedMass_ge_average
      (volume : Measure ProjectionSpace) highPhysical highWeight
      (by
        simpa only [highWeight] using
          measurable_highFibreWeightedMultiplicity
            Y active f hf level)
      E hE (by simpa only [highPhysical,
        positiveLowerFibreProjectedPhysical] using hactive)
      hsupport
  have hselected : MeasurableSet
      (E ∩ highPhysical.multiplicityBand p p) :=
    hE.inter (highPhysical.measurableSet_multiplicityBand p p)
  refine ⟨p, hpLower, by
    simpa only [highPhysical, positiveLowerFibreProjectedPhysical]
      using hpUpper, ?_⟩
  rw [withDensity_highFibreWeightedMultiplicity_apply
    Y active f hf level E hE] at hpMass
  rw [withDensity_highFibreWeightedMultiplicity_apply
    Y active f hf level
      (E ∩ highPhysical.multiplicityBand p p) hselected] at hpMass
  simpa only [highPhysical, highWeight,
    positiveLowerFibreProjectedPhysical] using hpMass

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Frozen-canonical specialization.  Graph nonemptiness is read from the
certificate already stored in `R`; hence this theorem has no new witness and
no external active-card premise. -/
theorem exists_sameGraph_zeroWindow_positiveLower_exactCard_highMass
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (level : ENNReal) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    let highPhysical :=
      positiveLowerFibreProjectedPhysical Yw graph f0
        measurable_const level
    ∃ p : Nat, 1 ≤ p ∧ p ≤ graph.card ∧
      highFibreWeightedMass Yw graph f0 level Set.univ ≤
        (graph.card : ENNReal) *
          highFibreWeightedMass Yw graph f0 level
            (highPhysical.multiplicityBand p p) := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let highPhysical :=
    positiveLowerFibreProjectedPhysical Yw graph f0
      measurable_const level
  let Q := Classical.choice R.graphCertificate
  have hgraphNonempty : graph.Nonempty := by
    simpa only [graph, VS] using Q.graph_nonempty
  obtain ⟨p, hpLower, hpUpper, hpMass⟩ :=
    exists_positiveLower_exactCard_highFibreWeightedMass_ge_average
      Yw graph f0 measurable_const level Set.univ MeasurableSet.univ
        (Finset.one_le_card.mpr hgraphNonempty)
  refine ⟨p, hpLower, hpUpper, ?_⟩
  simpa only [Set.univ_inter, highPhysical] using hpMass

#print axioms withDensity_highFibreWeightedMultiplicity_apply
#print axioms highFibreWeightedMultiplicity_supports_same_positiveLower
#print axioms
  exists_positiveLower_exactCard_highFibreWeightedMass_ge_average
#print axioms
  exists_sameGraph_zeroWindow_positiveLower_exactCard_highMass

end

end Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardV1
