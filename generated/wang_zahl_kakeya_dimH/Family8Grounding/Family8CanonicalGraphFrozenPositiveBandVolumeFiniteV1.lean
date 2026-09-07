import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketExactCardBandV1
import Family8Grounding.Family8Family7QuantitativeFibreFloorSelectionV1
import FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
import Mathlib.Tactic

/-!
# Finite volume of the canonical positive projected band

A positive-cardinality multiplicity band of the shading-aware physical datum
is supported in the finite union of the projected images of its active source
tubes.  For continuous graph functions those images are compact, so the band
has finite volume even when the declared projected base is `Set.univ`.

This supplies exactly the finite-volume premise of the quantitative fibre-
floor selector.  It does not assume that the projected base, fibre window,
shading carrier, or ambient space is compact.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenPositiveBandVolumeFiniteV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketExactCardBandV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7QuantitativeFibreFloorSelectionV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u

/-- The only compact support needed: the finite union of projected images of
the tubes in the actual active family. -/
def activeProjectedTubeImageSupport
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (active : Finset iota) (f : Real -> Real) : Set ProjectionSpace :=
  ⋃ i ∈ (active : Set iota), projectedTubeImageCarrier f (fine.tubes i)

theorem isCompact_activeProjectedTubeImageSupport
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (active : Finset iota) (f : Real -> Real) (hf : Continuous f) :
    IsCompact (activeProjectedTubeImageSupport fine active f) := by
  exact active.isCompact_biUnion fun i _hi =>
    isCompact_projectedTubeImageCarrier f hf (fine.tubes i)

/-- Positive fibre mass supplies an actual point of the same shading fibre. -/
theorem exists_mem_carrier_of_shadingFiberMass_pos
    {iota : Type u} {F : ConvexFamily iota}
    (Y : Shading F) (f : Real -> Real) (i : iota)
    (u : ProjectionSpace) (hpos : 0 < shadingFiberMass Y f i u) :
    ∃ y : Real, twistedFiberChart f (u, y) ∈ Y.carrier i := by
  by_contra hnone
  push Not at hnone
  have hintegrand :
      (fun y : Real =>
        (Y.carrier i).indicator (fun _ => (1 : ENNReal))
          (twistedFiberChart f (u, y))) = fun _ => 0 := by
    funext y
    simp [hnone y]
  unfold shadingFiberMass at hpos
  rw [hintegrand] at hpos
  simp at hpos

/-- For an actual uniform tube family, every positive projected carrier is
contained in the projected image of the same indexed tube. -/
theorem shadingAwareProjectedPhysical_carrier_subset_projectedTubeImageCarrier
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (i : iota) :
    (shadingAwareProjectedPhysical Y active f hf X hX I hI).carrier i ⊆
      projectedTubeImageCarrier f (fine.tubes i) := by
  intro u hu
  change u ∈ X ∧
    0 < shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u at hu
  obtain ⟨y, hy⟩ := exists_mem_carrier_of_shadingFiberMass_pos
    (shadingWindowRestriction Y f hf X hX I hI) f i u hu.2
  have hyY : twistedFiberChart f (u, y) ∈ Y.carrier i := by
    rw [shadingWindowRestriction, Shading.restrictSet_carrier] at hy
    exact hy.1
  refine ⟨twistedFiberChart f (u, y), Y.carrier_subset i hyY, ?_⟩
  simpa only [projectedTwistedProjection, twistedProjection] using
    (twistedProjection_twistedFiberChart f (u, y))

/-- A source multiplicity band with positive lower cardinality is supported
in the finite compact union above. -/
theorem positiveFibreMultiplicityBand_subset_activeProjectedTubeImageSupport
    {delta : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (f : Real -> Real) (hf : Continuous f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper : Nat) (hlower : 1 <= lower) :
    positiveFibreMultiplicityBand
        Y active f hf.measurable X hX I hI lower upper ⊆
      activeProjectedTubeImageSupport fine active f := by
  classical
  let physical := shadingAwareProjectedPhysical
    Y active f hf.measurable X hX I hI
  intro u hu
  have huband := (physical.mem_multiplicityBand).mp hu
  have hactiveOne : 1 <= (physical.activeAtPoint u).card :=
    hlower.trans huband.2.1
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hactiveOne
  have hidata := (physical.mem_activeAtPoint u i).mp hi
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨hidata.1, ?_⟩
  exact shadingAwareProjectedPhysical_carrier_subset_projectedTubeImageCarrier
    fine Y active f hf.measurable X hX I hI i hidata.2

/-- Weakest generic finite-volume producer used by the quantitative selector:
continuity and `1 <= lower` suffice; no global compactness premise is added. -/
theorem positiveFibreMultiplicityBand_volume_ne_top_of_continuous_of_one_le_lower
    {delta : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (f : Real -> Real) (hf : Continuous f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (lower upper : Nat) (hlower : 1 <= lower) :
    volume (positiveFibreMultiplicityBand
      Y active f hf.measurable X hX I hI lower upper) ≠ ⊤ := by
  have hsupportFinite :
      (volume : Measure ProjectionSpace)
        (activeProjectedTubeImageSupport fine active f) ≠ ⊤ :=
    (isCompact_activeProjectedTubeImageSupport
      fine active f hf).measure_ne_top
  exact ne_top_of_le_ne_top hsupportFinite <| measure_mono
    (positiveFibreMultiplicityBand_subset_activeProjectedTubeImageSupport
      fine Y active f hf X hX I hI lower upper hlower)

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Same-`R` specialization used by the frozen canonical zero-window caller.
The declared base and window are both universal; finiteness comes only from
the finite active graph family and compact projected tube images. -/
theorem sameGraph_zeroWindow_positiveExactCardBand_volume_ne_top
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (hn : 1 <= n) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real -> Real := fun _ => 0
    let hf0 : Continuous f0 := continuous_const
    let X0 : Set (Real × Real) := Set.univ
    let hX0 : MeasurableSet X0 := MeasurableSet.univ
    let I0 : Set Real := Set.univ
    let hI0 : MeasurableSet I0 := MeasurableSet.univ
    volume ((shadingAwareProjectedPhysical Z graph f0 hf0.measurable
      X0 hX0 I0 hI0).multiplicityBand n n) ≠ ⊤ := by
  dsimp only
  simpa only [positiveFibreMultiplicityBand] using
    positiveFibreMultiplicityBand_volume_ne_top_of_continuous_of_one_le_lower
      (firstCrossingFamilyVerticalSource R.axis F P R.k).family
      (firstCrossingFamilyGraphBucketShading
        R.axis R.label F P R.A R.k)
      (verticalSourceGraphCBucketFiber ((tau : Real) / 2)
        (firstCrossingFamilyVerticalSource R.axis F P R.k) R.label)
      (fun _ : Real => 0) continuous_const
      (Set.univ : Set (Real × Real)) MeasurableSet.univ
      (Set.univ : Set Real) MeasurableSet.univ n n hn

#print axioms activeProjectedTubeImageSupport
#print axioms isCompact_activeProjectedTubeImageSupport
#print axioms exists_mem_carrier_of_shadingFiberMass_pos
#print axioms
  shadingAwareProjectedPhysical_carrier_subset_projectedTubeImageCarrier
#print axioms
  positiveFibreMultiplicityBand_subset_activeProjectedTubeImageSupport
#print axioms
  positiveFibreMultiplicityBand_volume_ne_top_of_continuous_of_one_le_lower
#print axioms sameGraph_zeroWindow_positiveExactCardBand_volume_ne_top

end

end Family8CanonicalGraphFrozenPositiveBandVolumeFiniteV1
