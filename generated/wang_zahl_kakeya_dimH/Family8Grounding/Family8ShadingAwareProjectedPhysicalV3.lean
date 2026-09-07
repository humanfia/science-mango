import Family8Grounding.Family8FrostmanCinematicProjectedFirstHitMassBridgeV1
import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingAwareProjectedPhysicalV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TwistedFiberVolumeV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

/-!
# A shading-aware projected physical datum

The cinematic `FiniteProjectedShading` used by the current Family 7 endpoint
counts membership in a full analytic tube trace.  That carrier is independent
of the actual shading and therefore cannot, by itself, represent the fibre
mass appearing in `projectedActiveMultiplicity`.

Here the projected carrier of an index is instead the literal positivity set
of its actual one-dimensional shading mass.  Both the projected base `X` and
the fibre-coordinate window `I` are built into the ambient shading
restriction.  Tonelli gives measurability, and `volume I <= 1` gives the
callback-free pointwise comparison

`projectedActiveMultiplicity <= activeAtPoint.card`.

No multiplicity comparison is stored as structure data.
-/

variable {iota : Type*} {F : ConvexFamily iota}

/-- The literal ambient region over a projected set `X` and fibre-coordinate
window `I`. -/
def shadingProjectionWindow
    (f : Real -> Real) (X : Set ProjectionSpace) (I : Set Real) : Set Space :=
  twistedProjection f ⁻¹' X ∩ (fun p : Space => p 1) ⁻¹' I

theorem measurableSet_shadingProjectionWindow
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) :
    MeasurableSet (shadingProjectionWindow f X I) := by
  apply ((twistedProjection_measurable f hf) hX).inter
  exact (by fun_prop : Measurable fun p : Space => p 1) hI

/-- Restrict the actual shading, before projection, to the requested base and
fibre window. -/
noncomputable def shadingWindowRestriction
    (Y : Shading F) (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) : Shading F :=
  Y.restrictSet (shadingProjectionWindow f X I)
    (measurableSet_shadingProjectionWindow f hf X hX I hI)

/-- Actual one-dimensional mass of one shading carrier above a projected
point. -/
noncomputable def shadingFiberMass
    (Y : Shading F) (f : Real -> Real) (i : iota)
    (u : ProjectionSpace) : ENNReal :=
  ∫⁻ y : Real,
    (Y.carrier i).indicator (fun _ => (1 : ENNReal))
      (twistedFiberChart f (u, y)) ∂volume

/-- Fibre mass varies measurably with the projected point. -/
theorem measurable_shadingFiberMass
    (Y : Shading F) (f : Real -> Real) (hf : Measurable f) (i : iota) :
    Measurable (shadingFiberMass Y f i) := by
  unfold shadingFiberMass
  have hchart : Measurable (twistedFiberChart f) :=
    (twistedFiberChart_measurePreserving f hf).measurable
  have hintegrand : Measurable fun q : ProjectionSpace × Real =>
      (Y.carrier i).indicator (fun _ => (1 : ENNReal))
        (twistedFiberChart f q) :=
    (measurable_const.indicator (Y.measurable_carrier i)).comp hchart
  exact hintegrand.lintegral_prod_right

/-- Pointwise projected multiplicity is the sum of the literal fibre masses
of the active indices. -/
theorem projectedActiveMultiplicity_eq_sum_shadingFiberMass
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f) (u : ProjectionSpace) :
    projectedActiveMultiplicity Y active f u =
      ∑ i ∈ active, shadingFiberMass Y f i u := by
  classical
  unfold projectedActiveMultiplicity projectedSliceMultiplicity
  simp_rw [activePointMultiplicity_cast_eq_sum_indicator]
  rw [lintegral_finsetSum active]
  · rfl
  · intro i _hi
    have hchart : Measurable fun y : Real =>
        twistedFiberChart f (u, y) :=
      (twistedFiberChart_measurePreserving f hf).measurable.comp
        (measurable_const.prodMk measurable_id)
    exact (measurable_const.indicator (Y.measurable_carrier i)).comp hchart

/-- The projected physical datum attached to an actual localized shading.
An index is active exactly when its localized shading fibre has positive
one-dimensional mass. -/
noncomputable def shadingAwareProjectedPhysical
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) :
    FiniteProjectedShading ProjectionSpace iota where
  ambient := active
  base := X
  carrier := fun i => X ∩
    {u | 0 < shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u}
  measurable_base := hX
  measurable_carrier := by
    intro i _hi
    exact hX.inter (measurableSet_lt measurable_const
      (measurable_shadingFiberMass
        (shadingWindowRestriction Y f hf X hX I hI) f hf i))

@[simp]
theorem mem_activeAtPoint_shadingAwareProjectedPhysical
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (u : ProjectionSpace) (i : iota) :
    i ∈ (shadingAwareProjectedPhysical Y active f hf X hX I hI).activeAtPoint u ↔
      i ∈ active ∧ u ∈ X ∧
        0 < shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u := by
  rw [FiniteProjectedShading.mem_activeAtPoint]
  rfl

/-- Every fibre of the window-restricted shading is supported inside the
literal fibre window. -/
theorem shadingFiberMass_shadingWindowRestriction_le_volume
    (Y : Shading F) (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (i : iota)
    (u : ProjectionSpace) :
    shadingFiberMass (shadingWindowRestriction Y f hf X hX I hI) f i u <=
      volume I := by
  unfold shadingFiberMass
  calc
    (∫⁻ y : Real,
        ((shadingWindowRestriction Y f hf X hX I hI).carrier i).indicator
          (fun _ => (1 : ENNReal)) (twistedFiberChart f (u, y)) ∂volume) <=
        ∫⁻ y : Real, I.indicator (1 : Real -> ENNReal) y ∂volume := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ I
      · by_cases hmem : twistedFiberChart f (u, y) ∈
            (shadingWindowRestriction Y f hf X hX I hI).carrier i
        · simp [hy, hmem]
        · simp [hy, hmem]
      · have hnot : twistedFiberChart f (u, y) ∉
            (shadingWindowRestriction Y f hf X hX I hI).carrier i := by
          simp [shadingWindowRestriction, Shading.restrictSet,
            shadingProjectionWindow, hy, twistedFiberChart, point3]
        simp [hy, hnot]
    _ = volume I := by
      exact lintegral_indicator_one hI

/-- The promised constant-one comparison.  It is a theorem about the actual
window-restricted shading and the constructed physical datum, not a field or
callback. -/
theorem projectedActiveMultiplicity_shadingWindowRestriction_le_activeAtPoint_card
    [DecidableEq iota]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hIone : volume I <= 1) (u : ProjectionSpace) (hu : u ∈ X) :
    projectedActiveMultiplicity
        (shadingWindowRestriction Y f hf X hX I hI) active f u <=
      (((shadingAwareProjectedPhysical Y active f hf X hX I hI).activeAtPoint u).card :
        ENNReal) := by
  classical
  rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
    (shadingWindowRestriction Y f hf X hX I hI) active f hf u]
  let mass : iota -> ENNReal := fun i =>
    shadingFiberMass (shadingWindowRestriction Y f hf X hX I hI) f i u
  have hmassOne : forall i, mass i <= 1 := by
    intro i
    exact (shadingFiberMass_shadingWindowRestriction_le_volume
      Y f hf X hX I hI i u).trans hIone
  have hsum :
      (∑ i ∈ active, mass i) <=
        ∑ i ∈ active, if 0 < mass i then (1 : ENNReal) else 0 := by
    apply Finset.sum_le_sum
    intro i _hi
    by_cases hpos : 0 < mass i
    · simp only [if_pos hpos]
      exact hmassOne i
    · have hzero : mass i = 0 := by
        exact nonpos_iff_eq_zero.mp (le_of_not_gt hpos)
      simp [hzero]
  have hactiveEq :
      (shadingAwareProjectedPhysical Y active f hf X hX I hI).activeAtPoint u =
        active.filter fun i => 0 < mass i := by
    ext i
    rw [mem_activeAtPoint_shadingAwareProjectedPhysical,
      Finset.mem_filter]
    simp only [hu, true_and, mass]
  change (∑ i ∈ active, mass i) <= _
  calc
    (∑ i ∈ active, mass i) <=
        ∑ i ∈ active, if 0 < mass i then (1 : ENNReal) else 0 := hsum
    _ = ((active.filter fun i => 0 < mass i).card : ENNReal) := by
      exact Finset.sum_boole (fun i => 0 < mass i) active
    _ = (((shadingAwareProjectedPhysical Y active f hf X hX I hI).activeAtPoint u).card :
        ENNReal) := by rw [hactiveEq]

#print axioms shadingProjectionWindow
#print axioms measurableSet_shadingProjectionWindow
#print axioms shadingWindowRestriction
#print axioms shadingFiberMass
#print axioms measurable_shadingFiberMass
#print axioms projectedActiveMultiplicity_eq_sum_shadingFiberMass
#print axioms shadingAwareProjectedPhysical
#print axioms mem_activeAtPoint_shadingAwareProjectedPhysical
#print axioms shadingFiberMass_shadingWindowRestriction_le_volume
#print axioms projectedActiveMultiplicity_shadingWindowRestriction_le_activeAtPoint_card

end

end Family8ShadingAwareProjectedPhysicalV3
