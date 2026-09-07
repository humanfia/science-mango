import Family8Grounding.Family8ShadingAwareGenericNativeBranchCoreV2
import Family8Grounding.Family8FrostmanCinematicProjectedFirstHitMassBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ProjectedFirstHitActiveCardMassBridgeV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TwistedFiberVolumeV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open _root_.FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open Family8FrostmanCinematicFirstHitMassDecompositionV1
open Family8FrostmanCinematicProjectedFirstHitMassBridgeV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8ShadingAwareGenericNativeBranchCoreV2

noncomputable section

/-!
# Actual active first-hit mass is controlled by finite projected active card

The exact first-hit identity in the earlier bridge sums over the full tube
family.  Here the index set is an arbitrary actual active subfamily, so the
left side is honestly the corresponding finite sum of restricted masses.
The active-index Tonelli identity then matches the shading-aware physical
datum without changing `active` to `univ`.

The fact that the projected first-hit cell lies in the projected base is
proved from the literal shading window.  This module still does not construct
the native high/low geometry or upper-bound its active-card integral.
-/

/-- A projected first-hit cell of a window-restricted shading lies in the
literal projected base of that window. -/
theorem projectedFirstHit_windowRestriction_subset_base
    {iota cell : Type} [DecidableEq cell]
    {F : ConvexFamily iota}
    (Y : Shading F) (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (cells : Finset cell) (event : cell -> Set ProjectionSpace) (c : cell) :
    finiteFirstHitFiber
        (twistedProjection f ''
          (shadingWindowRestriction Y f hf X hX I hI).shadedUnion)
        cells event c ⊆ X := by
  intro u hu
  have huSource := finiteFirstHitFiber_subset_source
    (twistedProjection f ''
      (shadingWindowRestriction Y f hf X hX I hI).shadedUnion)
    cells event c hu
  obtain ⟨p, hp, rfl⟩ := huSource
  rw [shadingWindowRestriction, Shading.restrictSet_shadedUnion] at hp
  exact hp.2.1

/-- Intersecting a restriction set with the shaded union does not change the
restricted mass of any one index. -/
theorem restrictedMass_inter_shadedUnion
    {iota : Type} {F : ConvexFamily iota}
    (Y : Shading F) (A : Set Space) (i : iota) :
    restrictedMass Y (Y.shadedUnion ∩ A) i = restrictedMass Y A i := by
  unfold restrictedMass
  congr 1
  ext p
  constructor
  · rintro ⟨hpCarrier, _hpUnion, hpA⟩
    exact ⟨hpCarrier, hpA⟩
  · rintro ⟨hpCarrier, hpA⟩
    exact ⟨hpCarrier, Set.mem_iUnion.mpr ⟨i, hpCarrier⟩, hpA⟩

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {F : ConvexFamily iota}

/-- On each projected first-hit cell, the genuine multiplicity-counted mass
of the selected active indices is bounded by the integral of the finite
active-card function used by the shading-aware physical datum. -/
theorem activeRestrictedMass_projectedFirstHit_le_activeCardIntegral
    {cell : Type} [DecidableEq cell]
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (hIone : volume I <= 1)
    (cells : Finset cell) (event : cell -> Set ProjectionSpace) (c : cell) :
    (∑ i ∈ active,
        restrictedMass (shadingWindowRestriction Y f hf X hX I hI)
          (finiteFirstHitFiber
            (shadingWindowRestriction Y f hf X hX I hI).shadedUnion
            cells (fun k => twistedProjection f ⁻¹' event k) c) i) <=
      ∫⁻ u in finiteFirstHitFiber
          (twistedProjection f ''
            (shadingWindowRestriction Y f hf X hX I hI).shadedUnion)
          cells event c,
        (((shadingAwareProjectedPhysical Y active f hf X hX I hI).activeAtPoint u).card :
          ENNReal) ∂(volume : Measure ProjectionSpace) := by
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let A := finiteFirstHitFiber
    (twistedProjection f '' Yw.shadedUnion) cells event c
  have hfirst :
      finiteFirstHitFiber Yw.shadedUnion cells
          (fun k => twistedProjection f ⁻¹' event k) c =
        Yw.shadedUnion ∩ twistedProjection f ⁻¹' A := by
    exact finiteFirstHitFiber_twistedProjection_preimage
      Yw f cells event c
  have hsumEq :
      (∑ i ∈ active,
          restrictedMass Yw
            (finiteFirstHitFiber Yw.shadedUnion cells
              (fun k => twistedProjection f ⁻¹' event k) c) i) =
        ∑ i ∈ active, restrictedMass Yw (twistedProjection f ⁻¹' A) i := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hfirst, restrictedMass_inter_shadedUnion]
  rw [hsumEq]
  rw [← lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
    Yw active f hf A]
  have hmeasurableCard : Measurable fun u : ProjectionSpace =>
      (((shadingAwareProjectedPhysical Y active f hf X hX I hI).activeAtPoint u).card :
        ENNReal) :=
    FiniteProjectedShading.measurable_activeValue
      (shadingAwareProjectedPhysical Y active f hf X hX I hI)
      (fun s => (s.card : ENNReal))
  exact setLIntegral_mono hmeasurableCard
    (fun u hu =>
      projectedActiveMultiplicity_shadingWindowRestriction_le_activeAtPoint_card
        Y active f hf X hX I hI hIone u
          (projectedFirstHit_windowRestriction_subset_base
            Y f hf X hX I hI cells event c hu))

/-- Core-specialized form of the active-index bridge.  It compares with the
physical datum actually stored by the shading-aware generic core, not with
the old hard-coded Family 7 physical datum. -/
theorem ShadingAwareNativeBranchCore.activeRestrictedMass_projectedFirstHit_le
    {radius : NNReal}
    {S : WZL3UniformTubeSource radius iota}
    {Y : Shading S.family.bodyFamily} {active : Finset iota}
    {f : Real -> Real} {hfContinuous : Continuous f}
    {X : Set ProjectionSpace} {hX : MeasurableSet X}
    {I : Set Real} {hI : MeasurableSet I}
    (D : ShadingAwareNativeBranchCore S Y active f hfContinuous X hX I hI)
    (hIone : volume I <= 1)
    {cell : Type} [DecidableEq cell]
    (cells : Finset cell) (event : cell -> Set ProjectionSpace) (c : cell) :
    (∑ i ∈ active,
        restrictedMass
          (shadingWindowRestriction Y f hfContinuous.measurable X hX I hI)
          (finiteFirstHitFiber
            (shadingWindowRestriction Y f hfContinuous.measurable X hX I hI).shadedUnion
            cells (fun k => twistedProjection f ⁻¹' event k) c) i) <=
      ∫⁻ u in finiteFirstHitFiber
          (twistedProjection f ''
            (shadingWindowRestriction Y f hfContinuous.measurable X hX I hI).shadedUnion)
          cells event c,
        ((D.physicalDatum.activeAtPoint u).card : ENNReal)
          ∂(volume : Measure ProjectionSpace) := by
  exact activeRestrictedMass_projectedFirstHit_le_activeCardIntegral
    Y active f hfContinuous.measurable X hX I hI hIone cells event c

#print axioms projectedFirstHit_windowRestriction_subset_base
#print axioms restrictedMass_inter_shadedUnion
#print axioms activeRestrictedMass_projectedFirstHit_le_activeCardIntegral
#print axioms ShadingAwareNativeBranchCore.activeRestrictedMass_projectedFirstHit_le

end

end Family8ProjectedFirstHitActiveCardMassBridgeV6
