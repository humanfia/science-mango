import Family8Grounding.Family8FrostmanCinematicLocalMultiplicityChargeV1
import FamilyStickyGrounding.FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrostmanCinematicProjectedFirstHitMassBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8FrostmanCinematicFirstHitMassDecompositionV1
open Family8FrostmanCinematicLocalMultiplicityChargeV1
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TwistedFiberVolumeV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1

noncomputable section

/-!
# Exact ambient mass carried by projected cinematic first-hit cells

The Family 7 cinematic cells live in the two-dimensional twisted-projection
plane, whereas the all-Frostman conclusion concerns the literal
three-dimensional shaded union.  This module closes the set-theoretic and
Tonelli part of that interface.

A first-hit partition of the projected shaded union pulls back to the
first-hit partition of the actual shaded union.  Its multiplicity-counted
ambient mass is exactly the integral, on the projected cell, of the genuine
one-dimensional fibre multiplicity `projectedActiveMultiplicity`.

Crucially, this fibre multiplicity is not the finite projected active-card
used in the present Family 7 low moment.  Comparing those two quantities is
the next genuine geometric input supplied in the paper by the C-uniform,
unit-rescaled parent-fibre Convex Wolff structure.
-/

/-- First-hit selection commutes exactly with pulling the events back by the
twisted projection, once the projected source is the literal image of the
ambient shaded union. -/
theorem finiteFirstHitFiber_twistedProjection_preimage
    {iota cell : Type} [Fintype iota] [DecidableEq cell]
    {F : ConvexFamily iota} (Y : Shading F)
    (f : Real -> Real) (cells : Finset cell)
    (event : cell -> Set ProjectionSpace) (c : cell) :
    finiteFirstHitFiber Y.shadedUnion cells
        (fun k => twistedProjection f ⁻¹' event k) c =
      Y.shadedUnion ∩
        twistedProjection f ⁻¹'
          finiteFirstHitFiber (twistedProjection f '' Y.shadedUnion)
            cells event c := by
  classical
  ext p
  constructor
  · intro hp
    have h := (mem_finiteFirstHitFiber_iff Y.shadedUnion cells
      (fun k => twistedProjection f ⁻¹' event k) c p).mp hp
    refine ⟨h.2.1, ?_⟩
    apply (mem_finiteFirstHitFiber_iff
      (twistedProjection f '' Y.shadedUnion) cells event c
        (twistedProjection f p)).mpr
    refine ⟨h.1, ⟨p, h.2.1, rfl⟩, h.2.2.1, ?_⟩
    intro k hk hrank hkEvent
    exact h.2.2.2 k hk hrank hkEvent
  · rintro ⟨hpSource, hpProjected⟩
    have h := (mem_finiteFirstHitFiber_iff
      (twistedProjection f '' Y.shadedUnion) cells event c
        (twistedProjection f p)).mp hpProjected
    apply (mem_finiteFirstHitFiber_iff Y.shadedUnion cells
      (fun k => twistedProjection f ⁻¹' event k) c p).mpr
    refine ⟨h.1, hpSource, h.2.2.1, ?_⟩
    intro k hk hrank hkEvent
    exact h.2.2.2 k hk hrank hkEvent

/-- Intersecting a restriction set with the shaded union does not change
any restricted carrier mass. -/
theorem cellRestrictedShadingMass_inter_shadedUnion
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) (X : Set Space) :
    cellRestrictedShadingMass Y (Y.shadedUnion ∩ X) =
      cellRestrictedShadingMass Y X := by
  classical
  unfold cellRestrictedShadingMass
  apply Finset.sum_congr rfl
  intro i _hi
  unfold restrictedMass
  congr 1
  ext p
  constructor
  · rintro ⟨hpCarrier, _hpUnion, hpX⟩
    exact ⟨hpCarrier, hpX⟩
  · rintro ⟨hpCarrier, hpX⟩
    exact ⟨hpCarrier, Set.mem_iUnion.mpr ⟨i, hpCarrier⟩, hpX⟩

/-- Exact 3D-to-2D mass identity on one projected first-hit cell. -/
theorem cellRestrictedShadingMass_projectedFirstHit_eq_lintegral
    {iota cell : Type} [Fintype iota] [DecidableEq cell]
    {F : ConvexFamily iota} (Y : Shading F)
    (f : Real -> Real) (hf : Measurable f)
    (cells : Finset cell) (event : cell -> Set ProjectionSpace) (c : cell) :
    cellRestrictedShadingMass Y
        (finiteFirstHitFiber Y.shadedUnion cells
          (fun k => twistedProjection f ⁻¹' event k) c) =
      ∫⁻ u in finiteFirstHitFiber
          (twistedProjection f '' Y.shadedUnion) cells event c,
        projectedActiveMultiplicity Y (Finset.univ : Finset iota) f u
          ∂(volume : Measure ProjectionSpace) := by
  rw [finiteFirstHitFiber_twistedProjection_preimage]
  rw [cellRestrictedShadingMass_inter_shadedUnion]
  unfold cellRestrictedShadingMass
  exact (lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
    Y (Finset.univ : Finset iota) f hf
      (finiteFirstHitFiber (twistedProjection f '' Y.shadedUnion)
        cells event c)).symm.trans (by simp)

/-- A finite measurable cover of the projected shaded union automatically
pulls back to a measurable cover of the literal ambient shaded union. -/
theorem projectedCover_gives_ambientPreimageCover
    {iota cell : Type} [Fintype iota] [DecidableEq cell]
    {F : ConvexFamily iota} (Y : Shading F)
    (f : Real -> Real) (hf : Measurable f)
    (cells : Finset cell) (event : cell -> Set ProjectionSpace)
    (hmeasurable : forall c, c ∈ cells -> MeasurableSet (event c))
    (hcover : forall u, u ∈ twistedProjection f '' Y.shadedUnion ->
      exists c, c ∈ cells ∧ u ∈ event c) :
    (forall c, c ∈ cells ->
        MeasurableSet (twistedProjection f ⁻¹' event c)) ∧
      (forall p, p ∈ Y.shadedUnion ->
        exists c, c ∈ cells ∧ p ∈ twistedProjection f ⁻¹' event c) := by
  constructor
  · intro c hc
    exact (twistedProjection_measurable f hf) (hmeasurable c hc)
  · intro p hp
    obtain ⟨c, hc, hpEvent⟩ := hcover (twistedProjection f p) ⟨p, hp, rfl⟩
    exact ⟨c, hc, hpEvent⟩

#print axioms finiteFirstHitFiber_twistedProjection_preimage
#print axioms cellRestrictedShadingMass_inter_shadedUnion
#print axioms cellRestrictedShadingMass_projectedFirstHit_eq_lintegral
#print axioms projectedCover_gives_ambientPreimageCover

end

end Family8FrostmanCinematicProjectedFirstHitMassBridgeV1
