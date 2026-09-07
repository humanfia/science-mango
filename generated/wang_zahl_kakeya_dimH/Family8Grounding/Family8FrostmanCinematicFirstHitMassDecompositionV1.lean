import Family8Grounding.Family8FrostmanCinematicCellChargingUnionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1
import FamilyStickyGrounding.FamilyStickyWZ2ShadingPopularityV2

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrostmanCinematicFirstHitMassDecompositionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanCinematicCellChargingUnionV1
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1

noncomputable section

/-!
# Exact source-mass decomposition over cinematic spatial cells

The global charging theorem previously exposed an inequality
`shadingMass <= sum cellMass`.  Here that premise is generated from literal
measurable cells: `cellMass` is the sum, over all tubes, of shading mass
restricted to one cell.  Pairwise disjoint cells whose union is the shaded
union give an exact finite Fubini identity.

The first-hit corollary constructs such cells from any finite measurable cover
of the shaded union.  Thus the remaining Family 7 seam is only the genuine
local estimate bounding each restricted cell mass by its cinematic charge.
-/

/-- Multiplicity-counted shading mass restricted to one spatial cell. -/
def cellRestrictedShadingMass
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) (X : Set Space) : ENNReal :=
  ∑ i, restrictedMass Y X i

/-- Exact finite Fubini identity for a measurable disjoint partition of the
literal shaded union. -/
theorem sum_cellRestrictedShadingMass_eq_shadingMass
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    {cell : Type} [DecidableEq cell]
    (cells : Finset cell) (cellSet : cell -> Set Space)
    (hmeasurable : forall c, c ∈ cells -> MeasurableSet (cellSet c))
    (hdisjoint : Set.PairwiseDisjoint (cells : Set cell) cellSet)
    (hunion : (⋃ c ∈ (cells : Set cell), cellSet c) = Y.shadedUnion) :
    (∑ c ∈ cells, cellRestrictedShadingMass Y (cellSet c)) =
      Y.shadingMass := by
  classical
  unfold cellRestrictedShadingMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  have hmeasure :
      volume (⋃ c ∈ (cells : Set cell),
          Y.carrier i ∩ cellSet c) =
        ∑ c ∈ cells, volume (Y.carrier i ∩ cellSet c) := by
    apply measure_biUnion_finset
    · intro c hc d hd hcd
      exact (hdisjoint hc hd hcd).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro c hc
      exact (Y.measurable_carrier i).inter (hmeasurable c hc)
  have hunionCarrier :
      (⋃ c ∈ (cells : Set cell), Y.carrier i ∩ cellSet c) =
        Y.carrier i := by
    rw [show (⋃ c ∈ (cells : Set cell), Y.carrier i ∩ cellSet c) =
        Y.carrier i ∩ (⋃ c ∈ (cells : Set cell), cellSet c) by
      ext x
      simp only [mem_iUnion, mem_inter_iff]
      aesop]
    rw [hunion, Set.inter_eq_left]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  calc
    (∑ c ∈ cells, restrictedMass Y (cellSet c) i) =
        ∑ c ∈ cells, volume (Y.carrier i ∩ cellSet c) := by
      rfl
    _ = volume (⋃ c ∈ (cells : Set cell),
          Y.carrier i ∩ cellSet c) := hmeasure.symm
    _ = volume (Y.carrier i) := by rw [hunionCarrier]

/-- The measurable first-hit fibres of any finite cover of the shaded union
automatically provide the exact global source-mass decomposition. -/
theorem sum_firstHit_cellRestrictedShadingMass_eq_shadingMass
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    {cell : Type} [DecidableEq cell]
    (cells : Finset cell) (event : cell -> Set Space)
    (hmeasurable : forall c, c ∈ cells -> MeasurableSet (event c))
    (hcover : forall x, x ∈ Y.shadedUnion ->
      exists c, c ∈ cells ∧ x ∈ event c) :
    (∑ c ∈ cells,
        cellRestrictedShadingMass Y
          (finiteFirstHitFiber Y.shadedUnion cells event c)) =
      Y.shadingMass := by
  apply sum_cellRestrictedShadingMass_eq_shadingMass Y cells
    (fun c => finiteFirstHitFiber Y.shadedUnion cells event c)
  · intro c hc
    exact measurableSet_finiteFirstHitFiber Y.shadedUnion cells event
      Y.shadedUnion_measurableSet hmeasurable c
  · exact finiteFirstHitFibers_pairwiseDisjoint Y.shadedUnion cells event
  · exact biUnion_finiteFirstHitFiber_eq_source
      Y.shadedUnion cells event hcover

/-- Fully automatic global source side for the Frostman cinematic charge:
only one local bound per first-hit cell remains. -/
theorem shadedUnion_lower_of_firstHit_cinematic_cell_charges
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {eta zeta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hdensity : (delta : ENNReal) ^ eta <= D.shading.shadingDensity)
    (hfamily : (delta : ENNReal) ^ eta <= D.actualFamilyVolume)
    (hexponent : 2 * eta + zeta <= gamma / 2)
    {cell : Type} [DecidableEq cell]
    (cells : Finset cell) (event : cell -> Set Space)
    (hmeasurable : forall c, c ∈ cells -> MeasurableSet (event c))
    (hcover : forall x, x ∈ D.shading.shadedUnion ->
      exists c, c ∈ cells ∧ x ∈ event c)
    (hlocal : forall c, c ∈ cells ->
      cellRestrictedShadingMass D.shading
          (finiteFirstHitFiber D.shading.shadedUnion cells event c) <=
        (delta : ENNReal) ^ (-zeta) *
          volume (finiteFirstHitFiber D.shading.shadedUnion cells event c)) :
    (delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion := by
  apply shadedUnion_lower_of_disjoint_cinematic_cell_charges
    D hdelta hdeltaOne hdensity hfamily hexponent cells
      (fun c => finiteFirstHitFiber D.shading.shadedUnion cells event c)
      (fun c => cellRestrictedShadingMass D.shading
        (finiteFirstHitFiber D.shading.shadedUnion cells event c))
  · rw [sum_firstHit_cellRestrictedShadingMass_eq_shadingMass
      D.shading cells event hmeasurable hcover]
  · exact hlocal
  · intro c hc
    exact measurableSet_finiteFirstHitFiber D.shading.shadedUnion cells event
      D.shading.shadedUnion_measurableSet hmeasurable c
  · exact finiteFirstHitFibers_pairwiseDisjoint
      D.shading.shadedUnion cells event
  · intro c hc
    exact finiteFirstHitFiber_subset_source
      D.shading.shadedUnion cells event c

#print axioms cellRestrictedShadingMass
#print axioms sum_cellRestrictedShadingMass_eq_shadingMass
#print axioms sum_firstHit_cellRestrictedShadingMass_eq_shadingMass
#print axioms shadedUnion_lower_of_firstHit_cinematic_cell_charges

end

end Family8FrostmanCinematicFirstHitMassDecompositionV1
