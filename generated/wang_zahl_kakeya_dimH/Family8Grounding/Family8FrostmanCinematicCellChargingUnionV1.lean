import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrostmanCinematicCellChargingUnionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra

open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-!
# Global finite-cell charging for the Frostman-at-every-scale branch

The current Family 7 cinematic theorem is local: it controls one retained
positive-center cell.  The missing step in the paper's Theorem 7.3(A) is a
global decomposition which charges all high and low cells to disjoint pieces
of the original shaded union.  This file proves the complete measure and
power algebra after such a decomposition has been constructed.

The hypotheses below are deliberately geometric and local.  In particular,
there is no premise asserting a lower bound for the shaded union, no
average-multiplicity conclusion, and no Katz--Tao or `IsStickyAtEveryScale`
assumption.  The first unproved Family 7 seam is now the construction of
`cells`, `cellSet`, and `cellMass` for which `hsource`, `hlocal`, and the
disjointness/subset properties hold.
-/

/-- Density and a genuine lower bound for the indexed family volume give the
source mass power used by the all-Frostman branch.  The family-volume premise
is kept explicit because the current formal `IsFrostmanAtEveryScale` predicate
alone does not provide the paper's top-scale branching normalization. -/
theorem densityPower_le_shadingMass
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) {eta : Real}
    (hdelta : 0 < delta)
    (hdensity : (delta : ENNReal) ^ eta <= D.shading.shadingDensity)
    (hfamily : (delta : ENNReal) ^ eta <= D.actualFamilyVolume) :
    (delta : ENNReal) ^ (2 * eta) <= D.shading.shadingMass := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hdelta)
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [show 2 * eta = eta + eta by ring,
    ENNReal.rpow_add _ _ hd0 hdTop]
  calc
    (delta : ENNReal) ^ eta * (delta : ENNReal) ^ eta <=
        D.shading.shadingDensity * D.actualFamilyVolume :=
      mul_le_mul hdensity hfamily bot_le bot_le
    _ = D.shading.shadingMass := by
      simpa only [ActualTubeDatum.actualFamilyVolume] using
        (shadingDensity_mul_familyVolume D.shading)

/-- A finite collection of pairwise-disjoint measurable cells contained in
the literal shaded union converts local cinematic charges into one global
mass-to-union inequality.  This is the precise summation layer missing after
the current one-cell Family 7 endpoints. -/
theorem shadingMass_le_loss_mul_shadedUnion_of_disjoint_cell_charges
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {cell : Type} [DecidableEq cell]
    (cells : Finset cell) (cellSet : cell -> Set Space)
    (cellMass : cell -> ENNReal) (loss : ENNReal)
    (hsource : D.shading.shadingMass <=
      ∑ c ∈ cells, cellMass c)
    (hlocal : forall c, c ∈ cells ->
      cellMass c <= loss * volume (cellSet c))
    (hmeasurable : forall c, c ∈ cells -> MeasurableSet (cellSet c))
    (hdisjoint : Set.PairwiseDisjoint (cells : Set cell) cellSet)
    (hsubset : forall c, c ∈ cells ->
      cellSet c ⊆ D.shading.shadedUnion) :
    D.shading.shadingMass <= loss * volume D.shading.shadedUnion := by
  have hunionSubset :
      (⋃ c ∈ (cells : Set cell), cellSet c) ⊆ D.shading.shadedUnion := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    exact hsubset c hc hxc
  have hmeasure :
      volume (⋃ c ∈ (cells : Set cell), cellSet c) =
        ∑ c ∈ cells, volume (cellSet c) :=
    measure_biUnion_finset hdisjoint hmeasurable
  have hunionVolume :
      volume (⋃ c ∈ (cells : Set cell), cellSet c) <=
        volume D.shading.shadedUnion :=
    measure_mono hunionSubset
  calc
    D.shading.shadingMass <= ∑ c ∈ cells, cellMass c := hsource
    _ <= ∑ c ∈ cells, loss * volume (cellSet c) :=
      Finset.sum_le_sum hlocal
    _ = loss * ∑ c ∈ cells, volume (cellSet c) := by
      rw [Finset.mul_sum]
    _ = loss * volume (⋃ c ∈ (cells : Set cell), cellSet c) := by
      rw [hmeasure]
    _ <= loss * volume D.shading.shadedUnion := by
      exact mul_le_mul_right hunionVolume loss

/-- Small-base exponent bookkeeping for the exact loss `delta^(-zeta)`.
This is division-free until the final cancellation by a positive finite
power of the positive finite base `delta`. -/
theorem lossPower_mul_targetPower_le_densityPower
    {delta : NNReal} {eta zeta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hexponent : 2 * eta + zeta <= gamma / 2) :
    (delta : ENNReal) ^ (-zeta) * (delta : ENNReal) ^ (gamma / 2) <=
      (delta : ENNReal) ^ (2 * eta) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hdelta)
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have heta : 2 * eta <= gamma / 2 - zeta := by linarith
  calc
    (delta : ENNReal) ^ (-zeta) *
          (delta : ENNReal) ^ (gamma / 2) =
        (delta : ENNReal) ^ ((-zeta) + gamma / 2) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^ (gamma / 2 - zeta) := by
      congr 1
      ring
    _ <= (delta : ENNReal) ^ (2 * eta) :=
      ENNReal.rpow_le_rpow_of_exponent_ge
        (by exact_mod_cast hdeltaOne) heta

/-- Literal shaded-union lower bound from an honest finite disjoint cinematic
cell charging.  This theorem contains no coarse Katz--Tao input.  Its only
open analytic premise is local (`hlocal`) and its only global combinatorial
premise is an actual mass decomposition (`hsource`); pairwise disjointness and
literal containment perform the global charge without assuming the result. -/
theorem shadedUnion_lower_of_disjoint_cinematic_cell_charges
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {eta zeta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hdensity : (delta : ENNReal) ^ eta <= D.shading.shadingDensity)
    (hfamily : (delta : ENNReal) ^ eta <= D.actualFamilyVolume)
    (hexponent : 2 * eta + zeta <= gamma / 2)
    {cell : Type} [DecidableEq cell]
    (cells : Finset cell) (cellSet : cell -> Set Space)
    (cellMass : cell -> ENNReal)
    (hsource : D.shading.shadingMass <= ∑ c ∈ cells, cellMass c)
    (hlocal : forall c, c ∈ cells ->
      cellMass c <= (delta : ENNReal) ^ (-zeta) * volume (cellSet c))
    (hmeasurable : forall c, c ∈ cells -> MeasurableSet (cellSet c))
    (hdisjoint : Set.PairwiseDisjoint (cells : Set cell) cellSet)
    (hsubset : forall c, c ∈ cells ->
      cellSet c ⊆ D.shading.shadedUnion) :
    (delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion := by
  have hmassLower :
      (delta : ENNReal) ^ (2 * eta) <= D.shading.shadingMass :=
    densityPower_le_shadingMass D hdelta hdensity hfamily
  have hmassUpper :
      D.shading.shadingMass <=
        (delta : ENNReal) ^ (-zeta) * volume D.shading.shadedUnion :=
    shadingMass_le_loss_mul_shadedUnion_of_disjoint_cell_charges
      D cells cellSet cellMass ((delta : ENNReal) ^ (-zeta))
        hsource hlocal hmeasurable hdisjoint hsubset
  have hpower := lossPower_mul_targetPower_le_densityPower
    hdelta hdeltaOne hexponent
  have hfactor0 : (delta : ENNReal) ^ (-zeta) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta) ENNReal.coe_ne_top)
  have hfactorTop : (delta : ENNReal) ^ (-zeta) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (ENNReal.coe_pos.mpr hdelta)) ENNReal.coe_ne_top
  apply (ENNReal.mul_le_mul_iff_right hfactor0 hfactorTop).mp
  exact hpower.trans (hmassLower.trans hmassUpper)

#print axioms densityPower_le_shadingMass
#print axioms shadingMass_le_loss_mul_shadedUnion_of_disjoint_cell_charges
#print axioms lossPower_mul_targetPower_le_densityPower
#print axioms shadedUnion_lower_of_disjoint_cinematic_cell_charges

end

end Family8FrostmanCinematicCellChargingUnionV1
