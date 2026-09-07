import Family8Grounding.Family8SelectedOccurrenceDirectSourceKatzTaoEq45ControlV1
import Family8Grounding.Family8Prop51JointOccurrenceWeightedSelectionV1
import Mathlib.Tactic

/-!
# Density-band Katz--Tao control for an exact selected outer subbucket

Suppose a greedy occurrence set `R` lies in one common block-density band and
the later winner-side selection retains a nonempty literal subset
`Rside ⊆ R`.  The lower endpoint of that same band automatically gives the
block-mass hypothesis required by the direct selected-occurrence Katz--Tao
transport.  Thus the normalized outer family on `Rside` has maximal
concentration at most `sourceKT * d⁻¹`, where
`d = 2^n * base`.

No new occurrence is selected and no active-parent datum is identified with
the normalized outer datum.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SelectedOccurrenceNormalizedOuterDensityBandKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceDirectSourceKatzTaoEq45ControlV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- The common density band on `R` transfers losslessly to the exact later
subbucket `Rside` and supplies direct normalized Katz--Tao control. -/
theorem selectedOccurrenceNormalizedOuter_isKatzTao_of_densityBand
    (base : ENNReal) (n : Nat)
    (labelOuter : Fin 3 -> Int)
    (R Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hRside : Rside.Nonempty) (hsub : Rside ⊆ R)
    (hband : forall q, q ∈ R ->
      InENNRealDyadicBand base n
        (blockDensity fine.bodyFamily (blockAt fine.bodyFamily P q)))
    (sourceKT : ENNReal) (hKT : IsKatzTao sourceKT fine.bodyFamily) :
    IsKatzTao (sourceKT * ((2 : ENNReal) ^ n * base)⁻¹)
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside) := by
  let d := (2 : ENNReal) ^ n * base
  have hd0 : d ≠ 0 := by
    intro hd
    obtain ⟨q, hqside⟩ := hRside
    have hupper := (hband q (hsub hqside)).2
    have hupperEq : (2 : ENNReal) ^ (n + 1) * base = 2 * d := by
      dsimp only [d]
      rw [pow_succ]
      ac_rfl
    rw [hupperEq, hd, mul_zero] at hupper
    exact (not_lt_of_ge bot_le) hupper
  have hdTop : d ≠ ∞ := by
    intro hd
    obtain ⟨q, hqside⟩ := hRside
    have hlower : d <= blockDensity fine.bodyFamily
        (blockAt fine.bodyFamily P q) := by
      simpa only [d] using (hband q (hsub hqside)).1
    have hdensityTop : blockDensity fine.bodyFamily
          (blockAt fine.bodyFamily P q) = ∞ :=
      top_unique (by simpa only [hd] using hlower)
    have hupper := (hband q (hsub hqside)).2
    rw [hdensityTop] at hupper
    exact (not_lt_of_ge le_top) hupper
  have hblockMassLower : forall q, q ∈ Rside ->
      d * volume ((blockAt fine.bodyFamily P q).body : Set Space) <=
        blockMass fine.bodyFamily (blockAt fine.bodyFamily P q) := by
    intro q hq
    have hlower : d <= blockDensity fine.bodyFamily
        (blockAt fine.bodyFamily P q) := by
      simpa only [d] using (hband q (hsub hq)).1
    exact lower_mul_volume_le_blockMass fine.bodyFamily
      (blockAt fine.bodyFamily P q) d hlower
  simpa only [d] using
    (selectedOccurrenceNormalizedOuterFamily_isKatzTao_of_sourceKatzTao_and_blockMass_lower
      P labelOuter Rside sourceKT d hKT hblockMassLower hd0 hdTop)

/-- Maximal-concentration form of the preceding exact same-`Rside` transfer. -/
theorem selectedOccurrenceNormalizedOuter_maximalConcentration_le_of_densityBand
    (base : ENNReal) (n : Nat)
    (labelOuter : Fin 3 -> Int)
    (R Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hRside : Rside.Nonempty) (hsub : Rside ⊆ R)
    (hband : forall q, q ∈ R ->
      InENNRealDyadicBand base n
        (blockDensity fine.bodyFamily (blockAt fine.bodyFamily P q)))
    (sourceKT : ENNReal) (hKT : IsKatzTao sourceKT fine.bodyFamily) :
    maximalConcentration
        (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside) <=
      sourceKT * ((2 : ENNReal) ^ n * base)⁻¹ := by
  rw [maximalConcentration_le_iff_isKatzTao]
  exact selectedOccurrenceNormalizedOuter_isKatzTao_of_densityBand
    P base n labelOuter R Rside hRside hsub hband sourceKT hKT

#print axioms selectedOccurrenceNormalizedOuter_isKatzTao_of_densityBand
#print axioms
  selectedOccurrenceNormalizedOuter_maximalConcentration_le_of_densityBand

end

end Family8SelectedOccurrenceNormalizedOuterDensityBandKatzTaoV1
