import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Mathlib.Tactic

/-!
# Positive source shading mass survives the full occurrence factorization

When every fine index is active, each source carrier lies in the induced
carrier of its unique greedy occurrence block.  Hence nonzero source shaded
mass forces nonzero full outer occurrence shaded mass, independently of any
overlap between carriers.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceOuterMassPositiveV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa → ConvexBody Space} {active : Finset iota}

theorem selectedOccurrenceOuterShading_univ_mass_ne_zero_of_active_eq_univ
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (hactive : active = Finset.univ)
    (hsource : Y.shadingMass ≠ 0) :
    (selectedOccurrenceOuterShading P Y Finset.univ).shadingMass ≠ 0 := by
  intro houter
  have hsum :
      (∑ k : Fin (blocks F P).length,
        volume (((convexFactorization F P).inducedShading Y).carrier
          (some k))) = 0 := by
    simpa only [selectedOccurrenceOuterShading_mass, Finset.sum_const_zero,
      Finset.sum_filter, Finset.mem_univ, if_true] using houter
  have hterm (k : Fin (blocks F P).length) :
      volume (((convexFactorization F P).inducedShading Y).carrier
        (some k)) = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      volume (((convexFactorization F P).inducedShading Y).carrier
          (some k)) ≤
        ∑ l : Fin (blocks F P).length,
          volume (((convexFactorization F P).inducedShading Y).carrier
            (some l)) := by
        exact Finset.single_le_sum
          (fun l _ => show (0 : ENNReal) ≤
            volume (((convexFactorization F P).inducedShading Y).carrier
              (some l)) from bot_le)
          (Finset.mem_univ k)
      _ = 0 := hsum
  have hcarrier (i : iota) : volume (Y.carrier i) = 0 := by
    have hi : i ∈ active := by
      rw [hactive]
      exact Finset.mem_univ i
    let k := locate F P hi
    have hsubset : Y.carrier i ⊆
        ((convexFactorization F P).inducedShading Y).carrier (some k) := by
      intro x hx
      apply ((convexFactorization F P).mem_inducedShading_carrier_iff
        Y (some k) x).2
      refine ⟨?_, i, ?_, hx⟩
      · change some k ∈ occurrenceIndices F P
        simp [occurrenceIndices]
      · change i ∈ (indexFactorization F P).fiber (some k)
        rw [indexFactorization_fiber_eq_blockAt]
        exact mem_blockAt_locate F P hi
    exact nonpos_iff_eq_zero.mp ((measure_mono hsubset).trans_eq (hterm k))
  apply hsource
  unfold Shading.shadingMass
  exact Finset.sum_eq_zero fun i _hi => hcarrier i

#print axioms
  selectedOccurrenceOuterShading_univ_mass_ne_zero_of_active_eq_univ

end
end Family8SelectedOccurrenceOuterMassPositiveV2
