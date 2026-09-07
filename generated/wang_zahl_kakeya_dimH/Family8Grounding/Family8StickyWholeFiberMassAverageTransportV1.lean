import Family8Grounding.Family8StickyShadingAwareSelectedMassPopularFiberMassV1
import Mathlib.Tactic

/-!
# Sticky whole-fibre mass-to-average transport

This is the deterministic transport used after a parent has already been
selected: a source-to-fibre mass estimate implies the corresponding average
multiplicity estimate because the fibre shaded union is contained in the
active-fine shaded union.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyWholeFiberMassAverageTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Deterministic mass-to-average transport for one literal Sticky fibre. -/
theorem activeFine_averageMultiplicity_le_mul_stickyFiber_of_mass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) (loss : ENNReal)
    (hmass : shadingMassOn Y S.activeFine ≤
      loss * (stickyFiberSourceShading S Y k).shadingMass) :
    (activeFineShading S Y).averageMultiplicity ≤
      loss * (stickyFiberSourceShading S Y k).averageMultiplicity := by
  have hactiveMass : (activeFineShading S Y).shadingMass =
      shadingMassOn Y S.activeFine := by
    unfold Shading.shadingMass activeFineShading shadingMassOn
    rw [← Finset.attach_eq_univ]
    exact Finset.sum_attach S.activeFine (fun i => volume (Y.carrier i))
  have hmass' : (activeFineShading S Y).shadingMass ≤
      loss * (stickyFiberSourceShading S Y k).shadingMass := by
    rwa [hactiveMass]
  have hunion : (stickyFiberSourceShading S Y k).shadedUnion ⊆
      (activeFineShading S Y).shadedUnion := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hiActive : i.1 ∈ S.activeFine :=
      ((S.mem_fiber i.1 k).mp i.2).1
    exact Set.mem_iUnion.mpr ⟨⟨i.1, hiActive⟩, hxi⟩
  unfold Shading.averageMultiplicity
  calc
    (activeFineShading S Y).shadingMass /
        volume (activeFineShading S Y).shadedUnion ≤
      (loss * (stickyFiberSourceShading S Y k).shadingMass) /
        volume (activeFineShading S Y).shadedUnion :=
      ENNReal.div_le_div_right hmass' _
    _ ≤ (loss * (stickyFiberSourceShading S Y k).shadingMass) /
        volume (stickyFiberSourceShading S Y k).shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = loss * ((stickyFiberSourceShading S Y k).shadingMass /
        volume (stickyFiberSourceShading S Y k).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms activeFine_averageMultiplicity_le_mul_stickyFiber_of_mass

end
end Family8StickyWholeFiberMassAverageTransportV1
