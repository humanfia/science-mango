import Family8Grounding.Family8StickyShadingAwareSelectedMassPopularFiberMassV1
import Mathlib.Tactic

/-!
# Average transport to the actual mass-popular Sticky fibre

The mass-retaining parent chosen by the shading-aware selector also controls
the active source average.  The only extra fact is the literal inclusion of
that whole fibre's shaded union in the active-fine shaded union.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareSelectedMassPopularFiberAverageV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareSelectedMassPopularFiberMassV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The same maximum-mass parent selected in the actual logarithmic bucket
controls active-fine average multiplicity by its literal whole-fibre average. -/
theorem exists_shadingAwareSelected_massPopular_wholeFiber_average
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    let selected := shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass
    let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
    ∃ k ∈ selected,
      (activeFineShading S Y).averageMultiplicity ≤
        ((retention : ENNReal) * (selected.card : ENNReal)) *
          (stickyFiberSourceShading S Y k).averageMultiplicity := by
  dsimp only
  let selected := shadingAwareSelectedParents
    S Y A hA0 hAtop hrho hactive hmass
  let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  obtain ⟨k, hk, hsourceMass⟩ :=
    exists_shadingAwareSelected_massPopular_wholeFiber_mass
      S Y A hA0 hAtop hrho hactive hmass
  have hactiveMass : (activeFineShading S Y).shadingMass =
      shadingMassOn Y S.activeFine := by
    unfold Shading.shadingMass activeFineShading shadingMassOn
    rw [← Finset.attach_eq_univ]
    exact Finset.sum_attach S.activeFine (fun i => volume (Y.carrier i))
  have hmass' : (activeFineShading S Y).shadingMass ≤
      ((retention : ENNReal) * (selected.card : ENNReal)) *
        (stickyFiberSourceShading S Y k).shadingMass := by
    rw [hactiveMass]
    simpa only [retention, selected, mul_assoc] using hsourceMass
  have hunion : (stickyFiberSourceShading S Y k).shadedUnion ⊆
      (activeFineShading S Y).shadedUnion := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hiActive : i.1 ∈ S.activeFine :=
      ((S.mem_fiber i.1 k).mp i.2).1
    exact Set.mem_iUnion.mpr ⟨⟨i.1, hiActive⟩, hxi⟩
  refine ⟨k, by simpa only [selected] using hk, ?_⟩
  unfold Shading.averageMultiplicity
  calc
    (activeFineShading S Y).shadingMass /
        volume (activeFineShading S Y).shadedUnion ≤
      (((retention : ENNReal) * (selected.card : ENNReal)) *
          (stickyFiberSourceShading S Y k).shadingMass) /
        volume (activeFineShading S Y).shadedUnion :=
      ENNReal.div_le_div_right hmass' _
    _ ≤ (((retention : ENNReal) * (selected.card : ENNReal)) *
          (stickyFiberSourceShading S Y k).shadingMass) /
        volume (stickyFiberSourceShading S Y k).shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = ((retention : ENNReal) * (selected.card : ENNReal)) *
        ((stickyFiberSourceShading S Y k).shadingMass /
          volume (stickyFiberSourceShading S Y k).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms exists_shadingAwareSelected_massPopular_wholeFiber_average

end
end Family8StickyShadingAwareSelectedMassPopularFiberAverageV1
