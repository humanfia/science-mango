import Submission.Kakeya.ConvexFactoring.TubeParentInducedDensity

/-!
# Heavy tube-parent composition

This module composes global active-fine density, heavy-parent selection, finite
parent-label pigeonholing, and the tube-specific parent-induced density bound.
The selected bucket retains active shaded mass within `2 * card β`, has one
fine witness with loss `2 * L` in every selected parent, and its induced coarse
shading has density at least `lambda / (1536 * L)`.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open HeavyParentSelection
open TubeParentInducedDensity

noncomputable section

namespace HeavyTubeComposition

variable {delta rho : NNReal} {ι κ : Type*}
  [DecidableEq ι] [DecidableEq κ]
variable {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}

/-- Heavy selection, one weighted parent-label bucket, and the tube-specific
parent estimate produce a selected coarse-family density bound.

The minimal positivity input is nonzero active fine shaded mass. Retention then
forces the selected parent bucket to be nonempty. The loss `L` enters the heavy
threshold and the fine witness `2 * L`, while the label cardinality appears
only in the separate mass-retention conclusion. No parentwise volume bound or
final density estimate is assumed. -/
theorem exists_heavyParentLabel_bucket_with_selected_density
    {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily)
    (lambda L : ℝ≥0∞) (label : κ → β)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hglobal :
      lambda * activeBodyMass P.asConvexFactorization ≤
        L * activeShadingMass P.asConvexFactorization Y)
    (hmass0 : activeShadingMass P.asConvexFactorization Y ≠ 0)
    (hdeltaPos : 0 < delta) (hrhoPos : 0 < rho)
    (hscale : delta ≤ rho) (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    ∃ b : β,
      let parents := dyadicFiber
        (heavyParents P.asConvexFactorization Y lambda L) label b
      WithinFactor (2 * Fintype.card β)
          (activeShadingMass P.asConvexFactorization Y)
          (∑ k ∈ parents,
            fiberShadingMass P.asConvexFactorization Y k) ∧
        parents.Nonempty ∧
        HasDenseFiberWitness P.asConvexFactorization Y
          parents lambda (2 * L) ∧
        lambda / (1536 * L) ≤
          (selectedCoarseShading
            (P.asConvexFactorization.neighborhoodInducedShading
              Y (rho : ℝ)) parents).shadingDensity := by
  obtain ⟨b, hretained⟩ :=
    exists_heavyParentLabel_bucket_withinFactor
      P.asConvexFactorization Y lambda L label hL0 hLtop hglobal
  let parents := dyadicFiber
    (heavyParents P.asConvexFactorization Y lambda L) label b
  change WithinFactor (2 * Fintype.card β)
    (activeShadingMass P.asConvexFactorization Y)
    (∑ k ∈ parents, fiberShadingMass P.asConvexFactorization Y k)
    at hretained
  have hparents : parents.Nonempty := by
    by_contra hnot
    have hempty : parents = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hle0 : activeShadingMass P.asConvexFactorization Y ≤ 0 := by
      simpa [WithinFactor, hempty] using hretained
    exact hmass0 (nonpos_iff_eq_zero.mp hle0)
  have hheavyWitness := heavyParents_haveDenseFiberWitness P Y lambda L
  have hwitness : HasDenseFiberWitness P.asConvexFactorization Y
      parents lambda (2 * L) := by
    intro k hk
    apply hheavyWitness k
    exact (mem_dyadicFiber
      (heavyParents P.asConvexFactorization Y lambda L) label b k).1 hk |>.1
  have hdensity := lambda_div_loss_le_selected_neighborhoodDensity
    P Y parents hparents lambda (2 * L) hwitness
      hdeltaPos hrhoPos hscale hrhoHalf
  have hconstant : (768 : ℝ≥0∞) * (2 * L) = 1536 * L := by ring
  refine ⟨b, ?_⟩
  dsimp only
  exact ⟨hretained, hparents, hwitness,
    by simpa only [hconstant] using hdensity⟩

end HeavyTubeComposition

end

end Submission.Kakeya.ConvexFactoring
