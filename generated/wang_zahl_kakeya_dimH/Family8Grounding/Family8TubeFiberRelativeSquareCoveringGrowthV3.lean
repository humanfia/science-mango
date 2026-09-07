import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Submission.Kakeya.ConvexFactoring.TubeSpecificLocalGrowth
import Mathlib.Tactic

/-!
# Sharp relative-square covering growth into the uncut parent neighborhood, V3

V1 had stale module paths and V2 was frozen only by the unused-section-
variable linter.  This clean successor preserves the verified proofs and
disables that interface-only linter.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8TubeFiberRelativeSquareCoveringGrowthV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The exact coefficient obtained by summing the per-tube G4 constant over
at most `M` fine tubes in one parent fibre. -/
def tubeFiberRelativeSquareGrowth (M : Nat) : ENNReal :=
  (M : ENNReal) * 48

/-- Tube G4, summed over the literal factorization fibre, gives sharp
`rho^2`-to-`delta^2` covering growth into the neighborhood recomputed from
the same shading. -/
theorem hasFiberCoveringGrowth_of_fiber_card_le
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily)
    (M : Nat)
    (hcard : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    HasFiberCoveringGrowth P.asConvexFactorization Z (rho : Real)
      ((rho : ENNReal) ^ 2)
      (tubeFiberRelativeSquareGrowth M * (delta : ENNReal) ^ 2) := by
  intro k hk
  unfold fiberShadingMass
  rw [Finset.sum_mul]
  calc
    (∑ i ∈ P.index.fiber k,
        volume (Z.carrier i) * (rho : ENNReal) ^ 2) ≤
        ∑ _i ∈ P.index.fiber k,
          48 * (delta : ENNReal) ^ 2 *
            volume ((P.asConvexFactorization.neighborhoodInducedShading
              Z (rho : Real)).carrier k) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiFine : i ∈ P.index.fine :=
        P.index.fiber_subset_fine k hi
      have hparent : P.index.parent i = k :=
        (P.index.mem_fiber i k).1 hi |>.2
      have hAfine : Z.carrier i ⊆ (fine.tubes i).carrier := by
        intro x hx
        exact Z.carrier_subset i hx
      have hAcoarse : Z.carrier i ⊆ (coarse.tubes k).carrier := by
        intro x hx
        have hxParent := P.carrier_subset i hiFine (Z.carrier_subset i hx)
        simpa only [hparent] using hxParent
      obtain ⟨_packing, _hcapture, hgrowth⟩ :=
        exists_packingCertificate_with_explicit_tubeCrossGrowth
          (A := Z.carrier i) (fine.tubes i) (coarse.tubes k)
          hAfine hAcoarse hdelta hrho P.scale_le
      have hpieceFiber :
          Z.carrier i ⊆
            P.asConvexFactorization.fiberShadedUnion Z k := by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
      have hlocalSubset :
          (coarse.tubes k).carrier ∩
              Metric.thickening (rho : Real) (Z.carrier i) ⊆
            (P.asConvexFactorization.neighborhoodInducedShading
              Z (rho : Real)).carrier k := by
        intro x hx
        exact ⟨hx.1,
          Metric.thickening_subset_of_subset
            (rho : Real) hpieceFiber hx.2⟩
      exact hgrowth.trans
        (mul_le_mul' le_rfl (measure_mono hlocalSubset))
    _ = ((P.index.fiber k).card : ENNReal) *
        (48 * (delta : ENNReal) ^ 2 *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Z (rho : Real)).carrier k)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ENNReal) *
        (48 * (delta : ENNReal) ^ 2 *
          volume ((P.asConvexFactorization.neighborhoodInducedShading
            Z (rho : Real)).carrier k)) := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast hcard k hk
    _ = (tubeFiberRelativeSquareGrowth M * (delta : ENNReal) ^ 2) *
        volume ((P.asConvexFactorization.neighborhoodInducedShading
          Z (rho : Real)).carrier k) := by
      unfold tubeFiberRelativeSquareGrowth
      ac_rfl

/-- The partition's stored upper branching bound discharges the fibre-card
premise without changing the shading or neighborhood object. -/
theorem hasFiberCoveringGrowth_of_partition_branching
    (P : CoarseTubePartition fine coarse)
    (Z : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    HasFiberCoveringGrowth P.asConvexFactorization Z (rho : Real)
      ((rho : ENNReal) ^ 2)
      (tubeFiberRelativeSquareGrowth (P.branchingLoss * P.branching) *
        (delta : ENNReal) ^ 2) := by
  exact hasFiberCoveringGrowth_of_fiber_card_le P Z
    (P.branchingLoss * P.branching)
    (fun k hk => P.fiber_card_le_loss_mul_branching k hk)
    hdelta hrho

#print axioms tubeFiberRelativeSquareGrowth
#print axioms hasFiberCoveringGrowth_of_fiber_card_le
#print axioms hasFiberCoveringGrowth_of_partition_branching

end
end Family8TubeFiberRelativeSquareCoveringGrowthV3
