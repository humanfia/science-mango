import FamilyStickyGrounding.FamilyStickyActualLatticePointBalanceV1
import FamilyStickyGrounding.FamilyStickyActualTubeTranslationV1

open Set
open scoped BigOperators NNReal InnerProductSpace

namespace FamilyStickyLatticeMotionRadiusV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyLatticeBoxPointCountV1
open FamilyStickyLatticeMultiBoxPointCountV1

noncomputable section

/-!
# Explicit motion radius of the product lattice

The point-count construction is useful for `randommotion` only after its
actual translations are controlled geometrically.  This module records a
fully explicit (deliberately loose) radius: the sum, over all test blocks and
all three coordinates, of `siteCount * spacing`.  Every product-lattice
translation lies in that radius, and an actual tube translated by such a
vector lies in the corresponding closed thickening of its original carrier.
-/

namespace MultiBoxLattice

variable {test : Type*} [Fintype test] [DecidableEq test]

/-- Crude `l1` radius of one oriented coordinate block. -/
def blockMotionRadius (L : MultiBoxLattice test) (K : test) : NNReal :=
  ∑ i, (L.siteCount K i : NNReal) * L.spacing K i

/-- Crude radius of the sum of all test-indexed lattice blocks. -/
def motionRadius (L : MultiBoxLattice test) : NNReal :=
  ∑ K, blockMotionRadius L K

/-- Every vector in one explicit coordinate block satisfies its declared
`l1` radius. -/
theorem norm_boxLatticeVector_le_blockMotionRadius
    (L : MultiBoxLattice test) (K : test) (g : L.Block K) :
    ‖boxLatticeVector (L.box K) (L.spacing K) g‖ <=
      (blockMotionRadius L K : Real) := by
  calc
    ‖boxLatticeVector (L.box K) (L.spacing K) g‖ =
        ‖∑ i, (((g i : Nat) : Real) * (L.spacing K i : Real)) •
          (L.box K).frame i‖ := rfl
    _ <= ∑ i, ‖(((g i : Nat) : Real) * (L.spacing K i : Real)) •
          (L.box K).frame i‖ := norm_sum_le _ _
    _ = ∑ i, ((g i : Nat) : Real) * (L.spacing K i : Real) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [norm_smul, (L.box K).frame.norm_eq_one]
    _ <= ∑ i, (L.siteCount K i : Real) * (L.spacing K i : Real) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply mul_le_mul_of_nonneg_right _ NNReal.zero_le_coe
      exact_mod_cast Nat.le_of_lt (g i).isLt
    _ = (blockMotionRadius L K : Real) := by
      simp [blockMotionRadius]

/-- Every global product choice has norm at most the explicit total motion
radius. -/
theorem norm_choiceVector_le_motionRadius
    (L : MultiBoxLattice test) (omega : L.Choice) :
    ‖L.choiceVector omega‖ <= (motionRadius L : Real) := by
  calc
    ‖L.choiceVector omega‖ =
        ‖∑ K, boxLatticeVector (L.box K) (L.spacing K) (omega K)‖ := rfl
    _ <= ∑ K, ‖boxLatticeVector (L.box K) (L.spacing K) (omega K)‖ :=
      norm_sum_le _ _
    _ <= ∑ K, (blockMotionRadius L K : Real) := by
      exact Finset.sum_le_sum fun K _ =>
        norm_boxLatticeVector_le_blockMotionRadius L K (omega K)
    _ = (motionRadius L : Real) := by simp [motionRadius]

#print axioms norm_boxLatticeVector_le_blockMotionRadius
#print axioms norm_choiceVector_le_motionRadius

end MultiBoxLattice

open MultiBoxLattice
/-- Any actual vector translation of a tube lies in the closed thickening by
the vector norm. -/
theorem translateTube_carrier_subset_cthickening_of_norm_le
    {delta : NNReal} (T : Tube delta) (v : Space) (r : NNReal)
    (hv : ‖v‖ <= (r : Real)) :
    (translateTube T v).carrier ⊆
      Metric.cthickening (r : Real) T.carrier := by
  intro y hy
  rw [translateTube_carrier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  apply Metric.closedBall_subset_cthickening hx (r : Real)
  rw [Metric.mem_closedBall]
  calc
    dist (v + x) x = ‖v‖ := by
      simpa only [add_comm] using (dist_self_add_left v x)
    _ <= (r : Real) := hv

namespace ActualTubeTranslationGrid.IsMultiBoxLatticeRealization

open FamilyStickyActualLatticePointBalanceV1.ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]
  {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {L : MultiBoxLattice (Fin G.testCard)}

/-- Every actual realized grid vector obeys the explicit product-lattice
motion radius. -/
theorem gridVector_norm_le_motionRadius
    (R : IsMultiBoxLatticeRealization G L) (g : translation) :
    ‖G.gridVector g‖ <= (motionRadius L : Real) := by
  rw [R.gridVector_eq]
  exact norm_choiceVector_le_motionRadius L (R.decode g)

/-- If the explicit product radius is below `r`, every actually translated
tube lies in the `r`-closed thickening of its original carrier. -/
theorem translateTube_carrier_subset_cthickening_of_motionRadius_le
    (R : IsMultiBoxLatticeRealization G L) (r : NNReal)
    (hradius : motionRadius L <= r) (i : tubeIndex) (g : translation) :
    (translateTube (G.tube i) (G.gridVector g)).carrier ⊆
      Metric.cthickening (r : Real) (G.tube i).carrier := by
  apply translateTube_carrier_subset_cthickening_of_norm_le
  exact (gridVector_norm_le_motionRadius R g).trans (by exact_mod_cast hradius)

#print axioms gridVector_norm_le_motionRadius
#print axioms translateTube_carrier_subset_cthickening_of_motionRadius_le

end ActualTubeTranslationGrid.IsMultiBoxLatticeRealization

end

end FamilyStickyLatticeMotionRadiusV1
