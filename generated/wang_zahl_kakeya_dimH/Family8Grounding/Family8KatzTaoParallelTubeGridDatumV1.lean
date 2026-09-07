import Family8Grounding.Family8KatzTaoParallelTubeGridV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8KatzTaoParallelTubeGridDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoNegativeExponentObstructionV1
open Family8KatzTaoParallelTubeGridV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Finite actual data from the parallel-tube grid

For a positive natural number `n`, the radius is `1/(100n)` and consecutive
axes are separated by `4 delta`.  Thus all `n` closed carriers are
literally disjoint while remaining well inside the normalized unit ball.
-/

/-- Radius of the `n`-tube obstruction family. -/
def parallelGridDelta (n : Nat) : NNReal :=
  (100 * (n : NNReal))⁻¹

/-- Transverse offset of the `i`th axis. -/
def parallelGridOffset (n : Nat) (i : Fin n) : Real :=
  4 * (parallelGridDelta n : Real) * (i : Nat)

theorem parallelGridDelta_pos {n : Nat} (hn : 0 < n) :
    0 < parallelGridDelta n := by
  simp only [parallelGridDelta]
  positivity

theorem parallelGridDelta_mul_natCast {n : Nat} (hn : 0 < n) :
    parallelGridDelta n * (n : NNReal) = (100 : NNReal)⁻¹ := by
  have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    parallelGridDelta n * (n : NNReal) =
        (n : NNReal)⁻¹ * (n : NNReal) * (100 : NNReal)⁻¹ := by
      rw [parallelGridDelta, mul_inv_rev]
      ring
    _ = (100 : NNReal)⁻¹ := by
      rw [inv_mul_cancel₀ hn0, one_mul]

theorem parallelGridDelta_le_quarter {n : Nat} (hn : 0 < n) :
    parallelGridDelta n ≤ (1 / 4 : NNReal) := by
  have hnOne : (1 : NNReal) ≤ n := by exact_mod_cast hn
  calc
    parallelGridDelta n =
        parallelGridDelta n * 1 := by simp
    _ ≤ parallelGridDelta n * (n : NNReal) := by gcongr
    _ = (100 : NNReal)⁻¹ := parallelGridDelta_mul_natCast hn
    _ ≤ (1 / 4 : NNReal) := by
      rw [div_eq_mul_inv, one_mul]
      exact (inv_le_inv₀ (by norm_num) (by norm_num)).2 (by norm_num)

theorem abs_parallelGridOffset_le_quarter
    {n : Nat} (hn : 0 < n) (i : Fin n) :
    |parallelGridOffset n i| ≤ (1 / 4 : Real) := by
  have hi : (i : Nat) ≤ n := Nat.le_of_lt i.isLt
  have hoffsetNonneg : 0 ≤ parallelGridOffset n i := by
    unfold parallelGridOffset
    positivity
  have hscaleNN := parallelGridDelta_mul_natCast hn
  have hscale :
      (parallelGridDelta n : Real) * (n : Real) = (1 / 100 : Real) := by
    rw [show (1 / 100 : Real) = (((100 : NNReal)⁻¹) : Real) by norm_num [div_eq_mul_inv]]
    exact_mod_cast hscaleNN
  calc
    |parallelGridOffset n i| = parallelGridOffset n i := abs_of_nonneg hoffsetNonneg
    _ ≤
        4 * (parallelGridDelta n : Real) * (n : Real) := by
      unfold parallelGridOffset
      gcongr
    _ = 4 * (1 / 100 : Real) := by rw [mul_assoc, hscale]
    _ ≤ (1 / 4 : Real) := by norm_num

/-- Distinct finite indices have real absolute difference at least one. -/
theorem one_le_abs_fin_cast_sub
    {n : Nat} (i j : Fin n) (hij : i ≠ j) :
    (1 : Real) ≤ |((i : Nat) : Real) - ((j : Nat) : Real)| := by
  have hval : (i : Nat) ≠ (j : Nat) := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hstep : (i : Nat) + 1 ≤ (j : Nat) := Nat.succ_le_iff.mpr hlt
    have hstepReal :
        (((i : Nat) : Real) + 1) ≤ ((j : Nat) : Real) := by
      exact_mod_cast hstep
    rw [abs_of_nonpos]
    · linarith
    · linarith
  · have hstep : (j : Nat) + 1 ≤ (i : Nat) := Nat.succ_le_iff.mpr hgt
    have hstepReal :
        (((j : Nat) : Real) + 1) ≤ ((i : Nat) : Real) := by
      exact_mod_cast hstep
    rw [abs_of_nonneg]
    · linarith
    · linarith

theorem two_mul_delta_lt_offset_gap
    {n : Nat} (hn : 0 < n) (i j : Fin n) (hij : i ≠ j) :
    2 * (parallelGridDelta n : Real) <
      |parallelGridOffset n i - parallelGridOffset n j| := by
  have hd : 0 < (parallelGridDelta n : Real) := by
    exact_mod_cast parallelGridDelta_pos hn
  have hindex := one_le_abs_fin_cast_sub i j hij
  have hoffset :
      |parallelGridOffset n i - parallelGridOffset n j| =
        4 * (parallelGridDelta n : Real) *
          |((i : Nat) : Real) - ((j : Nat) : Real)| := by
    unfold parallelGridOffset
    rw [show
      4 * (parallelGridDelta n : Real) * (i : Nat) -
          4 * (parallelGridDelta n : Real) * (j : Nat) =
        (4 * (parallelGridDelta n : Real)) *
          (((i : Nat) : Real) - ((j : Nat) : Real)) by ring,
      abs_mul, abs_of_nonneg]
    positivity
  rw [hoffset]
  nlinarith [mul_le_mul_of_nonneg_left hindex (by positivity :
    0 ≤ 4 * (parallelGridDelta n : Real))]

/-- The explicit uniformly-presented tube family. -/
def parallelGridFamily (n : Nat) :
    UniformTubeFamily (parallelGridDelta n) (Fin n) where
  tubes i := parallelTube (parallelGridDelta n) (parallelGridOffset n i)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem parallelGridFamily_tubes (n : Nat) (i : Fin n) :
    (parallelGridFamily n).tubes i =
      parallelTube (parallelGridDelta n) (parallelGridOffset n i) := rfl

theorem parallelGridFamily_pairwiseDisjoint
    {n : Nat} (hn : 0 < n) :
    Set.Pairwise (Set.univ : Set (Fin n))
      (fun i j => Disjoint ((parallelGridFamily n).tubes i).carrier
        ((parallelGridFamily n).tubes j).carrier) := by
  intro i _hi j _hj hij
  exact parallelTube_carrier_disjoint_of_two_mul_lt_abs_sub
    (two_mul_delta_lt_offset_gap hn i j hij)

theorem parallelGridFamily_tube_subset_unitBall
    {n : Nat} (hn : 0 < n) (i : Fin n) :
    ((parallelGridFamily n).tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  exact parallelTube_carrier_subset_unitBall
    (abs_parallelGridOffset_le_quarter hn i)
    (parallelGridDelta_le_quarter hn)

theorem parallelGridFamily_familyVolume_pos
    {n : Nat} (hn : 0 < n) :
    0 < familyVolume (parallelGridFamily n).bodyFamily := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hi :
      0 < volume (((parallelGridFamily n).tubes i).carrier) :=
    Tube.volume_pos ((parallelGridFamily n).tubes i)
      (parallelGridDelta_pos hn)
  unfold familyVolume
  have hle :
      volume (((parallelGridFamily n).tubes i).carrier) ≤
        ∑ j, volume (((parallelGridFamily n).tubes j).carrier) :=
    Finset.single_le_sum (f := fun j : Fin n =>
      volume (((parallelGridFamily n).tubes j).carrier)) (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hi.trans_le (by simpa [UniformTubeFamily.bodyFamily,
    Tube.coe_body] using hle)

/-- Full-shaded actual datum carried by the explicit grid. -/
def parallelGridDatum (n : Nat) :
    ActualTubeDatum (parallelGridDelta n) (Fin n) where
  family := parallelGridFamily n
  shading := fullShading (parallelGridFamily n).bodyFamily

theorem parallelGridDatum_isAdmissible
    {n : Nat} (hn : 0 < n) :
    (parallelGridDatum n).IsAdmissible := by
  refine
    { delta_pos := parallelGridDelta_pos hn
      delta_le_half := (parallelGridDelta_le_quarter hn).trans (by
        rw [div_eq_mul_inv, one_mul]
        exact (inv_le_inv₀ (by norm_num) (by norm_num)).2 (by norm_num))
      contained_in_unit_ball := parallelGridFamily_tube_subset_unitBall hn
      pairwise_essentiallyDistinct := ?_ }
  intro i _hi j _hj hij
  exact essentiallyDistinct_of_carrier_disjoint
    (parallelGridFamily_pairwiseDisjoint hn
      (Set.mem_univ i) (Set.mem_univ j) hij)

theorem parallelGridDatum_density_eq_one
    {n : Nat} (hn : 0 < n) :
    (parallelGridDatum n).shading.shadingDensity = 1 := by
  exact fullShading_shadingDensity_eq_one _
    (parallelGridFamily_familyVolume_pos hn).ne'

theorem parallelGridDatum_averageMultiplicity_eq_one
    {n : Nat} (hn : 0 < n) :
    (parallelGridDatum n).shading.averageMultiplicity = 1 := by
  exact fullShading_averageMultiplicity_eq_one _
    (parallelGridFamily_pairwiseDisjoint hn)
    (parallelGridFamily_familyVolume_pos hn).ne'

theorem parallelGridDatum_katzTaoHypotheses
    {n : Nat} (hn : 0 < n) {eta : Real} (heta : 0 ≤ eta) :
    KatzTaoHypotheses (parallelGridDatum n) eta := by
  rw [katzTaoHypotheses_iff_density_and_isKatzTao]
  constructor
  · rw [parallelGridDatum_density_eq_one hn]
    apply ENNReal.rpow_le_one
    · exact_mod_cast (parallelGridDelta_le_quarter hn).trans
        (by exact_mod_cast (by norm_num : (1 / 4 : Real) ≤ 1))
    · exact heta
  · have hdisjoint :
        Set.Pairwise (Set.univ : Set (Fin n))
          (fun i j => Disjoint
            (((parallelGridFamily n).bodyFamily i : ConvexBody Space) : Set Space)
            (((parallelGridFamily n).bodyFamily j : ConvexBody Space) : Set Space)) := by
      simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
        parallelGridFamily_pairwiseDisjoint hn
    have hOne :
        IsKatzTao 1 (parallelGridFamily n).bodyFamily :=
      isKatzTao_one_of_pairwiseDisjoint _ hdisjoint
    have hdeltaOne : parallelGridDelta n ≤ 1 :=
      (parallelGridDelta_le_quarter hn).trans
        (by exact_mod_cast (by norm_num : (1 / 4 : Real) ≤ 1))
    have honeNN :
        (1 : NNReal) ≤ (parallelGridDelta n) ^ (-eta) :=
      NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos
        (parallelGridDelta_pos hn) hdeltaOne (by linarith)
    have hone :
        (1 : ENNReal) ≤ (parallelGridDelta n : ENNReal) ^ (-eta) := by
      rw [← ENNReal.coe_rpow_of_ne_zero (parallelGridDelta_pos hn).ne']
      exact_mod_cast honeNN
    exact hOne.mono hone

#print axioms parallelGridFamily_pairwiseDisjoint
#print axioms parallelGridFamily_tube_subset_unitBall
#print axioms parallelGridFamily_familyVolume_pos
#print axioms parallelGridDatum_isAdmissible
#print axioms parallelGridDatum_averageMultiplicity_eq_one
#print axioms parallelGridDatum_katzTaoHypotheses

end
end Family8KatzTaoParallelTubeGridDatumV1
