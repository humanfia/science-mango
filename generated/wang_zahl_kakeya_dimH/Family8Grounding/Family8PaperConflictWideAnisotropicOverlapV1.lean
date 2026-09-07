import Family8Grounding.Family8CommonPointTubePackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8PaperConflictWideAnisotropicOverlapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1

noncomputable section

/-!
# An overlap core with a wide longitudinal anchor window

Paper-conflict neighbours of a fixed tube need not pass through its
midpoint, so the common-point overlap lemma's `51/100` longitudinal window
is unavailable.  The direction coherence coming from full two-fold
containment is, however, much stronger than the old `delta/100` direction
mesh.  This file spends that extra accuracy to allow the honest window
`|a_T| <= 2`.
-/

/-- The crossed core transfers when the longitudinal anchor coordinate is
only bounded at unit scale, provided the direction mesh is `delta/1000`.
The numerical radial error is `delta/80`, still well inside the core's
`3 delta / 50` margin. -/
theorem commonPointPrism_subset_other_carrier_of_wide_anisotropic_close
    {delta : NNReal} (x0 : Space) (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction) (swap : Bool)
    (haT : |tubePointLongitudinal x0 T| ≤ 2)
    (hlong : |tubePointLongitudinal x0 T - tubePointLongitudinal x0 U| ≤
      (1 : Real) / 400)
    (htrans : dist (tubePointTransverse x0 T) (tubePointTransverse x0 U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 1000) :
    (commonPointPrism T frame swap).carrier ⊆ U.carrier := by
  intro z hz
  obtain ⟨t, ht, hzT⟩ :=
    commonPointPrism_exists_axisPoint T frame hframe swap z hz
  let aT : Real := tubePointLongitudinal x0 T
  let aU : Real := tubePointLongitudinal x0 U
  let eT : Space := tubePointTransverse x0 T
  let eU : Space := tubePointTransverse x0 U
  let tU : Real := t + (aT - aU)
  have hlong' : |aT - aU| ≤ (1 : Real) / 400 := by
    simpa only [aT, aU] using hlong
  have hlongBounds := abs_le.mp hlong'
  have htU : tU ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp only [tU] <;> norm_num at * <;>
      linarith [ht.1, ht.2, hlongBounds.1, hlongBounds.2]
  have htcenter : |t - (2 : Real)⁻¹| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  have haT' : |aT| ≤ 2 := by
    simpa only [aT] using haT
  have hcoeff :
      |aT + (t - (2 : Real)⁻¹)| ≤ (5 : Real) / 2 := by
    calc
      |aT + (t - (2 : Real)⁻¹)| ≤
          |aT| + |t - (2 : Real)⁻¹| := abs_add_le _ _
      _ ≤ 2 + (2 : Real)⁻¹ := add_le_add haT' htcenter
      _ = (5 : Real) / 2 := by norm_num
  have hmidT :
      tubeAxisMidpoint T = x0 + aT • T.axis.direction + eT := by
    simpa only [aT, eT] using tubeAxisMidpoint_eq_point_decomposition x0 T
  have hmidU :
      tubeAxisMidpoint U = x0 + aU • U.axis.direction + eU := by
    simpa only [aU, eU] using tubeAxisMidpoint_eq_point_decomposition x0 U
  have hpointT :
      T.axis.base + t • T.axis.direction =
        tubeAxisMidpoint T + (t - (2 : Real)⁻¹) • T.axis.direction := by
    simp only [tubeAxisMidpoint]
    module
  have hpointU :
      U.axis.base + tU • U.axis.direction =
        tubeAxisMidpoint U + (tU - (2 : Real)⁻¹) • U.axis.direction := by
    simp only [tubeAxisMidpoint]
    module
  have haxisVec :
      (T.axis.base + t • T.axis.direction) -
          (U.axis.base + tU • U.axis.direction) =
        (aT + (t - (2 : Real)⁻¹)) •
            (T.axis.direction - U.axis.direction) + (eT - eU) := by
    rw [hpointT, hpointU, hmidT, hmidU]
    dsimp only [tU]
    module
  have hscaled :
      |aT + (t - (2 : Real)⁻¹)| *
          dist T.axis.direction U.axis.direction ≤
        (5 : Real) / 2 * ((delta : Real) / 1000) := by
    exact mul_le_mul hcoeff hdir dist_nonneg (by norm_num)
  have haxis :
      dist (T.axis.base + t • T.axis.direction)
          (U.axis.base + tU • U.axis.direction) ≤
        (1 : Real) / 80 * (delta : Real) := by
    rw [dist_eq_norm, haxisVec]
    calc
      ‖(aT + (t - (2 : Real)⁻¹)) •
          (T.axis.direction - U.axis.direction) + (eT - eU)‖ ≤
          ‖(aT + (t - (2 : Real)⁻¹)) •
            (T.axis.direction - U.axis.direction)‖ + ‖eT - eU‖ :=
        norm_add_le _ _
      _ = |aT + (t - (2 : Real)⁻¹)| *
          dist T.axis.direction U.axis.direction + dist eT eU := by
        simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm]
      _ ≤ (5 : Real) / 2 * ((delta : Real) / 1000) +
          (delta : Real) / 100 := add_le_add hscaled htrans
      _ = (1 : Real) / 80 * (delta : Real) := by ring
  have hzU :
      dist z (U.axis.base + tU • U.axis.direction) ≤ (delta : Real) := by
    calc
      dist z (U.axis.base + tU • U.axis.direction) ≤
          dist z (T.axis.base + t • T.axis.direction) +
            dist (T.axis.base + t • T.axis.direction)
              (U.axis.base + tU • U.axis.direction) := dist_triangle _ _ _
      _ ≤ (47 : Real) / 50 * (delta : Real) +
          (1 : Real) / 80 * (delta : Real) := add_le_add hzT haxis
      _ ≤ (delta : Real) := by
        have hdelta : 0 ≤ (delta : Real) := NNReal.zero_le_coe
        nlinarith
  exact Metric.mem_cthickening_of_dist_le
    z (U.axis.base + tU • U.axis.direction) (delta : Real) U.axis.carrier
    (U.axis.mem_carrier_of_mem_Icc htU) hzU

/-- The full crossed core transfers under the wide-anchor estimates. -/
theorem commonPointCrossPrism_subset_other_carrier_of_wide_anisotropic_close
    {delta : NNReal} (x0 : Space) (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (haT : |tubePointLongitudinal x0 T| ≤ 2)
    (hlong : |tubePointLongitudinal x0 T - tubePointLongitudinal x0 U| ≤
      (1 : Real) / 400)
    (htrans : dist (tubePointTransverse x0 T) (tubePointTransverse x0 U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 1000) :
    commonPointCrossPrism T frame ⊆ U.carrier := by
  exact union_subset
    (commonPointPrism_subset_other_carrier_of_wide_anisotropic_close
      x0 T U frame hframe false haT hlong htrans hdir)
    (commonPointPrism_subset_other_carrier_of_wide_anisotropic_close
      x0 T U frame hframe true haT hlong htrans hdir)

/-- Wide-anchor anisotropic closeness contradicts the actual half-overlap
essential-distinctness predicate. -/
theorem not_essentiallyDistinct_of_wide_anisotropic_close
    {delta : NNReal} (x0 : Space) (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (haT : |tubePointLongitudinal x0 T| ≤ 2)
    (hlong : |tubePointLongitudinal x0 T - tubePointLongitudinal x0 U| ≤
      (1 : Real) / 400)
    (htrans : dist (tubePointTransverse x0 T) (tubePointTransverse x0 U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 1000) :
    ¬ EssentiallyDistinct T U := by
  intro hdistinct
  have hcrossInter :
      commonPointCrossPrism T frame ⊆ T.carrier ∩ U.carrier := fun z hz =>
    ⟨commonPointCrossPrism_subset_carrier T frame hframe hz,
      commonPointCrossPrism_subset_other_carrier_of_wide_anisotropic_close
        x0 T U frame hframe haT hlong htrans hdir hz⟩
  have hmeasure :
      volume (commonPointCrossPrism T frame) ≤
        volume (T.carrier ∩ U.carrier) := measure_mono hcrossInter
  have hstrict := half_max_volume_lt_volume_commonPointCrossPrism
    T U frame hdeltaPos hdeltaSmall
  exact (not_lt_of_ge hdistinct) (hstrict.trans_le hmeasure)

#print axioms commonPointPrism_subset_other_carrier_of_wide_anisotropic_close
#print axioms commonPointCrossPrism_subset_other_carrier_of_wide_anisotropic_close
#print axioms not_essentiallyDistinct_of_wide_anisotropic_close

end

end Family8PaperConflictWideAnisotropicOverlapV1
