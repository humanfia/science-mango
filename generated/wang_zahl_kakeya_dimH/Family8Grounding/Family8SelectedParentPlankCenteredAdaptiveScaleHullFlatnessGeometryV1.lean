import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleFlatnessTransportV3
import Family8Grounding.Family8SelectedParentBucketMapDistortionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

theorem exists_unit_inner_eq_zero (v : Space) (hv : v ≠ 0) :
    ∃ n : Space, ‖n‖ = 1 ∧ inner ℝ n v = 0 := by
  let K : Submodule ℝ Space := ℝ ∙ v
  have hdimSpace : Module.finrank ℝ Space = 3 := by
    simp [Space]
  let _ : Fact (Module.finrank ℝ Space = 2 + 1) :=
    ⟨by simp [hdimSpace]⟩
  have hdim : Module.finrank ℝ K.orthogonal = 2 := by
    simpa [K] using
      (Submodule.finrank_orthogonal_span_singleton (n := 2) hv)
  have hpos : 0 < Module.finrank ℝ K.orthogonal := by omega
  have hex : ∃ z : K.orthogonal, z ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero).mp hpos
  obtain ⟨z, hz⟩ := hex
  let n : Space := ‖(z : Space)‖⁻¹ • (z : Space)
  have hznorm : 0 < ‖(z : Space)‖ := norm_pos_iff.mpr (by
    intro hzero
    apply hz
    exact Subtype.ext hzero)
  refine ⟨n, ?_, ?_⟩
  · dsimp only [n]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hznorm), inv_mul_cancel₀ hznorm.ne']
  · dsimp only [n]
    rw [real_inner_smul_left]
    have hzmem : (z : Space) ∈ (ℝ ∙ v).orthogonal := z.property
    have hzorth : inner ℝ (z : Space) v = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_left).mp hzmem
    rw [hzorth, mul_zero]

theorem exists_half_le_abs_inner_frame
    (B : FrameBox) (n : Space) (hnorm : ‖n‖ = 1) :
    ∃ i : Fin 3, (1 / 2 : Real) ≤ |inner ℝ n (B.frame i)| := by
  by_contra hnone
  rw [not_exists] at hnone
  have hsmall (i : Fin 3) :
      |inner ℝ (B.frame i) n| < (1 / 2 : Real) := by
    have h := lt_of_not_ge (hnone i)
    simpa only [real_inner_comm] using h
  have h0 := abs_lt.mp (hsmall 0)
  have h1 := abs_lt.mp (hsmall 1)
  have h2 := abs_lt.mp (hsmall 2)
  have hparseval := B.frame.sum_sq_inner_right n
  rw [Fin.sum_univ_three, hnorm] at hparseval
  norm_num at h0 h1 h2 hparseval
  nlinarith [sq_nonneg (inner ℝ (B.frame 0) n),
    sq_nonneg (inner ℝ (B.frame 1) n),
    sq_nonneg (inner ℝ (B.frame 2) n)]

theorem BoxDimensionsCertificate.exists_side_le_of_subset_centeredSlab
    {C : NNReal} {side : Fin 3 → NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (n : Space) (hnorm : ‖n‖ = 1) (center : Real) (w : NNReal)
    (hslab : ∀ x, x ∈ (K : Set Space) →
      |inner ℝ n x - center| ≤ (w : Real)) :
    ∃ i : Fin 3, side i ≤ 4 * C * w := by
  let D := cert.box.rescale C⁻¹
  obtain ⟨i, hi⟩ := exists_half_le_abs_inner_frame D n hnorm
  have hposK : D.positiveFacePoint i ∈ (K : Set Space) :=
    cert.inner_le (D.positiveFacePoint_mem_carrier i)
  have hnegK : D.negativeFacePoint i ∈ (K : Set Space) :=
    cert.inner_le (D.negativeFacePoint_mem_carrier i)
  have hpos := hslab (D.positiveFacePoint i) hposK
  have hneg := hslab (D.negativeFacePoint i) hnegK
  have hproj :
      |inner ℝ n (D.positiveFacePoint i) -
          inner ℝ n (D.negativeFacePoint i)| ≤ 2 * (w : Real) := by
    calc
      |inner ℝ n (D.positiveFacePoint i) -
          inner ℝ n (D.negativeFacePoint i)| =
          |(inner ℝ n (D.positiveFacePoint i) - center) -
            (inner ℝ n (D.negativeFacePoint i) - center)| := by ring
      _ ≤ |inner ℝ n (D.positiveFacePoint i) - center| +
          |inner ℝ n (D.negativeFacePoint i) - center| := by
        have h := abs_sub_le
          (inner ℝ n (D.positiveFacePoint i) - center)
          (0 : Real)
          (inner ℝ n (D.negativeFacePoint i) - center)
        simpa only [sub_zero, zero_sub, abs_neg] using h
      _ ≤ (w : Real) + (w : Real) := add_le_add hpos hneg
      _ = 2 * (w : Real) := by ring
  have hdiff :
      inner ℝ n (D.positiveFacePoint i) -
          inner ℝ n (D.negativeFacePoint i) =
        (D.side i : Real) * inner ℝ n (D.frame i) := by
    simp only [FrameBox.positiveFacePoint, FrameBox.negativeFacePoint,
      inner_add_right, inner_sub_right, real_inner_smul_right]
    ring
  rw [hdiff, abs_mul,
    abs_of_nonneg (show (0 : Real) ≤ (D.side i : Real) by positivity)] at hproj
  have hhalf : (D.side i : Real) / 2 ≤
      (D.side i : Real) * |inner ℝ n (D.frame i)| := by
    have hside : 0 ≤ (D.side i : Real) := by positivity
    nlinarith
  have hscaled : (D.side i : Real) / 2 ≤ 2 * (w : Real) :=
    hhalf.trans hproj
  have hC : (0 : Real) < (C : Real) := by
    exact_mod_cast (zero_lt_one.trans_le cert.one_le)
  have hraw : (C : Real)⁻¹ * (side i : Real) ≤ 4 * (w : Real) := by
    dsimp only [D] at hscaled
    simp only [FrameBox.rescale_side, cert.side_eq,
      NNReal.coe_mul, NNReal.coe_inv] at hscaled
    linarith
  have hsideReal : (side i : Real) ≤
      (C : Real) * (4 * (w : Real)) :=
    (inv_mul_le_iff₀ hC).mp hraw
  refine ⟨i, ?_⟩
  exact_mod_cast (show (side i : Real) ≤
      ((4 * C * w : NNReal) : Real) by
    norm_num only [NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith)

theorem affineEquiv_sub_eq_linear
    (e : Space ≃ᵃ[ℝ] Space) (x y : Space) :
    e x - e y = e.linear (x - y) := by
  simpa only [vsub_eq_sub, AffineEquiv.coe_toAffineMap,
    AffineEquiv.linear_toAffineMap, LinearEquiv.coe_coe] using
      (e.toAffineMap.linearMap_vsub x y).symm

theorem contractedJohnAffineEquiv_linear_norm_le_three_mul
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (m : NNReal) (hm : 0 < m) (hside : ∀ j, m ≤ J.side j)
    (r : NNReal) (hr : 0 < r) (v : Space) :
    ‖(contractedJohnAffineEquiv J r hr).linear v‖ ≤
      (((3 * r / m : NNReal) : Real)) * ‖v‖ := by
  have hJ :=
    Family8SelectedParentBucketMapDistortionV1.PositiveJohnFrame.linear_norm_le_three_div_of_side_lower
      J m hm hside v
  change ‖(r : Real) • J.affineEquiv.linear v‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (show (0 : Real) < (r : Real) by exact_mod_cast hr)]
  calc
    (r : Real) * ‖J.affineEquiv.linear v‖ ≤
        (r : Real) * ((3 / (m : Real)) * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (((3 * r / m : NNReal) : Real)) * ‖v‖ := by
      norm_num [NNReal.coe_div, NNReal.coe_mul]
      ring

theorem exists_contractedJohn_tube_centeredSlab
    {H : ConvexBody Space} {rho : NNReal}
    (J : PositiveJohnFrame H)
    (m : NNReal) (hm : 0 < m) (hside : ∀ j, m ≤ J.side j)
    (r : NNReal) (hr : 0 < r) (T : Tube rho) :
    let e := contractedJohnAffineEquiv J r hr
    ∃ n : Space, ‖n‖ = 1 ∧
      ∀ y, y ∈ e '' T.carrier →
        |inner ℝ n y - inner ℝ n (e T.axis.base)| ≤
          ((((3 * r / m) * rho : NNReal) : Real)) := by
  dsimp only
  let e := contractedJohnAffineEquiv J r hr
  have hdir : e.linear T.axis.direction ≠ 0 := by
    intro hzero
    have hzero' : e.linear T.axis.direction = e.linear 0 := by
      simpa only [map_zero] using hzero
    have hsource : T.axis.direction = 0 := e.linear.injective hzero'
    have hnorm := T.axis.norm_direction
    rw [hsource, norm_zero] at hnorm
    norm_num at hnorm
  obtain ⟨n, hn, hnorth⟩ :=
    exists_unit_inner_eq_zero (e.linear T.axis.direction) hdir
  refine ⟨n, hn, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (rho : Real) by positivity)] at hx
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨a, haAxis, hxa⟩ := hx
  rw [T.axis.carrier_eq_image] at haAxis
  obtain ⟨t, _ht, rfl⟩ := haAxis
  let a : Space := T.axis.base + t • T.axis.direction
  have hmap : e x - e a = e.linear (x - a) :=
    affineEquiv_sub_eq_linear e x a
  have haxis : e a - e T.axis.base =
      t • e.linear T.axis.direction := by
    rw [affineEquiv_sub_eq_linear]
    have ha : a - T.axis.base = t • T.axis.direction := by
      dsimp only [a]
      module
    rw [ha, map_smul]
  have hsplit : e x - e T.axis.base =
      (e x - e a) + (e a - e T.axis.base) := by abel
  have hinner :
      inner ℝ n (e x) - inner ℝ n (e T.axis.base) =
        inner ℝ n (e.linear (x - a)) := by
    rw [← inner_sub_right, hsplit, inner_add_right, hmap, haxis,
      real_inner_smul_right, hnorth, mul_zero, add_zero]
  rw [hinner]
  have hinnerNorm := abs_real_inner_le_norm n (e.linear (x - a))
  rw [hn, one_mul] at hinnerNorm
  have hlinear :=
    contractedJohnAffineEquiv_linear_norm_le_three_mul
      J m hm hside r hr (x - a)
  have hxaNorm : ‖x - a‖ ≤ (rho : Real) := by
    simpa only [a, dist_eq_norm] using hxa
  calc
    |inner ℝ n (e.linear (x - a))| ≤ ‖e.linear (x - a)‖ := hinnerNorm
    _ ≤ (((3 * r / m : NNReal) : Real)) * ‖x - a‖ := hlinear
    _ ≤ (((3 * r / m : NNReal) : Real)) * (rho : Real) := by
      gcongr
    _ = ((((3 * r / m) * rho : NNReal) : Real)) := by
      norm_num [NNReal.coe_mul]

def hullShortestSide {H : ConvexBody Space}
    (J : PositiveJohnFrame H) : NNReal :=
  min (J.side 0) (min (J.side 1) (J.side 2))

theorem hullShortestSide_pos {H : ConvexBody Space}
    (J : PositiveJohnFrame H) : 0 < hullShortestSide J := by
  simp only [hullShortestSide, lt_min_iff]
  exact ⟨J.side_pos 0, J.side_pos 1, J.side_pos 2⟩

theorem hullShortestSide_le {H : ConvexBody Space}
    (J : PositiveJohnFrame H) (i : Fin 3) :
    hullShortestSide J ≤ J.side i := by
  fin_cases i <;> simp [hullShortestSide]

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedParentContracted_transverseShort_le_hullRatio
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    let e := contractedJohnAffineEquiv J r hr
    let side := selectedParentLongRelabeledSide e S
      (blockAt S.activeCoarseFamily P k).fiber hrho p
    min (side 0) (side 1) ≤
      3456 * r * rho / hullShortestSide J := by
  dsimp only
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let T := S.coarse.tubes p.1.1
  let side := selectedParentLongRelabeledSide e S B hrho p
  let m := hullShortestSide J
  let w : NNReal := (3 * r / m) * rho
  have hm : 0 < m := hullShortestSide_pos J
  have hmSide : ∀ j, m ≤ J.side j := hullShortestSide_le J
  obtain ⟨n, hn, hslab⟩ :=
    exists_contractedJohn_tube_centeredSlab J m hm hmSide r hr T
  let cert := selectedParentLongRelabeledCertificate e S B hrho p
  have hslabK : ∀ y, y ∈
      (selectedParentAffineFamily e S B p : Set Space) →
      |inner ℝ n y - inner ℝ n (e T.axis.base)| ≤ (w : Real) := by
    intro y hy
    have hy' : y ∈ e '' T.carrier := by
      rw [selectedParentAffineFamily_apply] at hy
      simpa [T, FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
        UniformTubeFamily.bodyFamily] using hy
    simpa only [e] using hslab y hy'
  obtain ⟨i, hi⟩ :=
    BoxDimensionsCertificate.exists_side_le_of_subset_centeredSlab
      cert n hn (inner ℝ n (e T.axis.base)) w hslabK
  have hmin : min (side 0) (side 1) ≤ side i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans
        (selectedParentLongRelabeledSide_le_two e S B hrho p 0)
  have hconst : 4 * 288 * w = 3456 * r * rho / m := by
    dsimp only [w]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hconst] at hi
  exact hmin.trans hi

#print axioms exists_unit_inner_eq_zero
#print axioms exists_half_le_abs_inner_frame
#print axioms BoxDimensionsCertificate.exists_side_le_of_subset_centeredSlab
#print axioms affineEquiv_sub_eq_linear
#print axioms contractedJohnAffineEquiv_linear_norm_le_three_mul
#print axioms exists_contractedJohn_tube_centeredSlab
#print axioms hullShortestSide_pos
#print axioms hullShortestSide_le
#print axioms selectedParentContracted_transverseShort_le_hullRatio

end
end Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
