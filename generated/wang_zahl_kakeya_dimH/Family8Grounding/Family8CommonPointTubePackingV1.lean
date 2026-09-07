import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8SphereDirectionPackingV1
import Family8Grounding.Family8SphereDirectionPackingENNRealV1
import Family8Grounding.Family8PointwisePackingVolumeV1
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Family6FiniteMapFiberCapCardV1
import FamilyStickyRandomFiniteFloorParameterNetV1
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix BigOperators

namespace Family8CommonPointTubePackingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Family4GlobalExtremalUpstream

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-!
# A quantitative inner core for an actual tube

The usual certified inner box occupies too small a fraction of the coarse
outer-box volume to contradict the half-overlap definition of
`EssentiallyDistinct`.  We instead use the union of two crossed rectangular
prisms.  Their transverse half-widths are `3 delta / 4` and `11 delta / 20`;
the squared corner radius is only `173 delta^2 / 200`, leaving genuine room
for a later perturbation.  Their common axial length is `99 / 100`.
-/

/-- Side lengths of one of the two crossed inner prisms. -/
def commonPointPrismSide (delta : NNReal) (swap : Bool) : Fin 3 → NNReal :=
  if swap then
    ![(11 / 10 : NNReal) * delta, (3 / 2 : NNReal) * delta,
      (99 / 100 : NNReal)]
  else
    ![(3 / 2 : NNReal) * delta, (11 / 10 : NNReal) * delta,
      (99 / 100 : NNReal)]

/-- A long rectangular prism centered on the tube axis.  The Boolean swaps
the two transverse widths. -/
def commonPointPrism {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) (swap : Bool) : FrameBox where
  center := T.axis.base + (2 : Real)⁻¹ • T.axis.direction
  frame := frame
  side := commonPointPrismSide delta swap

@[simp]
theorem commonPointPrism_center {delta : NNReal} (T : Tube delta) (frame) (swap) :
    (commonPointPrism T frame swap).center =
      T.axis.base + (2 : Real)⁻¹ • T.axis.direction :=
  rfl

@[simp]
theorem commonPointPrism_frame {delta : NNReal} (T : Tube delta) (frame) (swap) :
    (commonPointPrism T frame swap).frame = frame :=
  rfl

@[simp]
theorem commonPointPrism_side {delta : NNReal} (T : Tube delta) (frame) (swap) :
    (commonPointPrism T frame swap).side = commonPointPrismSide delta swap :=
  rfl

private theorem sq_le_sq_of_abs_le {x a : Real} (h : |x| ≤ a) :
    x ^ 2 ≤ a ^ 2 := by
  have ha : 0 ≤ a := (abs_nonneg x).trans h
  have hsquare := (sq_le_sq₀ (abs_nonneg x) ha).2 h
  simpa only [sq_abs] using hsquare

/-- Every point of an arm has an axis witness at distance at most
`47 delta / 50`.  This is the quantitative radial margin used to transfer the
core between nearby tubes. -/
theorem commonPointPrism_exists_axisPoint
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction) (swap : Bool) :
    ∀ x ∈ (commonPointPrism T frame swap).carrier,
      ∃ t ∈ Set.Icc ((1 : Real) / 200) ((199 : Real) / 200),
        dist x (T.axis.base + t • T.axis.direction) ≤
          (47 : Real) / 50 * (delta : Real) := by
  intro x hx
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff] at hx
  let c : Space := T.axis.base + (2 : Real)⁻¹ • T.axis.direction
  let d : Fin 3 → Real := fun i =>
    ⟪frame i, x⟫_ℝ - ⟪frame i, c⟫_ℝ
  have hd2 : |d 2| ≤ (99 : Real) / 200 := by
    have h := hx (2 : Fin 3)
    cases swap <;>
      simp [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
        commonPointPrism, commonPointPrismSide] at h <;>
      dsimp only [d, c] <;>
      ring_nf at h ⊢ <;>
      exact h
  have htransverse :
      d 0 ^ 2 + d 1 ^ 2 ≤ (173 : Real) / 200 * (delta : Real) ^ 2 := by
    cases swap with
    | false =>
        have hd0 : |d 0| ≤ (3 : Real) / 4 * (delta : Real) := by
          have h := hx (0 : Fin 3)
          simp [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
            commonPointPrism, commonPointPrismSide] at h
          dsimp only [d, c]
          ring_nf at h ⊢
          exact h
        have hd1 : |d 1| ≤ (11 : Real) / 20 * (delta : Real) := by
          have h := hx (1 : Fin 3)
          simp [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
            commonPointPrism, commonPointPrismSide] at h
          dsimp only [d, c]
          ring_nf at h ⊢
          exact h
        have hd0sq := sq_le_sq_of_abs_le hd0
        have hd1sq := sq_le_sq_of_abs_le hd1
        nlinarith
    | true =>
        have hd0 : |d 0| ≤ (11 : Real) / 20 * (delta : Real) := by
          have h := hx (0 : Fin 3)
          simp [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
            commonPointPrism, commonPointPrismSide] at h
          dsimp only [d, c]
          ring_nf at h ⊢
          exact h
        have hd1 : |d 1| ≤ (3 : Real) / 4 * (delta : Real) := by
          have h := hx (1 : Fin 3)
          simp [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
            commonPointPrism, commonPointPrismSide] at h
          dsimp only [d, c]
          ring_nf at h ⊢
          exact h
        have hd0sq := sq_le_sq_of_abs_le hd0
        have hd1sq := sq_le_sq_of_abs_le hd1
        nlinarith
  let t : Real := (2 : Real)⁻¹ + d 2
  have ht : t ∈ Set.Icc ((1 : Real) / 200) ((199 : Real) / 200) := by
    rw [abs_le] at hd2
    constructor <;> dsimp only [t] <;> norm_num at * <;> linarith
  have hsum : ∑ i, d i • frame i = x - c := by
    simpa [d, inner_sub_right] using frame.sum_repr' (x - c)
  have hsum3 :
      d 0 • frame 0 + d 1 • frame 1 + d 2 • frame 2 = x - c := by
    simpa [Fin.sum_univ_three] using hsum
  have hxyvec :
      x - (T.axis.base + t • T.axis.direction) =
        d 0 • frame 0 + d 1 • frame 1 := by
    calc
      x - (T.axis.base + t • T.axis.direction) =
          (x - c) + (c - (T.axis.base + t • T.axis.direction)) := by
            abel
      _ = (d 0 • frame 0 + d 1 • frame 1 + d 2 • frame 2) +
          (c - (T.axis.base + t • T.axis.direction)) := by rw [hsum3]
      _ = d 0 • frame 0 + d 1 • frame 1 := by
        simp only [c, t]
        rw [hframe]
        module
  have horthogonal :
      ⟪d 0 • frame 0, d 1 • frame 1⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right,
      frame.inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)]
  have hnormSq :
      ‖d 0 • frame 0 + d 1 • frame 1‖ ^ 2 = d 0 ^ 2 + d 1 ^ 2 := by
    calc
      ‖d 0 • frame 0 + d 1 • frame 1‖ ^ 2 =
          ‖d 0 • frame 0‖ ^ 2 + ‖d 1 • frame 1‖ ^ 2 := by
            simpa only [pow_two] using
              norm_add_sq_eq_norm_sq_add_norm_sq_real horthogonal
      _ = d 0 ^ 2 + d 1 ^ 2 := by
        simp [norm_smul, frame.norm_eq_one, Real.norm_eq_abs, sq_abs]
  have hnormSqLe :
      ‖d 0 • frame 0 + d 1 • frame 1‖ ^ 2 ≤
        ((47 : Real) / 50 * (delta : Real)) ^ 2 := by
    rw [hnormSq]
    nlinarith [sq_nonneg (delta : Real)]
  have hradiusNonneg :
      0 ≤ (47 : Real) / 50 * (delta : Real) :=
    mul_nonneg (by norm_num) NNReal.zero_le_coe
  have hnorm :
      ‖d 0 • frame 0 + d 1 • frame 1‖ ≤
        (47 : Real) / 50 * (delta : Real) :=
    (sq_le_sq₀ (norm_nonneg _) hradiusNonneg).1 hnormSqLe
  have hdist :
      dist x (T.axis.base + t • T.axis.direction) ≤
        (47 : Real) / 50 * (delta : Real) := by
    simpa [dist_eq_norm, hxyvec] using hnorm
  exact ⟨t, ht, hdist⟩

/-- Each crossed prism is an actual subset of the metric tube. -/
theorem commonPointPrism_subset_carrier
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction) (swap : Bool) :
    (commonPointPrism T frame swap).carrier ⊆ T.carrier := by
  intro x hx
  obtain ⟨t, ht, hdist⟩ :=
    commonPointPrism_exists_axisPoint T frame hframe swap x hx
  have htUnit : t ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> nlinarith [ht.1, ht.2]
  exact Metric.mem_cthickening_of_dist_le
    x (T.axis.base + t • T.axis.direction) (delta : Real) T.axis.carrier
    (T.axis.mem_carrier_of_mem_Icc htUnit)
    (hdist.trans (by
      have hdelta : 0 ≤ (delta : Real) := NNReal.zero_le_coe
      nlinarith))

/-- The crossed union of the two inner prisms. -/
def commonPointCrossPrism {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) : Set Space :=
  (commonPointPrism T frame false).carrier ∪
    (commonPointPrism T frame true).carrier

/-- The whole crossed core lies in the actual tube. -/
theorem commonPointCrossPrism_subset_carrier
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction) :
    commonPointCrossPrism T frame ⊆ T.carrier := by
  exact union_subset
    (commonPointPrism_subset_carrier T frame hframe false)
    (commonPointPrism_subset_carrier T frame hframe true)

/-- The exact overlap box of the two crossed prisms. -/
def commonPointCoreSide (delta : NNReal) : Fin 3 → NNReal :=
  ![(11 / 10 : NNReal) * delta, (11 / 10 : NNReal) * delta,
    (99 / 100 : NNReal)]

/-- The rectangular overlap shared by both arms of the crossed core. -/
def commonPointCorePrism {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) : FrameBox where
  center := T.axis.base + (2 : Real)⁻¹ • T.axis.direction
  frame := frame
  side := commonPointCoreSide delta

/-- The two arms meet in exactly the smaller square-transverse prism. -/
theorem commonPointPrism_inter_eq_core
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    (commonPointPrism T frame false).carrier ∩
        (commonPointPrism T frame true).carrier =
      (commonPointCorePrism T frame).carrier := by
  rw [(commonPointPrism T frame false).carrier_eq_centeredCoordinateWindow,
    (commonPointPrism T frame true).carrier_eq_centeredCoordinateWindow,
    (commonPointCorePrism T frame).carrier_eq_centeredCoordinateWindow]
  ext x
  simp only [mem_inter_iff, mem_centeredCoordinateWindow_iff]
  constructor
  · rintro ⟨hfalse, htrue⟩ i
    fin_cases i
    · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
        commonPointPrism, commonPointPrismSide, commonPointCorePrism,
        commonPointCoreSide] using htrue (0 : Fin 3)
    · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
        commonPointPrism, commonPointPrismSide, commonPointCorePrism,
        commonPointCoreSide] using hfalse (1 : Fin 3)
    · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
        commonPointPrism, commonPointPrismSide, commonPointCorePrism,
        commonPointCoreSide] using hfalse (2 : Fin 3)
  · intro hcore
    constructor
    · intro i
      fin_cases i
      · have h := hcore (0 : Fin 3)
        simp [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
          commonPointPrism, commonPointPrismSide, commonPointCorePrism,
          commonPointCoreSide] at h ⊢
        nlinarith [(NNReal.zero_le_coe : 0 ≤ (delta : Real))]
      · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
          commonPointPrism, commonPointPrismSide, commonPointCorePrism,
          commonPointCoreSide] using hcore (1 : Fin 3)
      · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
          commonPointPrism, commonPointPrismSide, commonPointCorePrism,
          commonPointCoreSide] using hcore (2 : Fin 3)
    · intro i
      fin_cases i
      · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
          commonPointPrism, commonPointPrismSide, commonPointCorePrism,
          commonPointCoreSide] using hcore (0 : Fin 3)
      · have h := hcore (1 : Fin 3)
        simp [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
          commonPointPrism, commonPointPrismSide, commonPointCorePrism,
          commonPointCoreSide] at h ⊢
        nlinarith [(NNReal.zero_le_coe : 0 ≤ (delta : Real))]
      · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
          commonPointPrism, commonPointPrismSide, commonPointCorePrism,
          commonPointCoreSide] using hcore (2 : Fin 3)

/-- Exact volume of either arm of the crossed prism. -/
theorem volume_commonPointPrism
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) (swap : Bool) :
    volume (commonPointPrism T frame swap).carrier =
      (3267 / 2000 : ENNReal) * (delta : ENNReal) ^ 2 := by
  rw [FrameBox.volume_carrier, Fin.prod_univ_three]
  cases swap <;>
    simp [commonPointPrism, commonPointPrismSide, ENNReal.coe_mul,
      ENNReal.coe_div]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div]
    ring

/-- Exact volume of the overlap of the two arms. -/
theorem volume_commonPointCorePrism
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    volume (commonPointCorePrism T frame).carrier =
      (11979 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 := by
  rw [FrameBox.volume_carrier, Fin.prod_univ_three]
  simp [commonPointCorePrism, commonPointCoreSide, ENNReal.coe_mul,
    ENNReal.coe_div]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div]
  ring

/-- Exact volume of the crossed core.  Inclusion--exclusion is lossless here
because the overlap is the explicit core prism above. -/
theorem volume_commonPointCrossPrism
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) :
    volume (commonPointCrossPrism T frame) =
      (20691 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 := by
  have hIE := measure_union_add_inter
    (μ := volume) (commonPointPrism T frame false).carrier
    (commonPointPrism T frame true).measurableSet_carrier
  rw [commonPointPrism_inter_eq_core,
    volume_commonPointCorePrism, volume_commonPointPrism,
    volume_commonPointPrism] at hIE
  change volume (commonPointCrossPrism T frame) +
      (11979 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 =
    (3267 / 2000 : ENNReal) * (delta : ENNReal) ^ 2 +
      (3267 / 2000 : ENNReal) * (delta : ENNReal) ^ 2 at hIE
  have hnumeric :
      (3267 / 2000 : ENNReal) * (delta : ENNReal) ^ 2 +
          (3267 / 2000 : ENNReal) * (delta : ENNReal) ^ 2 =
        (20691 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 +
          (11979 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div]
    ring
  have hcancel :
      volume (commonPointCrossPrism T frame) +
          (11979 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 =
        (20691 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 +
          (11979 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 :=
    hIE.trans hnumeric
  exact (ENNReal.add_left_inj (by finiteness)).mp hcancel

/-- At sufficiently small positive radius, the explicit crossed core occupies
strictly more than half of the containing tube's volume.  The smallness
threshold is concrete and leaves a quantitative margin for perturbing the
axis in the subsequent common-point argument. -/
theorem half_volume_of_tube_lt_volume_commonPointCrossPrism
    {delta : NNReal} (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (2 : ENNReal)⁻¹ * volume U.carrier <
      volume (commonPointCrossPrism T frame) := by
  have hsmallToHalf : (1 / 100 : NNReal) ≤ (2 : NNReal)⁻¹ := by
    rw [← NNReal.coe_le_coe]
    norm_num [NNReal.coe_div, NNReal.coe_inv]
  have hhalf : delta ≤ (2 : NNReal)⁻¹ :=
    hdeltaSmall.trans hsmallToHalf
  have hupper := (U.volume_sandwich_of_le_half hhalf).2
  have hdeltaRealPos : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have hdeltaRealSmall : (delta : Real) ≤ (1 : Real) / 100 := by
    exact_mod_cast hdeltaSmall
  have hnumeric :
      (2 : ENNReal)⁻¹ *
          (4 * (delta : ENNReal) ^ 2 * (1 + 2 * (delta : ENNReal))) <
        (20691 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_div]
    have hproduct :
        0 ≤ (delta : Real) ^ 2 * ((1 : Real) / 100 - (delta : Real)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hdeltaRealSmall)
    have hsquarePos : 0 < (delta : Real) ^ 2 := sq_pos_of_pos hdeltaRealPos
    nlinarith
  calc
    (2 : ENNReal)⁻¹ * volume U.carrier ≤
        (2 : ENNReal)⁻¹ *
          (4 * (delta : ENNReal) ^ 2 * (1 + 2 * (delta : ENNReal))) :=
      mul_le_mul_of_nonneg_left hupper (by exact bot_le)
    _ < (20691 / 10000 : ENNReal) * (delta : ENNReal) ^ 2 := hnumeric
    _ = volume (commonPointCrossPrism T frame) :=
      (volume_commonPointCrossPrism T frame).symm

/-- In particular, the crossed core beats half of its own tube. -/
theorem half_volume_lt_volume_commonPointCrossPrism
    {delta : NNReal} (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (2 : ENNReal)⁻¹ * volume T.carrier <
      volume (commonPointCrossPrism T frame) :=
  half_volume_of_tube_lt_volume_commonPointCrossPrism
    T T frame hdeltaPos hdeltaSmall

/-- The crossed core beats the half-volume threshold used in
`EssentiallyDistinct` for any second tube of the same radius. -/
theorem half_max_volume_lt_volume_commonPointCrossPrism
    {delta : NNReal} (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (2 : ENNReal)⁻¹ * max (volume T.carrier) (volume U.carrier) <
      volume (commonPointCrossPrism T frame) := by
  rcases le_total (volume T.carrier) (volume U.carrier) with hTU | hUT
  · rw [max_eq_right hTU]
    exact half_volume_of_tube_lt_volume_commonPointCrossPrism
      T U frame hdeltaPos hdeltaSmall
  · rw [max_eq_left hUT]
    exact half_volume_of_tube_lt_volume_commonPointCrossPrism
      T T frame hdeltaPos hdeltaSmall

/-- Midpoint of the unit axis segment, used as the position parameter in the
local packing code. -/
def tubeAxisMidpoint {delta : NNReal} (T : Tube delta) : Space :=
  T.axis.base + (2 : Real)⁻¹ • T.axis.direction

/-- Matching midpoint and direction parameters control the distance between
corresponding points of two unit axes. -/
theorem dist_axisPoint_le_of_midpoint_direction_close
    {delta : NNReal} (T U : Tube delta) {t : Real}
    (ht : t ∈ Set.Icc (0 : Real) 1)
    (hmid : dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 100) :
    dist (T.axis.base + t • T.axis.direction)
        (U.axis.base + t • U.axis.direction) ≤
      (3 : Real) / 200 * (delta : Real) := by
  let s : Real := t - (2 : Real)⁻¹
  have hs : |s| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> dsimp only [s] <;> norm_num at * <;> linarith [ht.1, ht.2]
  have hT :
      T.axis.base + t • T.axis.direction =
        tubeAxisMidpoint T + s • T.axis.direction := by
    simp only [tubeAxisMidpoint, s]
    module
  have hU :
      U.axis.base + t • U.axis.direction =
        tubeAxisMidpoint U + s • U.axis.direction := by
    simp only [tubeAxisMidpoint, s]
    module
  rw [hT, hU, dist_eq_norm]
  have hvec :
      (tubeAxisMidpoint T + s • T.axis.direction) -
          (tubeAxisMidpoint U + s • U.axis.direction) =
        (tubeAxisMidpoint T - tubeAxisMidpoint U) +
          s • (T.axis.direction - U.axis.direction) := by
    module
  rw [hvec]
  have hscaled :
      |s| * dist T.axis.direction U.axis.direction ≤
        (2 : Real)⁻¹ * ((delta : Real) / 100) := by
    calc
      |s| * dist T.axis.direction U.axis.direction ≤
          (2 : Real)⁻¹ * dist T.axis.direction U.axis.direction :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
      _ ≤ (2 : Real)⁻¹ * ((delta : Real) / 100) :=
        mul_le_mul_of_nonneg_left hdir (by norm_num)
  calc
    ‖(tubeAxisMidpoint T - tubeAxisMidpoint U) +
        s • (T.axis.direction - U.axis.direction)‖ ≤
      ‖tubeAxisMidpoint T - tubeAxisMidpoint U‖ +
        ‖s • (T.axis.direction - U.axis.direction)‖ := norm_add_le _ _
    _ = dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) +
        |s| * dist T.axis.direction U.axis.direction := by
      simp only [dist_eq_norm, norm_smul, Real.norm_eq_abs]
    _ ≤ (delta : Real) / 100 +
        (2 : Real)⁻¹ * ((delta : Real) / 100) :=
      add_le_add hmid hscaled
    _ = (3 : Real) / 200 * (delta : Real) := by ring

/-- If midpoint and direction parameters are in the same sufficiently fine
cell, every point of either crossed arm of `T` lies in `U`. -/
theorem commonPointPrism_subset_other_carrier_of_close
    {delta : NNReal} (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction) (swap : Bool)
    (hmid : dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 100) :
    (commonPointPrism T frame swap).carrier ⊆ U.carrier := by
  intro x hx
  obtain ⟨t, ht, hxT⟩ :=
    commonPointPrism_exists_axisPoint T frame hframe swap x hx
  have htUnit : t ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> nlinarith [ht.1, ht.2]
  have haxis := dist_axisPoint_le_of_midpoint_direction_close
    T U htUnit hmid hdir
  have hxU :
      dist x (U.axis.base + t • U.axis.direction) ≤ (delta : Real) := by
    calc
      dist x (U.axis.base + t • U.axis.direction) ≤
          dist x (T.axis.base + t • T.axis.direction) +
            dist (T.axis.base + t • T.axis.direction)
              (U.axis.base + t • U.axis.direction) := dist_triangle _ _ _
      _ ≤ (47 : Real) / 50 * (delta : Real) +
          (3 : Real) / 200 * (delta : Real) := add_le_add hxT haxis
      _ ≤ (delta : Real) := by
        have hdelta : 0 ≤ (delta : Real) := NNReal.zero_le_coe
        nlinarith
  exact Metric.mem_cthickening_of_dist_le
    x (U.axis.base + t • U.axis.direction) (delta : Real) U.axis.carrier
    (U.axis.mem_carrier_of_mem_Icc htUnit) hxU

/-- The full crossed core transfers to a nearby tube. -/
theorem commonPointCrossPrism_subset_other_carrier_of_close
    {delta : NNReal} (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hmid : dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 100) :
    commonPointCrossPrism T frame ⊆ U.carrier := by
  exact union_subset
    (commonPointPrism_subset_other_carrier_of_close
      T U frame hframe false hmid hdir)
    (commonPointPrism_subset_other_carrier_of_close
      T U frame hframe true hmid hdir)

/-- Quantitative near-parameter separation forced by the actual
half-overlap definition: two such nearby tubes cannot be essentially
distinct. -/
theorem not_essentiallyDistinct_of_midpoint_direction_close
    {delta : NNReal} (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hmid : dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 100) :
    ¬ EssentiallyDistinct T U := by
  intro hdistinct
  have hcrossInter :
      commonPointCrossPrism T frame ⊆ T.carrier ∩ U.carrier := fun x hx =>
    ⟨commonPointCrossPrism_subset_carrier T frame hframe hx,
      commonPointCrossPrism_subset_other_carrier_of_close
        T U frame hframe hmid hdir hx⟩
  have hmeasure :
      volume (commonPointCrossPrism T frame) ≤
        volume (T.carrier ∩ U.carrier) := measure_mono hcrossInter
  have hstrict := half_max_volume_lt_volume_commonPointCrossPrism
    T U frame hdeltaPos hdeltaSmall
  exact (not_lt_of_ge hdistinct) (hstrict.trans_le hmeasure)

/-- Signed longitudinal coordinate of the tube midpoint relative to a common
point, measured in the tube direction. -/
def tubePointLongitudinal {delta : NNReal} (x : Space) (T : Tube delta) : Real :=
  ⟪T.axis.direction, tubeAxisMidpoint T - x⟫_ℝ

/-- Transverse residual of the tube midpoint relative to a common point. -/
def tubePointTransverse {delta : NNReal} (x : Space) (T : Tube delta) : Space :=
  tubeAxisMidpoint T - x - tubePointLongitudinal x T • T.axis.direction

theorem tubeAxisMidpoint_eq_point_decomposition
    {delta : NNReal} (x : Space) (T : Tube delta) :
    tubeAxisMidpoint T = x +
      tubePointLongitudinal x T • T.axis.direction +
        tubePointTransverse x T := by
  simp only [tubePointTransverse]
  abel

/-- A point in an actual tube has a concrete nearby point on its axis. -/
theorem exists_axis_parameter_dist_le_of_mem
    {delta : NNReal} (T : Tube delta) {x : Space} (hx : x ∈ T.carrier) :
    ∃ t ∈ Set.Icc (0 : Real) 1,
      dist x (T.axis.base + t • T.axis.direction) ≤ (delta : Real) := by
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (delta : Real) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hyAxis, hdist⟩ := hx
  rw [T.axis.carrier_eq_image] at hyAxis
  obtain ⟨t, ht, rfl⟩ := hyAxis
  exact ⟨t, ht, hdist⟩

/-- The common-point longitudinal parameter lies in a fixed compact
interval, independent of `delta`. -/
theorem abs_tubePointLongitudinal_le
    {delta : NNReal} (T : Tube delta) {x : Space}
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) (hx : x ∈ T.carrier) :
    |tubePointLongitudinal x T| ≤ (51 : Real) / 100 := by
  obtain ⟨t, ht, hdist⟩ := exists_axis_parameter_dist_le_of_mem T hx
  let q : Space := T.axis.base + t • T.axis.direction
  have hqnorm : ‖q - x‖ ≤ (delta : Real) := by
    simpa [q, dist_eq_norm, norm_sub_rev] using hdist
  have htcenter : |(2 : Real)⁻¹ - t| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  have hmidvec :
      tubeAxisMidpoint T - x =
        ((2 : Real)⁻¹ - t) • T.axis.direction + (q - x) := by
    simp only [tubeAxisMidpoint, q]
    module
  have haeq :
      tubePointLongitudinal x T =
        ((2 : Real)⁻¹ - t) + ⟪T.axis.direction, q - x⟫_ℝ := by
    rw [tubePointLongitudinal, hmidvec, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      T.axis.norm_direction]
    norm_num
  have hinner : |⟪T.axis.direction, q - x⟫_ℝ| ≤ (delta : Real) := by
    have h := abs_real_inner_le_norm T.axis.direction (q - x)
    rw [T.axis.norm_direction, one_mul] at h
    exact h.trans hqnorm
  have hdeltaRealSmall : (delta : Real) ≤ (1 : Real) / 100 := by
    exact_mod_cast hdeltaSmall
  calc
    |tubePointLongitudinal x T| =
        |((2 : Real)⁻¹ - t) + ⟪T.axis.direction, q - x⟫_ℝ| := by
      rw [haeq]
    _ ≤ |(2 : Real)⁻¹ - t| +
        |⟪T.axis.direction, q - x⟫_ℝ| := abs_add_le _ _
    _ ≤ (2 : Real)⁻¹ + (delta : Real) := add_le_add htcenter hinner
    _ ≤ (51 : Real) / 100 := by norm_num at *; linarith

/-- The midpoint residual transverse to the tube direction is controlled by
the tube radius at every common carrier point. -/
theorem norm_tubePointTransverse_le_two_mul
    {delta : NNReal} (T : Tube delta) {x : Space} (hx : x ∈ T.carrier) :
    ‖tubePointTransverse x T‖ ≤ 2 * (delta : Real) := by
  obtain ⟨t, _ht, hdist⟩ := exists_axis_parameter_dist_le_of_mem T hx
  let q : Space := T.axis.base + t • T.axis.direction
  have hqnorm : ‖q - x‖ ≤ (delta : Real) := by
    simpa [q, dist_eq_norm, norm_sub_rev] using hdist
  have hmidvec :
      tubeAxisMidpoint T - x =
        ((2 : Real)⁻¹ - t) • T.axis.direction + (q - x) := by
    simp only [tubeAxisMidpoint, q]
    module
  have haeq :
      tubePointLongitudinal x T =
        ((2 : Real)⁻¹ - t) + ⟪T.axis.direction, q - x⟫_ℝ := by
    rw [tubePointLongitudinal, hmidvec, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      T.axis.norm_direction]
    norm_num
  have heq :
      tubePointTransverse x T =
        (q - x) - ⟪T.axis.direction, q - x⟫_ℝ • T.axis.direction := by
    rw [tubePointTransverse, hmidvec, haeq]
    module
  have hinner : |⟪T.axis.direction, q - x⟫_ℝ| ≤ (delta : Real) := by
    have h := abs_real_inner_le_norm T.axis.direction (q - x)
    rw [T.axis.norm_direction, one_mul] at h
    exact h.trans hqnorm
  rw [heq]
  calc
    ‖(q - x) - ⟪T.axis.direction, q - x⟫_ℝ • T.axis.direction‖ ≤
        ‖q - x‖ +
          ‖⟪T.axis.direction, q - x⟫_ℝ • T.axis.direction‖ :=
      norm_sub_le _ _
    _ = ‖q - x‖ + |⟪T.axis.direction, q - x⟫_ℝ| := by
      simp [norm_smul, T.axis.norm_direction, Real.norm_eq_abs]
    _ ≤ (delta : Real) + (delta : Real) := add_le_add hqnorm hinner
    _ = 2 * (delta : Real) := by ring

/-- Anisotropic transfer: longitudinal midpoint displacement is allowed at
constant scale, while only direction and transverse displacement are forced
to be `O(delta)`.  This is the geometry needed for a `delta^-2` pointwise
packing bound. -/
theorem commonPointPrism_subset_other_carrier_of_anisotropic_close
    {delta : NNReal} (x0 : Space) (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction) (swap : Bool)
    (haT : |tubePointLongitudinal x0 T| ≤ (51 : Real) / 100)
    (hlong : |tubePointLongitudinal x0 T - tubePointLongitudinal x0 U| ≤
      (1 : Real) / 400)
    (htrans : dist (tubePointTransverse x0 T) (tubePointTransverse x0 U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 100) :
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
  have hlongBounds := (abs_le.mp hlong')
  have htU : tU ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp only [tU] <;> norm_num at * <;>
      linarith [ht.1, ht.2, hlongBounds.1, hlongBounds.2]
  have htcenter : |t - (2 : Real)⁻¹| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  have haT' : |aT| ≤ (51 : Real) / 100 := by
    simpa only [aT] using haT
  have hcoeff :
      |aT + (t - (2 : Real)⁻¹)| ≤ (101 : Real) / 100 := by
    calc
      |aT + (t - (2 : Real)⁻¹)| ≤
          |aT| + |t - (2 : Real)⁻¹| := abs_add_le _ _
      _ ≤ (51 : Real) / 100 + (2 : Real)⁻¹ := add_le_add haT' htcenter
      _ = (101 : Real) / 100 := by norm_num
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
        (101 : Real) / 100 * ((delta : Real) / 100) := by
    exact mul_le_mul hcoeff hdir dist_nonneg (by norm_num)
  have haxis :
      dist (T.axis.base + t • T.axis.direction)
          (U.axis.base + tU • U.axis.direction) ≤
        (201 : Real) / 10000 * (delta : Real) := by
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
      _ ≤ (101 : Real) / 100 * ((delta : Real) / 100) +
          (delta : Real) / 100 := add_le_add hscaled htrans
      _ = (201 : Real) / 10000 * (delta : Real) := by ring
  have hzU :
      dist z (U.axis.base + tU • U.axis.direction) ≤ (delta : Real) := by
    calc
      dist z (U.axis.base + tU • U.axis.direction) ≤
          dist z (T.axis.base + t • T.axis.direction) +
            dist (T.axis.base + t • T.axis.direction)
              (U.axis.base + tU • U.axis.direction) := dist_triangle _ _ _
      _ ≤ (47 : Real) / 50 * (delta : Real) +
          (201 : Real) / 10000 * (delta : Real) := add_le_add hzT haxis
      _ ≤ (delta : Real) := by
        have hdelta : 0 ≤ (delta : Real) := NNReal.zero_le_coe
        nlinarith
  exact Metric.mem_cthickening_of_dist_le
    z (U.axis.base + tU • U.axis.direction) (delta : Real) U.axis.carrier
    (U.axis.mem_carrier_of_mem_Icc htU) hzU

/-- Anisotropic closeness transfers the full crossed core. -/
theorem commonPointCrossPrism_subset_other_carrier_of_anisotropic_close
    {delta : NNReal} (x0 : Space) (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (haT : |tubePointLongitudinal x0 T| ≤ (51 : Real) / 100)
    (hlong : |tubePointLongitudinal x0 T - tubePointLongitudinal x0 U| ≤
      (1 : Real) / 400)
    (htrans : dist (tubePointTransverse x0 T) (tubePointTransverse x0 U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 100) :
    commonPointCrossPrism T frame ⊆ U.carrier := by
  exact union_subset
    (commonPointPrism_subset_other_carrier_of_anisotropic_close
      x0 T U frame hframe false haT hlong htrans hdir)
    (commonPointPrism_subset_other_carrier_of_anisotropic_close
      x0 T U frame hframe true haT hlong htrans hdir)

/-- Actual `EssentiallyDistinct` tubes through a common point cannot share
one anisotropic position/direction code. -/
theorem not_essentiallyDistinct_of_anisotropic_close
    {delta : NNReal} (x0 : Space) (T U : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (haT : |tubePointLongitudinal x0 T| ≤ (51 : Real) / 100)
    (hlong : |tubePointLongitudinal x0 T - tubePointLongitudinal x0 U| ≤
      (1 : Real) / 400)
    (htrans : dist (tubePointTransverse x0 T) (tubePointTransverse x0 U) ≤
      (delta : Real) / 100)
    (hdir : dist T.axis.direction U.axis.direction ≤
      (delta : Real) / 100) :
    ¬ EssentiallyDistinct T U := by
  intro hdistinct
  have hcrossInter :
      commonPointCrossPrism T frame ⊆ T.carrier ∩ U.carrier := fun z hz =>
    ⟨commonPointCrossPrism_subset_carrier T frame hframe hz,
      commonPointCrossPrism_subset_other_carrier_of_anisotropic_close
        x0 T U frame hframe haT hlong htrans hdir hz⟩
  have hmeasure :
      volume (commonPointCrossPrism T frame) ≤
        volume (T.carrier ∩ U.carrier) := measure_mono hcrossInter
  have hstrict := half_max_volume_lt_volume_commonPointCrossPrism
    T U frame hdeltaPos hdeltaSmall
  exact (not_lt_of_ge hdistinct) (hstrict.trans_le hmeasure)

/-- Every coordinate of a three-dimensional Euclidean vector is bounded by
its Euclidean norm. -/
theorem abs_apply_le_norm (v : Space) (k : Fin 3) :
    |v k| ≤ ‖v‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum
    (fun i _hi => sq_nonneg (v i)) (Finset.mem_univ k)

/-- Coordinatewise `delta/1000` closeness implies the transverse distance
required by the anisotropic transfer theorem. -/
theorem dist_le_delta_div_hundred_of_coordinate_close
    {delta : NNReal} {v w : Space}
    (hcoord : ∀ k : Fin 3, |v k - w k| < (delta : Real) / 1000) :
    dist v w ≤ (delta : Real) / 100 := by
  have h0 := sq_le_sq_of_abs_le (hcoord (0 : Fin 3)).le
  have h1 := sq_le_sq_of_abs_le (hcoord (1 : Fin 3)).le
  have h2 := sq_le_sq_of_abs_le (hcoord (2 : Fin 3)).le
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  norm_num at h0 h1 h2 ⊢
  nlinarith [sq_nonneg (delta : Real)]

/-- Four bounded coordinates describing the position of a tube through a
fixed point.  The first coordinate is longitudinal and therefore lives on a
fixed scale.  The remaining three are the transverse displacement divided by
`delta`; this normalization prevents an artificial third power of the inverse
scale in the final packing bound. -/
def commonPointPositionCoordinates {delta : NNReal} (x : Space)
    (T : Tube delta) : Fin 4 → Real :=
  ![tubePointLongitudinal x T,
    tubePointTransverse x T 0 / (delta : Real),
    tubePointTransverse x T 1 / (delta : Real),
    tubePointTransverse x T 2 / (delta : Real)]

/-- A tube containing `x` has all four normalized position coordinates in
the fixed box `[-2,2]`. -/
theorem abs_commonPointPositionCoordinates_le_two
    {delta : NNReal} (x : Space) (T : Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hx : x ∈ T.carrier) (k : Fin 4) :
    |commonPointPositionCoordinates x T k| ≤ 2 := by
  have hlong := abs_tubePointLongitudinal_le T hdeltaSmall hx
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have htrans (j : Fin 3) :
      |tubePointTransverse x T j / (delta : Real)| ≤ 2 := by
    rw [abs_div, abs_of_pos hdeltaReal, div_le_iff₀ hdeltaReal]
    exact (abs_apply_le_norm (tubePointTransverse x T) j).trans
      (norm_tubePointTransverse_le_two_mul T hx)
  fin_cases k
  · simpa [commonPointPositionCoordinates] using hlong.trans (by norm_num)
  · simpa [commonPointPositionCoordinates] using htrans 0
  · simpa [commonPointPositionCoordinates] using htrans 1
  · simpa [commonPointPositionCoordinates] using htrans 2

/-- Fixed mesh used for the anisotropic position code. -/
def commonPointPositionMesh : Real := (1 : Real) / 1000

/-- Fixed coordinate bound used for the anisotropic position code. -/
def commonPointPositionBound : Real := 2

/-- Number of cells in the explicit four-coordinate position box. -/
def commonPointPositionCodeLoss : Nat := 4001 ^ 4

/-- Equality of normalized position floor codes gives precisely the two
position estimates used by the anisotropic overlap lemma. -/
theorem anisotropic_close_of_position_floorCode_eq
    {delta : NNReal} (x : Space) (T U : Tube delta)
    (hdeltaPos : 0 < delta)
    (hcode :
      FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
          commonPointPositionMesh (commonPointPositionCoordinates x) T =
        FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
          commonPointPositionMesh (commonPointPositionCoordinates x) U) :
    |tubePointLongitudinal x T - tubePointLongitudinal x U| ≤
        (1 : Real) / 400 ∧
      dist (tubePointTransverse x T) (tubePointTransverse x U) ≤
        (delta : Real) / 100 := by
  have hmesh : 0 < commonPointPositionMesh := by
    norm_num [commonPointPositionMesh]
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have h0 :=
    FamilyStickyRandomFiniteFloorParameterNetV1.abs_coord_sub_lt_of_floorCode_eq
      hmesh (commonPointPositionCoordinates x) hcode (0 : Fin 4)
  have hlong :
      |tubePointLongitudinal x T - tubePointLongitudinal x U| <
        (1 : Real) / 1000 := by
    simpa [commonPointPositionCoordinates, commonPointPositionMesh] using h0
  refine ⟨hlong.le.trans (by norm_num), ?_⟩
  apply dist_le_delta_div_hundred_of_coordinate_close
  intro j
  have normalizedClose (j : Fin 3) (k : Fin 4)
      (hk : commonPointPositionCoordinates x T k =
          tubePointTransverse x T j / (delta : Real))
      (hkU : commonPointPositionCoordinates x U k =
          tubePointTransverse x U j / (delta : Real)) :
      |tubePointTransverse x T j - tubePointTransverse x U j| <
        (delta : Real) / 1000 := by
    have h :=
      FamilyStickyRandomFiniteFloorParameterNetV1.abs_coord_sub_lt_of_floorCode_eq
        hmesh (commonPointPositionCoordinates x) hcode k
    rw [hk, hkU, ← sub_div, abs_div, abs_of_pos hdeltaReal] at h
    rw [commonPointPositionMesh] at h
    have hscaled := (div_lt_iff₀ hdeltaReal).mp h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hscaled
  fin_cases j
  · exact normalizedClose 0 1 (by simp [commonPointPositionCoordinates])
      (by simp [commonPointPositionCoordinates])
  · exact normalizedClose 1 2 (by simp [commonPointPositionCoordinates])
      (by simp [commonPointPositionCoordinates])
  · exact normalizedClose 2 3 (by simp [commonPointPositionCoordinates])
      (by simp [commonPointPositionCoordinates])

/-- The explicit four-dimensional normalized position grid has at most
`4001^4` occupied cells. -/
theorem commonPointPosition_occupiedCode_card_le
    {parameter : Type}
    (coord : parameter → Fin 4 → Real)
    (hbound : ∀ p k, |coord p k| ≤ commonPointPositionBound) :
    Fintype.card
        (FamilyStickyRandomFiniteFloorParameterNetV1.OccupiedCode
          commonPointPositionMesh commonPointPositionBound
          (by norm_num [commonPointPositionMesh]) coord hbound) ≤
      commonPointPositionCodeLoss := by
  have h :=
    FamilyStickyRandomFiniteFloorParameterNetV1.card_occupiedCode_le
      commonPointPositionMesh commonPointPositionBound
      (by norm_num [commonPointPositionMesh]) coord hbound
  norm_num [commonPointPositionMesh, commonPointPositionBound,
    commonPointPositionCodeLoss] at h ⊢
  exact h

/-- Tubes from `indices` whose actual carriers contain `x`. -/
def commonPointTubeIndices
    {delta : NNReal} {index : Type} [DecidableEq index]
    (indices : Finset index) (tube : index → Tube delta) (x : Space) :
    Finset index :=
  indices.filter fun i => x ∈ (tube i).carrier

/-- Direction cap at the separation scale used by the overlap argument. -/
def commonPointDirectionCap (delta : NNReal) : Nat :=
  Nat.ceil (32 * ((((delta / 100 : NNReal) : Real))⁻¹) ^ 2)

/-- Fully explicit natural pointwise cap. -/
def commonPointTubePackingNatCap (delta : NNReal) : Nat :=
  commonPointPositionCodeLoss * commonPointDirectionCap delta

/-- An essentially-distinct finite family has at most the explicit packing
cap many tubes through any one point.  The only inverse-scale contribution is
the two-dimensional direction packing; position contributes the fixed
`4001^4` loss. -/
theorem commonPointTubeIndices_card_le
    {delta : NNReal} {index : Type} [DecidableEq index]
    (indices : Finset index) (tube : index → Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (↑indices : Set index) fun i j =>
      EssentiallyDistinct (tube i) (tube j))
    (x : Space) :
    (commonPointTubeIndices indices tube x).card ≤
      commonPointTubePackingNatCap delta := by
  classical
  let active : Finset index := commonPointTubeIndices indices tube x
  let Parameter := ↥active
  let mesh : Real := commonPointPositionMesh
  let bound : Real := commonPointPositionBound
  let coord : Parameter → Fin 4 → Real := fun p =>
    commonPointPositionCoordinates x (tube p.1)
  have hmesh : 0 < mesh := by
    norm_num [mesh, commonPointPositionMesh]
  have hbound : ∀ p : Parameter, ∀ k, |coord p k| ≤ bound := by
    intro p k
    have hp : p.1 ∈ indices ∧ x ∈ (tube p.1).carrier := by
      simpa only [active, commonPointTubeIndices, Finset.mem_filter] using
        p.property
    simpa only [coord, bound, commonPointPositionBound] using
      abs_commonPointPositionCoordinates_le_two
        x (tube p.1) hdeltaPos hdeltaSmall hp.2 k
  let Code :=
    FamilyStickyRandomFiniteFloorParameterNetV1.OccupiedCode
      mesh bound hmesh coord hbound
  let code : Parameter → Code := fun p =>
    FamilyStickyRandomFiniteFloorParameterNetV1.ownCode
      mesh bound hmesh coord hbound p
  have hscalePos : 0 < delta / 100 := div_pos hdeltaPos (by norm_num)
  have hscaleOne : delta / 100 ≤ (1 : NNReal) := by
    apply (div_le_one (by norm_num : (0 : NNReal) < 100)).2
    exact hdeltaSmall.trans (by
      exact_mod_cast (show (1 : Real) / 100 ≤ 100 by norm_num))
  have hfiber : ∀ c ∈ (Finset.univ : Finset Code),
      ((Finset.univ : Finset Parameter).filter fun p => code p = c).card ≤
        commonPointDirectionCap delta := by
    intro c _hc
    let fiber : Finset Parameter :=
      (Finset.univ : Finset Parameter).filter fun p => code p = c
    have hseparated :
        ∀ p ∈ fiber, ∀ q ∈ fiber, p ≠ q →
          (((delta / 100 : NNReal) : Real)) ≤
            dist (tube p.1).axis.direction (tube q.1).axis.direction := by
      intro p hp q hq hpq
      have hpFilter := Finset.mem_filter.mp hp
      have hqFilter := Finset.mem_filter.mp hq
      have hpActive : p.1 ∈ indices ∧ x ∈ (tube p.1).carrier := by
        simpa only [active, commonPointTubeIndices, Finset.mem_filter] using
          p.property
      have hqActive : q.1 ∈ indices ∧ x ∈ (tube q.1).carrier := by
        simpa only [active, commonPointTubeIndices, Finset.mem_filter] using
          q.property
      have hpqVal : p.1 ≠ q.1 := by
        intro hpqVal
        apply hpq
        exact Subtype.ext hpqVal
      have hcodeEq : code p = code q := hpFilter.2.trans hqFilter.2.symm
      have hboundedEq :
          FamilyStickyRandomFiniteFloorParameterNetV1.boundedFloorCode
              mesh bound hmesh coord hbound p =
            FamilyStickyRandomFiniteFloorParameterNetV1.boundedFloorCode
              mesh bound hmesh coord hbound q :=
        congrArg Subtype.val hcodeEq
      have hfloorEq :
          FamilyStickyRandomFiniteFloorParameterNetV1.floorCode mesh coord p =
            FamilyStickyRandomFiniteFloorParameterNetV1.floorCode mesh coord q := by
        funext k
        exact congrArg Subtype.val (congrFun hboundedEq k)
      have hfloorTube :
          FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
              commonPointPositionMesh (commonPointPositionCoordinates x)
                (tube p.1) =
            FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
              commonPointPositionMesh (commonPointPositionCoordinates x)
                (tube q.1) := by
        funext k
        have hk := congrFun hfloorEq k
        change Int.floor
            (commonPointPositionCoordinates x (tube p.1) k /
              commonPointPositionMesh) =
          Int.floor
            (commonPointPositionCoordinates x (tube q.1) k /
              commonPointPositionMesh)
        change Int.floor
            (commonPointPositionCoordinates x (tube p.1) k /
              commonPointPositionMesh) =
          Int.floor
            (commonPointPositionCoordinates x (tube q.1) k /
              commonPointPositionMesh) at hk
        exact hk
      have hposition := anisotropic_close_of_position_floorCode_eq
        x (tube p.1) (tube q.1) hdeltaPos hfloorTube
      have hessential := hpairwise hpActive.1 hqActive.1 hpqVal
      by_contra hnotSeparated
      have hdirection :
          dist (tube p.1).axis.direction (tube q.1).axis.direction ≤
            (delta : Real) / 100 := by
        have hlt := (lt_of_not_ge hnotSeparated).le
        norm_num at hlt ⊢
        exact hlt
      obtain ⟨frame, hframe⟩ := (tube p.1).exists_alignedFrame
      exact (not_essentiallyDistinct_of_anisotropic_close
        x (tube p.1) (tube q.1) frame hframe hdeltaPos hdeltaSmall
        (abs_tubePointLongitudinal_le (tube p.1) hdeltaSmall hpActive.2)
        hposition.1 hposition.2 hdirection) hessential
    have hcard :=
      Family8SphereDirectionPackingV1.directionFinset_card_le_natCeil_thirtyTwo_mul_inv_sq
        fiber (fun p => (tube p.1).axis.direction) (delta / 100)
        hscalePos hscaleOne
        (fun p _hp => (tube p.1).axis.norm_direction) hseparated
    simpa only [fiber, commonPointDirectionCap] using hcard
  have hfinite :=
    Family6FiniteMapFiberCapCardV1.card_le_fiberCap_mul_card
      (Finset.univ : Finset Parameter) (Finset.univ : Finset Code) code
      (commonPointDirectionCap delta) (by simp) hfiber
  have hcodeCard : Fintype.card Code ≤ commonPointPositionCodeLoss := by
    simpa only [Code, mesh, bound] using
      commonPointPosition_occupiedCode_card_le coord hbound
  change active.card ≤ commonPointTubePackingNatCap delta
  calc
    active.card = Fintype.card Parameter := by simp only [Parameter, Fintype.card_coe]
    _ ≤ commonPointDirectionCap delta * Fintype.card Code := by
      simpa only [Finset.card_univ] using hfinite
    _ ≤ commonPointDirectionCap delta * commonPointPositionCodeLoss := by
      exact Nat.mul_le_mul_left _ hcodeCard
    _ = commonPointTubePackingNatCap delta := by
      simp only [commonPointTubePackingNatCap, Nat.mul_comm]

/-- The generic finite theorem specialized to every tube of an admissible
actual datum. -/
theorem actualTubeDatum_commonPoint_card_le
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta index)
    (hD : D.IsAdmissible) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (x : Space) :
    (Finset.univ.filter fun i => x ∈ (D.family.tubes i).carrier).card ≤
      commonPointTubePackingNatCap delta := by
  apply commonPointTubeIndices_card_le Finset.univ D.family.tubes
    hD.delta_pos hdeltaSmall
  intro i _hi j _hj hij
  exact hD.pairwise_essentiallyDistinct (Set.mem_univ i)
    (Set.mem_univ j) hij

/-- Direct hypothesis for the pointwise-multiplicity integration modules. -/
theorem actualCarrierShading_pointMultiplicity_le_commonPointTubePackingNatCap
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta index)
    (hD : D.IsAdmissible) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (x : Space) :
    (Family8PointwisePackingVolumeV1.actualCarrierShading D).pointMultiplicity x ≤
      commonPointTubePackingNatCap delta := by
  rw [Family8PointwisePackingVolumeV1.actualCarrierShading_pointMultiplicity]
  exact actualTubeDatum_commonPoint_card_le D hD hdeltaSmall x

/-- Any actual shading is pointwise dominated by the full-carrier shading. -/
theorem actualShading_pointMultiplicity_le_actualCarrierShading
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta index)
    (x : Space) :
    D.shading.pointMultiplicity x ≤
      (Family8PointwisePackingVolumeV1.actualCarrierShading D).pointMultiplicity x := by
  classical
  unfold Shading.pointMultiplicity
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, D.shading.carrier_subset i hi.2⟩

/-- Direct pointwise cap for the actual shading, not merely for the full tube
carriers. -/
theorem actualShading_pointMultiplicity_le_commonPointTubePackingNatCap
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta index)
    (hD : D.IsAdmissible) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (x : Space) :
    D.shading.pointMultiplicity x ≤ commonPointTubePackingNatCap delta :=
  (actualShading_pointMultiplicity_le_actualCarrierShading D x).trans
    (actualCarrierShading_pointMultiplicity_le_commonPointTubePackingNatCap
      D hD hdeltaSmall x)

/-- Rescaling the direction separation from `delta` to `delta/100`
contributes exactly the fixed factor `10000`. -/
theorem coe_div_hundred_rpow_neg_two
    (delta : NNReal) (hdeltaPos : 0 < delta) :
    (((delta / 100 : NNReal) : Real) ^ (-2 : Real)) =
      10000 * (delta : Real) ^ (-2 : Real) := by
  have hdeltaReal : (delta : Real) ≠ 0 :=
    ne_of_gt (NNReal.coe_pos.mpr hdeltaPos)
  rw [show (-2 : Real) = ((-2 : Int) : Real) by norm_num,
    Real.rpow_intCast, Real.rpow_intCast]
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
  norm_num [zpow_neg]
  field_simp
  norm_num

/-- Explicit finite constant in the scale-invariant `ENNReal` point cap. -/
def commonPointTubePackingConstant : ENNReal :=
  (commonPointPositionCodeLoss * 330000 : Nat)

/-- The natural cap is bounded by an explicit constant times `delta⁻²`. -/
theorem commonPointTubePackingNatCap_coe_le_rpow
    (delta : NNReal) (hdeltaPos : 0 < delta)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (commonPointTubePackingNatCap delta : ENNReal) ≤
      commonPointTubePackingConstant *
        (delta : ENNReal) ^ (-2 : Real) := by
  have hscalePos : 0 < delta / 100 := div_pos hdeltaPos (by norm_num)
  have hscaleOne : delta / 100 ≤ (1 : NNReal) := by
    apply (div_le_one (by norm_num : (0 : NNReal) < 100)).2
    exact hdeltaSmall.trans (by
      exact_mod_cast (show (1 : Real) / 100 ≤ 100 by norm_num))
  have hdirReal :=
    Family8SphereDirectionPackingENNRealV1.directionPackingNatCap_real_le_rpow
      (delta / 100) hscalePos hscaleOne
  have hdirReal2 :
      (commonPointDirectionCap delta : Real) ≤
        33 * (((delta / 100 : NNReal) : Real) ^ (-2 : Real)) := by
    simpa only [commonPointDirectionCap,
      Family8SphereDirectionPackingENNRealV1.directionPackingNatCap] using
      hdirReal
  have hreal :
      (commonPointTubePackingNatCap delta : Real) ≤
        (commonPointPositionCodeLoss * 330000 : Nat) *
          (delta : Real) ^ (-2 : Real) := by
    calc
      (commonPointTubePackingNatCap delta : Real) =
          (commonPointPositionCodeLoss : Real) *
            (commonPointDirectionCap delta : Real) := by
        simp only [commonPointTubePackingNatCap, Nat.cast_mul]
      _ ≤ (commonPointPositionCodeLoss : Real) *
          (33 * (((delta / 100 : NNReal) : Real) ^ (-2 : Real))) :=
        mul_le_mul_of_nonneg_left hdirReal2 (by positivity)
      _ = (commonPointPositionCodeLoss * 330000 : Nat) *
          (delta : Real) ^ (-2 : Real) := by
        rw [coe_div_hundred_rpow_neg_two delta hdeltaPos]
        push_cast
        ring
  have hnn :
      (commonPointTubePackingNatCap delta : NNReal) ≤
        (commonPointPositionCodeLoss * 330000 : Nat) *
          delta ^ (-2 : Real) := by
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_rpow] using hreal
  rw [commonPointTubePackingConstant,
    ← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hdeltaPos) (-2 : Real)]
  exact_mod_cast hnn

/-- A single explicit cap controls both every point multiplicity and its
scale-invariant `ENNReal` size. -/
theorem exists_actualCarrierShading_commonPointTubePackingNatCap
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta index)
    (hD : D.IsAdmissible) (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    ∃ M : Nat,
      (∀ x,
        (Family8PointwisePackingVolumeV1.actualCarrierShading D).pointMultiplicity x ≤ M) ∧
      (M : ENNReal) ≤ commonPointTubePackingConstant *
        (delta : ENNReal) ^ (-2 : Real) := by
  exact ⟨commonPointTubePackingNatCap delta,
    actualCarrierShading_pointMultiplicity_le_commonPointTubePackingNatCap
      D hD hdeltaSmall,
    commonPointTubePackingNatCap_coe_le_rpow delta hD.delta_pos hdeltaSmall⟩

/-- Finite volume constant obtained by integrating the pointwise cap over
the normalized unit ball. -/
def commonPointFamilyVolumeConstant : ENNReal :=
  commonPointTubePackingConstant *
    volume (Family8KatzTaoFrostmanPropertiesV1.unitBallBody : Set Space)

theorem commonPointFamilyVolumeConstant_ne_top :
    commonPointFamilyVolumeConstant ≠ ∞ := by
  unfold commonPointFamilyVolumeConstant
  apply ENNReal.mul_ne_top
  · unfold commonPointTubePackingConstant
    exact ENNReal.natCast_ne_top _
  · exact measure_closedBall_lt_top.ne

/-- The requested small-scale summed family-volume producer, proved by
integrating the actual common-point multiplicity cap. -/
theorem actualFamilyVolume_le_commonPointPacking
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta index)
    (hD : D.IsAdmissible) (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    D.actualFamilyVolume ≤ commonPointFamilyVolumeConstant *
      (delta : ENNReal) ^ (-2 : Real) := by
  simpa only [commonPointFamilyVolumeConstant] using
    Family8PointwisePackingVolumeV1.actualFamilyVolume_le_rpow_neg_two_of_pointCap
      D hD (commonPointTubePackingNatCap delta)
      (actualCarrierShading_pointMultiplicity_le_commonPointTubePackingNatCap
        D hD hdeltaSmall)
      (commonPointTubePackingNatCap_coe_le_rpow
        delta hD.delta_pos hdeltaSmall)

/-- The explicit packing constant is finite. -/
theorem commonPointTubePackingConstant_ne_top :
    commonPointTubePackingConstant ≠ ∞ := by
  unfold commonPointTubePackingConstant
  exact ENNReal.natCast_ne_top _

/-- Honest terminal scale: the numerical Frostman threshold is additionally
restricted to the geometric regime in which the crossed-prism overlap proof
was established. -/
def commonPointFrostmanOneThreshold (epsilon : Real) : NNReal :=
  min
    (Family8FrostmanOneFromPointwisePackingV1.frostmanOnePointwisePackingThreshold
      commonPointTubePackingConstant epsilon)
    (1 / 100 : NNReal)

theorem commonPointFrostmanOneThreshold_pos
    (epsilon : Real) : 0 < commonPointFrostmanOneThreshold epsilon := by
  rw [commonPointFrostmanOneThreshold, lt_min_iff]
  exact
    ⟨Family8FrostmanOneFromPointwisePackingV1.frostmanOnePointwisePackingThreshold_pos
        commonPointTubePackingConstant epsilon,
      by positivity⟩

theorem commonPointFrostmanOneThreshold_le_hundredth
    (epsilon : Real) :
    commonPointFrostmanOneThreshold epsilon ≤ (1 / 100 : NNReal) :=
  min_le_right _ _

theorem commonPointFrostmanOneThreshold_le_half
    (epsilon : Real) :
    commonPointFrostmanOneThreshold epsilon ≤ (2 : NNReal)⁻¹ := by
  exact (commonPointFrostmanOneThreshold_le_hundredth epsilon).trans (by
    exact_mod_cast (show (1 : Real) / 100 ≤ (2 : Real)⁻¹ by norm_num))

/-- The actual common-point packing theorem closes the complete per-parameter
`K_F(1)` estimate at the honest restricted terminal scale. -/
theorem frostmanAtParameters_one_of_commonPointPacking
    (epsilon eta : Real) (hepsilon : 0 < epsilon) :
    Family8KatzTaoFrostmanPropertiesV1.FrostmanAtParameters
      1 epsilon eta (commonPointFrostmanOneThreshold epsilon) := by
  intro delta index _ _ D hD hdelta _hFrostman
  have hdeltaNumeric :
      delta ≤
        Family8FrostmanOneFromPointwisePackingV1.frostmanOnePointwisePackingThreshold
          commonPointTubePackingConstant epsilon :=
    hdelta.trans (min_le_left _ _)
  have hdeltaSmall : delta ≤ (1 / 100 : NNReal) :=
    hdelta.trans (commonPointFrostmanOneThreshold_le_hundredth epsilon)
  exact
    Family8FrostmanOneFromPointwisePackingV1.averageMultiplicity_le_frostmanOneRHS_of_pointwisePacking
      D commonPointTubePackingConstant (commonPointTubePackingNatCap delta)
      hD.delta_pos hdeltaNumeric commonPointTubePackingConstant_ne_top hepsilon
      (actualShading_pointMultiplicity_le_commonPointTubePackingNatCap
        D hD hdeltaSmall)
      (commonPointTubePackingNatCap_coe_le_rpow
        delta hD.delta_pos hdeltaSmall)

/-- Unconditional base case from actual Euclidean tube geometry:
`K_F(1)` holds with no packing callback or assumed separation theorem beyond
the paper-level admissibility hypothesis itself. -/
theorem frostmanProperty_one :
    Family8KatzTaoFrostmanPropertiesV1.FrostmanProperty 1 := by
  intro epsilon hepsilon
  refine ⟨1, commonPointFrostmanOneThreshold epsilon,
    by norm_num, commonPointFrostmanOneThreshold_pos epsilon,
    commonPointFrostmanOneThreshold_le_half epsilon, ?_⟩
  exact frostmanAtParameters_one_of_commonPointPacking epsilon 1 hepsilon

#print axioms commonPointTubeIndices_card_le
#print axioms commonPointTubePackingNatCap_coe_le_rpow
#print axioms actualCarrierShading_pointMultiplicity_le_commonPointTubePackingNatCap
#print axioms actualFamilyVolume_le_commonPointPacking
#print axioms frostmanProperty_one

#print axioms abs_apply_le_norm
#print axioms dist_le_delta_div_hundred_of_coordinate_close

#print axioms commonPointPrism_subset_other_carrier_of_anisotropic_close
#print axioms not_essentiallyDistinct_of_anisotropic_close

#print axioms norm_tubePointTransverse_le_two_mul

#print axioms abs_tubePointLongitudinal_le

#print axioms dist_axisPoint_le_of_midpoint_direction_close
#print axioms commonPointCrossPrism_subset_other_carrier_of_close
#print axioms not_essentiallyDistinct_of_midpoint_direction_close

#print axioms half_max_volume_lt_volume_commonPointCrossPrism

#print axioms half_volume_lt_volume_commonPointCrossPrism

#print axioms volume_commonPointCrossPrism

#print axioms volume_commonPointPrism
#print axioms volume_commonPointCorePrism

#print axioms commonPointPrism_inter_eq_core

#print axioms commonPointPrism_subset_carrier
#print axioms commonPointCrossPrism_subset_carrier

end


end Family8CommonPointTubePackingV1
