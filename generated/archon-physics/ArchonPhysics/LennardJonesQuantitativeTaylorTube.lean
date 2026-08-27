import ArchonPhysics.LennardJonesTaylorRemainder

/-!
# Quantitative fourth-order Lennard--Jones remainder in a strain tube

This module upgrades the local little-`o` statement for the equilibrium-
centered Lennard--Jones bond to an explicit estimate.  If

`|x| <= rho * r0`, with `0 <= rho < 1`,

then the exact fourth-order remainder is bounded by

`depth * C(rho) * (|x| / r0)^5`,

where `C(rho) = P_abs(rho) / (1 - rho)^12`.  The same constant controls the
per-site sum over any finite periodic lattice on which every bond is in the
tube.  No statement here transfers a long-time dynamical property from the
quartic model to the exact Lennard--Jones flow.
-/

namespace ArchonPhysics.LennardJonesQuantitativeTaylorTube

open LennardJonesPotential
open LennardJonesTaylorRemainder

noncomputable section

/-- The positive-coefficient dimensionless polynomial in the exact
fourth-order remainder.  Its coefficients are the absolute values of those
in `fourthOrderRemainderNumerator`. -/
def dimensionlessFourthOrderNumerator (y : Real) : Real :=
  3864 + y *
    (34916 + y *
      (147840 + y *
        (384120 + y *
          (676940 + y *
            (846582 + y *
              (764664 + y *
                (497870 + y *
                  (228660 + y *
                    (70470 + y *
                      (13104 + y * 1113))))))))))

/-- Sum of the twelve positive coefficients in the dimensionless numerator. -/
def fourthOrderCoefficientSum : Real := 3670143

/-- A sharp, volume-independent explicit envelope for the fourth-order Taylor
remainder on the relative-strain tube of radius `rho`. -/
def fourthOrderTubeConstant (rho : Real) : Real :=
  dimensionlessFourthOrderNumerator rho / (1 - rho) ^ 12

private theorem abs_horner_step
    {a b B y : Real} (ha : 0 <= a) (hy : |y| <= 1) (hb : |b| <= B) :
    |a + y * b| <= a + B := by
  calc
    |a + y * b| <= |a| + |y * b| := abs_add_le _ _
    _ = a + |y| * |b| := by rw [abs_of_nonneg ha, abs_mul]
    _ <= a + 1 * B := by
      simpa [add_comm] using
        add_le_add_left (mul_le_mul hy hb (abs_nonneg b) zero_le_one) a
    _ = a + B := by ring

private theorem abs_horner_step_radius
    {a b B y rho : Real} (ha : 0 <= a) (hrho : 0 <= rho)
    (hy : |y| <= rho) (hb : |b| <= B) :
    |a + y * b| <= a + rho * B := by
  calc
    |a + y * b| <= |a| + |y * b| := abs_add_le _ _
    _ = a + |y| * |b| := by rw [abs_of_nonneg ha, abs_mul]
    _ <= a + rho * B := by
      simpa [add_comm] using
        add_le_add_left (mul_le_mul hy hb (abs_nonneg b) hrho) a

/-- The sharp radius-weighted coefficient polynomial controls the numerator:
no replacement of `rho^k` by one is made. -/
theorem abs_dimensionlessFourthOrderNumerator_le_radiusPolynomial
    {rho y : Real} (hrho : 0 <= rho) (hy : |y| <= rho) :
    |dimensionlessFourthOrderNumerator y| <=
      dimensionlessFourthOrderNumerator rho := by
  unfold dimensionlessFourthOrderNumerator
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  norm_num

/-- The explicit coefficient sum controls the dimensionless numerator on the
closed unit interval. -/
theorem abs_dimensionlessFourthOrderNumerator_le_coefficientSum
    {y : Real} (hy : |y| <= 1) :
    |dimensionlessFourthOrderNumerator y| <= fourthOrderCoefficientSum := by
  have h11 : |(1113 : Real)| <= 1113 := by norm_num
  have h10 : |(13104 : Real) + y * 1113| <= 14217 := by
    calc
      |(13104 : Real) + y * 1113| <= 13104 + 1113 :=
        abs_horner_step (by norm_num) hy h11
      _ = 14217 := by norm_num
  have h9 : |(70470 : Real) + y * (13104 + y * 1113)| <= 84687 := by
    calc
      |(70470 : Real) + y * (13104 + y * 1113)| <= 70470 + 14217 :=
        abs_horner_step (by norm_num) hy h10
      _ = 84687 := by norm_num
  have h8 :
      |(228660 : Real) + y * (70470 + y * (13104 + y * 1113))| <=
        313347 := by
    calc
      |(228660 : Real) + y * (70470 + y * (13104 + y * 1113))| <=
          228660 + 84687 := abs_horner_step (by norm_num) hy h9
      _ = 313347 := by norm_num
  have h7 :
      |(497870 : Real) + y *
          (228660 + y * (70470 + y * (13104 + y * 1113)))| <=
        811217 := by
    calc
      |(497870 : Real) + y *
          (228660 + y * (70470 + y * (13104 + y * 1113)))| <=
          497870 + 313347 := abs_horner_step (by norm_num) hy h8
      _ = 811217 := by norm_num
  have h6 :
      |(764664 : Real) + y *
          (497870 + y *
            (228660 + y * (70470 + y * (13104 + y * 1113))))| <=
        1575881 := by
    calc
      |(764664 : Real) + y *
          (497870 + y *
            (228660 + y * (70470 + y * (13104 + y * 1113))))| <=
          764664 + 811217 := abs_horner_step (by norm_num) hy h7
      _ = 1575881 := by norm_num
  have h5 :
      |(846582 : Real) + y *
          (764664 + y *
            (497870 + y *
              (228660 + y * (70470 + y * (13104 + y * 1113)))))| <=
        2422463 := by
    calc
      |(846582 : Real) + y *
          (764664 + y *
            (497870 + y *
              (228660 + y * (70470 + y * (13104 + y * 1113)))))| <=
          846582 + 1575881 := abs_horner_step (by norm_num) hy h6
      _ = 2422463 := by norm_num
  have h4 :
      |(676940 : Real) + y *
          (846582 + y *
            (764664 + y *
              (497870 + y *
                (228660 + y * (70470 + y * (13104 + y * 1113))))))| <=
        3099403 := by
    calc
      |(676940 : Real) + y *
          (846582 + y *
            (764664 + y *
              (497870 + y *
                (228660 + y * (70470 + y * (13104 + y * 1113))))))| <=
          676940 + 2422463 := abs_horner_step (by norm_num) hy h5
      _ = 3099403 := by norm_num
  have h3 :
      |(384120 : Real) + y *
          (676940 + y *
            (846582 + y *
              (764664 + y *
                (497870 + y *
                  (228660 + y * (70470 + y * (13104 + y * 1113)))))))| <=
        3483523 := by
    calc
      |(384120 : Real) + y *
          (676940 + y *
            (846582 + y *
              (764664 + y *
                (497870 + y *
                  (228660 + y * (70470 + y * (13104 + y * 1113)))))))| <=
          384120 + 3099403 := abs_horner_step (by norm_num) hy h4
      _ = 3483523 := by norm_num
  have h2 :
      |(147840 : Real) + y *
          (384120 + y *
            (676940 + y *
              (846582 + y *
                (764664 + y *
                  (497870 + y *
                    (228660 + y * (70470 + y * (13104 + y * 1113))))))))| <=
        3631363 := by
    calc
      |(147840 : Real) + y *
          (384120 + y *
            (676940 + y *
              (846582 + y *
                (764664 + y *
                  (497870 + y *
                    (228660 + y * (70470 + y * (13104 + y * 1113))))))))| <=
          147840 + 3483523 := abs_horner_step (by norm_num) hy h3
      _ = 3631363 := by norm_num
  have h1 :
      |(34916 : Real) + y *
          (147840 + y *
            (384120 + y *
              (676940 + y *
                (846582 + y *
                  (764664 + y *
                    (497870 + y *
                      (228660 + y * (70470 + y * (13104 + y * 1113)))))))))| <=
        3666279 := by
    calc
      |(34916 : Real) + y *
          (147840 + y *
            (384120 + y *
              (676940 + y *
                (846582 + y *
                  (764664 + y *
                    (497870 + y *
                      (228660 + y * (70470 + y * (13104 + y * 1113)))))))))| <=
          34916 + 3631363 := abs_horner_step (by norm_num) hy h2
      _ = 3666279 := by norm_num
  have h0 :
      |(3864 : Real) + y *
          (34916 + y *
            (147840 + y *
              (384120 + y *
                (676940 + y *
                  (846582 + y *
                    (764664 + y *
                      (497870 + y *
                        (228660 + y *
                          (70470 + y * (13104 + y * 1113))))))))))| <=
        3670143 := by
    calc
      |(3864 : Real) + y *
          (34916 + y *
            (147840 + y *
              (384120 + y *
                (676940 + y *
                  (846582 + y *
                    (764664 + y *
                      (497870 + y *
                        (228660 + y *
                          (70470 + y * (13104 + y * 1113))))))))))| <=
          3864 + 3666279 := abs_horner_step (by norm_num) hy h1
      _ = 3670143 := by norm_num
  simpa [dimensionlessFourthOrderNumerator, fourthOrderCoefficientSum] using h0

/-- A convenient coarse envelope obtained by replacing every `rho^k` by one. -/
def coarseFourthOrderTubeConstant (rho : Real) : Real :=
  fourthOrderCoefficientSum / (1 - rho) ^ 12

/-- The sharp radius-dependent constant is no larger than the coefficient-sum
envelope on `0 <= rho < 1`. -/
theorem fourthOrderTubeConstant_le_coarse
    {rho : Real} (hrho0 : 0 <= rho) (hrho1 : rho < 1) :
    fourthOrderTubeConstant rho <= coarseFourthOrderTubeConstant rho := by
  have habs : |rho| <= 1 := by simpa [abs_of_nonneg hrho0] using hrho1.le
  have hpolyAbs :=
    abs_dimensionlessFourthOrderNumerator_le_coefficientSum habs
  have hpoly0 : 0 <= dimensionlessFourthOrderNumerator rho := by
    unfold dimensionlessFourthOrderNumerator
    positivity
  have hpoly : dimensionlessFourthOrderNumerator rho <=
      fourthOrderCoefficientSum := by
    simpa [abs_of_nonneg hpoly0] using hpolyAbs
  unfold fourthOrderTubeConstant coarseFourthOrderTubeConstant
  exact (div_le_div_iff_of_pos_right
    (pow_pos (sub_pos.mpr hrho1) 12)).2 hpoly

/-- The homogeneous numerator is exactly the dimensionless polynomial after
factoring out `-r0^11`. -/
theorem fourthOrderRemainderNumerator_eq_dimensionless
    {r0 x : Real} (hr0 : r0 ≠ 0) :
    fourthOrderRemainderNumerator r0 x =
      -r0 ^ 11 * dimensionlessFourthOrderNumerator (x / r0) := by
  unfold fourthOrderRemainderNumerator dimensionlessFourthOrderNumerator
  field_simp [hr0]
  ring

/-- Exact dimensionless formula for the fourth-order LJ remainder. -/
theorem bondPotential_sub_localAlphaBetaPotential_eq_dimensionless
    {depth r0 x : Real} (hr0 : r0 ≠ 0) (hbond : r0 + x ≠ 0) :
    bondPotential depth r0 x - localAlphaBetaPotential depth r0 x =
      -depth * (x / r0) ^ 5 *
        dimensionlessFourthOrderNumerator (x / r0) /
          (1 + x / r0) ^ 12 := by
  rw [bondPotential_sub_localAlphaBetaPotential_factor hr0 hbond]
  unfold fourthOrderRemainderFactor
  rw [fourthOrderRemainderNumerator_eq_dimensionless hr0]
  field_simp [hr0, hbond]

/-- The radius polynomial is positive for every nonnegative tube radius. -/
theorem dimensionlessFourthOrderNumerator_pos_of_nonneg
    {rho : Real} (hrho : 0 <= rho) :
    0 < dimensionlessFourthOrderNumerator rho := by
  unfold dimensionlessFourthOrderNumerator
  positivity

/-- The sharp explicit tube constant is strictly positive before the singular
tube radius `rho = 1`. -/
theorem fourthOrderTubeConstant_pos {rho : Real}
    (hrho0 : 0 <= rho) (hrho1 : rho < 1) :
    0 < fourthOrderTubeConstant rho := by
  unfold fourthOrderTubeConstant
  exact div_pos (dimensionlessFourthOrderNumerator_pos_of_nonneg hrho0)
    (pow_pos (sub_pos.mpr hrho1) 12)

theorem fourthOrderTubeConstant_nonneg {rho : Real}
    (hrho0 : 0 <= rho) (hrho1 : rho < 1) :
    0 <= fourthOrderTubeConstant rho :=
  (fourthOrderTubeConstant_pos hrho0 hrho1).le

/-- Finiteness recorded in `ENNReal`: the explicit real envelope has no
infinite exceptional value. -/
theorem fourthOrderTubeConstant_ofReal_ne_top (rho : Real) :
    ENNReal.ofReal (fourthOrderTubeConstant rho) ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- A simple exact rational certificate for the practically useful tube
radius `rho = 1/40`. -/
theorem fourthOrderTubeConstant_one_div_forty_lt :
    fourthOrderTubeConstant (1 / 40 : Real) < 6553 := by
  norm_num [fourthOrderTubeConstant, dimensionlessFourthOrderNumerator]

/-- At `rho = 1/40`, the complete fifth-order per-bond envelope is below
`6.4 * 10^-5` times the well depth. -/
theorem fourthOrderTubeConstant_mul_one_div_forty_pow_five_lt :
    fourthOrderTubeConstant (1 / 40 : Real) * (1 / 40 : Real) ^ 5 <
      (64 / 1000000 : Real) := by
  norm_num [fourthOrderTubeConstant, dimensionlessFourthOrderNumerator]


/-- Explicit fifth-order remainder estimate on a closed relative-strain tube. -/
theorem abs_bondPotential_sub_localAlphaBetaPotential_le
    {depth r0 rho x : Real}
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hx : |x| <= rho * r0) :
    |bondPotential depth r0 x - localAlphaBetaPotential depth r0 x| <=
      depth * fourthOrderTubeConstant rho * (|x| / r0) ^ 5 := by
  let y : Real := x / r0
  have hy : |y| <= rho := by
    dsimp [y]
    rw [abs_div, abs_of_pos hr0]
    exact (div_le_iff₀ hr0).2 hx
  have hyLower : -rho <= y := by
    calc
      -rho <= -|y| := neg_le_neg hy
      _ <= y := neg_abs_le y
  have hone : 0 < 1 + y := by linarith
  have hbase : 0 < 1 - rho := sub_pos.mpr hrho1
  have hbase_le : 1 - rho <= 1 + y := by linarith
  have hden_le : (1 - rho) ^ 12 <= (1 + y) ^ 12 :=
    pow_le_pow_left₀ hbase.le hbase_le 12
  have hbondPos : 0 < r0 + x := by
    have heq : r0 + x = r0 * (1 + y) := by
      dsimp [y]
      field_simp [ne_of_gt hr0]
    rw [heq]
    exact mul_pos hr0 hone
  rw [bondPotential_sub_localAlphaBetaPotential_eq_dimensionless
    (ne_of_gt hr0) (ne_of_gt hbondPos)]
  change
    |-depth * y ^ 5 * dimensionlessFourthOrderNumerator y /
        (1 + y) ^ 12| <= _
  have habs :
      |-depth * y ^ 5 * dimensionlessFourthOrderNumerator y /
          (1 + y) ^ 12| =
        depth * |y| ^ 5 * |dimensionlessFourthOrderNumerator y| /
          (1 + y) ^ 12 := by
    rw [abs_div, abs_mul, abs_mul, abs_neg, abs_pow,
      abs_pow, abs_of_nonneg hdepth, abs_of_pos hone]
  rw [habs]
  calc
    depth * |y| ^ 5 * |dimensionlessFourthOrderNumerator y| /
          (1 + y) ^ 12 <=
        depth * |y| ^ 5 * dimensionlessFourthOrderNumerator rho /
          (1 + y) ^ 12 := by
      apply (div_le_div_iff_of_pos_right (pow_pos hone 12)).2
      exact mul_le_mul_of_nonneg_left
        (abs_dimensionlessFourthOrderNumerator_le_radiusPolynomial hrho0 hy)
        (mul_nonneg hdepth (pow_nonneg (abs_nonneg y) 5))
    _ <= depth * |y| ^ 5 * dimensionlessFourthOrderNumerator rho /
          (1 - rho) ^ 12 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg
          (mul_nonneg hdepth (pow_nonneg (abs_nonneg y) 5))
          (dimensionlessFourthOrderNumerator_pos_of_nonneg hrho0).le)
        (pow_pos hbase 12) hden_le
    _ = depth * fourthOrderTubeConstant rho * (|x| / r0) ^ 5 := by
      dsimp [y]
      unfold fourthOrderTubeConstant
      rw [abs_div, abs_of_pos hr0]
      ring

/-- Per-site absolute fourth-order remainder for a finite periodic list of
bond strains. -/
def perSiteAbsoluteFourthOrderRemainder {N : Nat} [NeZero N]
    (depth r0 : Real) (strain : Lattice.Site N -> Real) : Real :=
  (∑ i : Lattice.Site N,
      |bondPotential depth r0 (strain i) -
        localAlphaBetaPotential depth r0 (strain i)|) / (N : Real)

/-- Summed per-site version of the pointwise estimate.  The right side keeps
the empirical fifth strain moment visible. -/
theorem perSiteAbsoluteFourthOrderRemainder_le_fifthMoment
    {N : Nat} [NeZero N]
    {depth r0 rho : Real} (strain : Lattice.Site N -> Real)
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (htube : forall i, |strain i| <= rho * r0) :
    perSiteAbsoluteFourthOrderRemainder depth r0 strain <=
      depth * fourthOrderTubeConstant rho *
        ((∑ i : Lattice.Site N, (|strain i| / r0) ^ 5) / (N : Real)) := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsum :
      (∑ i : Lattice.Site N,
        |bondPotential depth r0 (strain i) -
          localAlphaBetaPotential depth r0 (strain i)|) <=
      ∑ i : Lattice.Site N,
        depth * fourthOrderTubeConstant rho * (|strain i| / r0) ^ 5 := by
    exact Finset.sum_le_sum fun i _ =>
      abs_bondPotential_sub_localAlphaBetaPotential_le
        hdepth hr0 hrho0 hrho1 (htube i)
  unfold perSiteAbsoluteFourthOrderRemainder
  calc
    (∑ i : Lattice.Site N,
        |bondPotential depth r0 (strain i) -
          localAlphaBetaPotential depth r0 (strain i)|) / (N : Real) <=
      (∑ i : Lattice.Site N,
        depth * fourthOrderTubeConstant rho * (|strain i| / r0) ^ 5) /
          (N : Real) := (div_le_div_iff_of_pos_right hN).2 hsum
    _ = depth * fourthOrderTubeConstant rho *
        ((∑ i : Lattice.Site N, (|strain i| / r0) ^ 5) / (N : Real)) := by
      rw [<- Finset.mul_sum]
      ring

/-- If every bond lies in the same tube, the per-site remainder has a bound
independent of the lattice size. -/
theorem perSiteAbsoluteFourthOrderRemainder_le_tubePower
    {N : Nat} [NeZero N]
    {depth r0 rho : Real} (strain : Lattice.Site N -> Real)
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (htube : forall i, |strain i| <= rho * r0) :
    perSiteAbsoluteFourthOrderRemainder depth r0 strain <=
      depth * fourthOrderTubeConstant rho * rho ^ 5 := by
  have hmoment := perSiteAbsoluteFourthOrderRemainder_le_fifthMoment
    strain hdepth hr0 hrho0 hrho1 htube
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hratio : forall i : Lattice.Site N, |strain i| / r0 <= rho := fun i =>
    (div_le_iff₀ hr0).2 (htube i)
  have hsum :
      (∑ i : Lattice.Site N, (|strain i| / r0) ^ 5) <=
        ∑ _i : Lattice.Site N, rho ^ 5 := by
    exact Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hr0.le) (hratio i) 5
  have haverage :
      (∑ i : Lattice.Site N, (|strain i| / r0) ^ 5) / (N : Real) <=
        rho ^ 5 := by
    calc
      (∑ i : Lattice.Site N, (|strain i| / r0) ^ 5) / (N : Real) <=
          (∑ _i : Lattice.Site N, rho ^ 5) / (N : Real) :=
        (div_le_div_iff_of_pos_right hN).2 hsum
      _ = rho ^ 5 := by
        simp [Lattice.Site, ne_of_gt hN]
  exact hmoment.trans (mul_le_mul_of_nonneg_left haverage
    (mul_nonneg hdepth (fourthOrderTubeConstant_nonneg hrho0 hrho1)))

/-- Bonds whose strain lies in the closed relative Taylor tube. -/
def relativeTaylorGoodBondSet {N : Nat} [NeZero N] (r0 rho : Real)
    (strain : Lattice.Site N -> Real) : Finset (Lattice.Site N) :=
  Finset.univ.filter fun i => |strain i| <= rho * r0

/-- Per-site absolute Taylor remainder restricted to bonds in the local tube.
Bonds outside the tube are honestly omitted, not silently bounded by the local
Taylor estimate. -/
def perSiteGoodBondAbsoluteFourthOrderRemainder {N : Nat} [NeZero N]
    (depth r0 rho : Real) (strain : Lattice.Site N -> Real) : Real :=
  (∑ i ∈ relativeTaylorGoodBondSet r0 rho strain,
      |bondPotential depth r0 (strain i) -
        localAlphaBetaPotential depth r0 (strain i)|) / (N : Real)

/-- Uniform restricted-good-bond estimate, retaining the exact good-bond
fraction.  This endpoint can be combined with a separate bad-bond density
estimate without assuming that every bond lies in the Taylor tube. -/
theorem perSiteGoodBondAbsoluteFourthOrderRemainder_le_cardFraction
    {N : Nat} [NeZero N]
    {depth r0 rho : Real} (strain : Lattice.Site N -> Real)
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1) :
    perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 rho strain <=
      depth * fourthOrderTubeConstant rho * rho ^ 5 *
        ((relativeTaylorGoodBondSet r0 rho strain).card : Real) / (N : Real) := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hpoint : ∀ i ∈ relativeTaylorGoodBondSet r0 rho strain,
      |bondPotential depth r0 (strain i) -
        localAlphaBetaPotential depth r0 (strain i)| <=
        depth * fourthOrderTubeConstant rho * rho ^ 5 := by
    intro i hi
    have hx : |strain i| <= rho * r0 := by
      exact (Finset.mem_filter.mp hi).2
    have hrem := abs_bondPotential_sub_localAlphaBetaPotential_le
      hdepth hr0 hrho0 hrho1 hx
    have hratio : |strain i| / r0 <= rho := (div_le_iff₀ hr0).2 hx
    have hp : (|strain i| / r0) ^ 5 <= rho ^ 5 :=
      pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hr0.le) hratio 5
    exact hrem.trans (mul_le_mul_of_nonneg_left hp
      (mul_nonneg hdepth (fourthOrderTubeConstant_nonneg hrho0 hrho1)))
  have hsum :
      (∑ i ∈ relativeTaylorGoodBondSet r0 rho strain,
        |bondPotential depth r0 (strain i) -
          localAlphaBetaPotential depth r0 (strain i)|) <=
      ∑ _i ∈ relativeTaylorGoodBondSet r0 rho strain,
        depth * fourthOrderTubeConstant rho * rho ^ 5 :=
    Finset.sum_le_sum hpoint
  unfold perSiteGoodBondAbsoluteFourthOrderRemainder
  calc
    (∑ i ∈ relativeTaylorGoodBondSet r0 rho strain,
        |bondPotential depth r0 (strain i) -
          localAlphaBetaPotential depth r0 (strain i)|) / (N : Real) <=
      (∑ _i ∈ relativeTaylorGoodBondSet r0 rho strain,
        depth * fourthOrderTubeConstant rho * rho ^ 5) / (N : Real) :=
      (div_le_div_iff_of_pos_right hN).2 hsum
    _ = depth * fourthOrderTubeConstant rho * rho ^ 5 *
        ((relativeTaylorGoodBondSet r0 rho strain).card : Real) /
          (N : Real) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Balanced static low-density interface.  With tube radius `rho = t^2`
and dimensionless energy ratio `t^7`, the Taylor remainder divided by that
energy scale is bounded by `C(t^2) * t^3`, uniformly in `N`.  This is an
algebraic remainder statement, not a long-time dynamical comparison. -/
theorem perSiteAbsoluteFourthOrderRemainder_div_balancedEnergyRatio_le
    {N : Nat} [NeZero N]
    {depth r0 t : Real} (strain : Lattice.Site N -> Real)
    (hdepth : 0 < depth) (hr0 : 0 < r0)
    (ht0 : 0 < t) (ht1 : t < 1)
    (htube : forall i, |strain i| <= t ^ 2 * r0) :
    perSiteAbsoluteFourthOrderRemainder depth r0 strain /
        (depth * t ^ 7) <=
      fourthOrderTubeConstant (t ^ 2) * t ^ 3 := by
  have htSq0 : 0 <= t ^ 2 := sq_nonneg t
  have htSq1 : t ^ 2 < 1 := by
    have hprod : 0 < (1 - t) * (1 + t) :=
      mul_pos (sub_pos.mpr ht1) (by linarith)
    nlinarith
  have hrem := perSiteAbsoluteFourthOrderRemainder_le_tubePower
    strain hdepth.le hr0 htSq0 htSq1 htube
  have hden : 0 < depth * t ^ 7 := mul_pos hdepth (pow_pos ht0 7)
  calc
    perSiteAbsoluteFourthOrderRemainder depth r0 strain /
        (depth * t ^ 7) <=
      (depth * fourthOrderTubeConstant (t ^ 2) * (t ^ 2) ^ 5) /
        (depth * t ^ 7) := (div_le_div_iff_of_pos_right hden).2 hrem
    _ = fourthOrderTubeConstant (t ^ 2) * t ^ 3 := by
      field_simp [ne_of_gt hdepth, ne_of_gt ht0]

end

end ArchonPhysics.LennardJonesQuantitativeTaylorTube
