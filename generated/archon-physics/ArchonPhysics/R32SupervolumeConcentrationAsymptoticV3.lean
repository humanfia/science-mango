import ArchonPhysics.R32SupervolumeJointLimit
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# R32 supervolume concentration asymptotics

For `g j = 1 / (j + 1)`, this module proves that the concentration cost

`N j * (g j)⁻⁶ * exp (-c * N j * (g j)⁸)`

tends to zero under the sole volume condition
`N j ≥ ceil ((g j)⁻¹²)`.  No upper bound on `N` is assumed.  It also gives an
explicit finite grid covering `[0, T / g²]` at mesh `g⁴`, with cardinality
`O(T g⁻⁶ + 1)`.
-/

namespace ArchonPhysics.R32SupervolumeConcentrationAsymptotic

open ArchonPhysics.R32SupervolumeJointLimit
open Filter Set Topology

noncomputable section

/-! ## An explicit kinetic time grid -/

/-- A finite family is a time net when every point of the interval is within
`mesh` of one of its values. -/
def IsTimeNet {I : Type*} (horizon mesh : Real) (grid : I → Real) : Prop :=
  ∀ t ∈ Icc 0 horizon, ∃ i : I, |t - grid i| ≤ mesh

/-- Number of grid points used for `[0, T / g²]` at mesh `g⁴`. -/
def kineticTimeGridCard (T g : Real) : Nat :=
  Nat.ceil (T / g ^ 6) + 1

/-- The equally spaced kinetic time grid `i g⁴`. -/
def kineticTimeGrid (T g : Real) : Fin (kineticTimeGridCard T g) → Real :=
  fun i ↦ (i.val : Real) * g ^ 4

@[simp]
theorem card_kineticTimeGrid (T g : Real) :
    Fintype.card (Fin (kineticTimeGridCard T g)) =
      kineticTimeGridCard T g := by
  simp

/-- The concrete grid covers the full kinetic interval with radius `g⁴`. -/
theorem kineticTimeGrid_isTimeNet
    (T g : Real) (hT : 0 ≤ T) (hg : 0 < g) :
    IsTimeNet (T / g ^ 2) (g ^ 4) (kineticTimeGrid T g) := by
  intro t ht
  let q : Real := t / g ^ 4
  have hg4 : 0 < g ^ 4 := pow_pos hg 4
  have hg6 : 0 < g ^ 6 := pow_pos hg 6
  have hq_nonneg : 0 ≤ q := div_nonneg ht.1 hg4.le
  have ht_mul : t * g ^ 2 ≤ T := by
    apply (le_div_iff₀ (pow_pos hg 2)).mp
    simpa [mul_comm] using ht.2
  have hq_le : q ≤ T / g ^ 6 := by
    apply (le_div_iff₀ hg6).2
    dsimp [q]
    calc
      (t / g ^ 4) * g ^ 6 = t * g ^ 2 := by
        field_simp [ne_of_gt hg] <;> ring
      _ ≤ T := ht_mul
  have hceil_le : Nat.ceil q ≤ Nat.ceil (T / g ^ 6) :=
    Nat.ceil_mono hq_le
  let i : Fin (kineticTimeGridCard T g) :=
    ⟨Nat.ceil q, by
      rw [kineticTimeGridCard]
      omega⟩
  refine ⟨i, ?_⟩
  have hceil_error : |(Nat.ceil q : Real) - q| ≤ 1 :=
    Nat.abs_ceil_sub_le hq_nonneg
  have ht_eq : t = q * g ^ 4 := by
    dsimp [q]
    field_simp [ne_of_gt hg]
  change |t - (i.val : Real) * g ^ 4| ≤ g ^ 4
  rw [ht_eq]
  calc
    |q * g ^ 4 - (i.val : Real) * g ^ 4| =
        |q - (i.val : Real)| * |g ^ 4| := by
      rw [← sub_mul, abs_mul]
    _ ≤ 1 * g ^ 4 := by
      rw [abs_of_pos hg4]
      gcongr
      simpa [i, abs_sub_comm] using hceil_error
    _ = g ^ 4 := one_mul _

/-- Sharp ceiling-level cardinality estimate for the concrete grid. -/
theorem kineticTimeGrid_card_le
    (T g : Real) (hT : 0 ≤ T) (hg : 0 < g) :
    (Fintype.card (Fin (kineticTimeGridCard T g)) : Real) ≤
      T / g ^ 6 + 2 := by
  rw [card_kineticTimeGrid, kineticTimeGridCard, Nat.cast_add, Nat.cast_one]
  have hx : 0 ≤ T / g ^ 6 :=
    div_nonneg hT (pow_pos hg 6).le
  linarith [Nat.ceil_lt_add_one hx]

/-- Polynomial reading of the grid bound, with explicit constant `2`. -/
theorem kineticTimeGrid_card_le_polynomial
    (T g : Real) (hT : 0 ≤ T) (hg : 0 < g) :
    (Fintype.card (Fin (kineticTimeGridCard T g)) : Real) ≤
      2 * (T * g⁻¹ ^ 6 + 1) := by
  have hcard := kineticTimeGrid_card_le T g hT hg
  have hrewrite : T / g ^ 6 = T * g⁻¹ ^ 6 := by
    rw [div_eq_mul_inv, inv_pow]
  have hx : 0 ≤ T * g⁻¹ ^ 6 := by positivity
  rw [hrewrite] at hcard
  linarith

/-! ## Arbitrary-supervolume exponential domination -/

/-- The polynomial union-bound cost accompanying the fixed-time exponent
`c N g⁸`. -/
def concentrationUnionCost (c : Real) (N : Nat → Nat) (j : Nat) : Real :=
  (N j : Real) * (inverseLinearCoupling j)⁻¹ ^ 6 *
    Real.exp
      (-c * (N j : Real) * inverseLinearCoupling j ^ 8)

/-- The inverse-twelfth-power ceiling gives the corresponding real lower
bound. -/
theorem inverse_pow_twelve_le_of_ceiling_le
    {g : Real} {N : Nat} (hN : inverseTwelfthPowerCeiling g ≤ N) :
    g ^ (-12 : Int) ≤ (N : Real) := by
  exact Nat.le_of_ceil_le hN

/-- A pointwise envelope using no upper bound on `N`. -/
theorem concentrationUnionCost_le_envelope
    (c g : Real) (N : Nat) (hc : 0 < c) (hg : 0 < g)
    (hN : g ^ (-12 : Int) ≤ (N : Real)) :
    (N : Real) * g⁻¹ ^ 6 * Real.exp (-c * (N : Real) * g ^ 8) ≤
      (2 / c) * Real.exp (-1) * g⁻¹ ^ 14 *
        Real.exp (-(c / 2) * g⁻¹ ^ 4) := by
  let y : Real := c * (N : Real) * g ^ 8
  let z : Real := y / 2
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hz_bound : z * Real.exp (-z) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one z
  have hpow_lower : g⁻¹ ^ 12 ≤ (N : Real) := by
    simpa [zpow_neg, inv_pow] using hN
  have hz_lower : (c / 2) * g⁻¹ ^ 4 ≤ z := by
    dsimp [z, y]
    have hmultiplier : 0 ≤ (c / 2) * g ^ 8 := by positivity
    have hscaled :=
      mul_le_mul_of_nonneg_left hpow_lower hmultiplier
    calc
      (c / 2) * g⁻¹ ^ 4 =
          ((c / 2) * g ^ 8) * g⁻¹ ^ 12 := by
        field_simp [hg0] <;> ring
      _ ≤ ((c / 2) * g ^ 8) * (N : Real) := hscaled
      _ = c * (N : Real) * g ^ 8 / 2 := by ring
  have hexp_bound : Real.exp (-z) ≤ Real.exp (-(c / 2) * g⁻¹ ^ 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hz_lower]
  have hfactor_nonneg : 0 ≤ (2 / c) * g⁻¹ ^ 14 := by positivity
  have hcoefficient :
      (N : Real) * g⁻¹ ^ 6 = ((2 / c) * g⁻¹ ^ 14) * z := by
    dsimp [z, y]
    field_simp [hc0, hg0] <;> ring
  have hexp_split : Real.exp (-y) = Real.exp (-z) * Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [z]
    ring
  calc
    (N : Real) * g⁻¹ ^ 6 * Real.exp (-c * (N : Real) * g ^ 8) =
        ((2 / c) * g⁻¹ ^ 14) *
          (z * Real.exp (-z)) * Real.exp (-z) := by
      rw [show -c * (N : Real) * g ^ 8 = -y by
        dsimp [y]
        ring]
      rw [hcoefficient, hexp_split]
      ring
    _ ≤ ((2 / c) * g⁻¹ ^ 14) * Real.exp (-1) * Real.exp (-z) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hz_bound hfactor_nonneg)
        (Real.exp_pos _).le
    _ ≤ ((2 / c) * g⁻¹ ^ 14) * Real.exp (-1) *
          Real.exp (-(c / 2) * g⁻¹ ^ 4) := by
      exact mul_le_mul_of_nonneg_left hexp_bound (by positivity)
    _ = (2 / c) * Real.exp (-1) * g⁻¹ ^ 14 *
          Real.exp (-(c / 2) * g⁻¹ ^ 4) := by ring

/-- Along `g j = 1 / (j + 1)`, the pointwise envelope tends to zero. -/
theorem concentrationEnvelope_tendsto_zero (c : Real) (hc : 0 < c) :
    Tendsto
      (fun j : Nat ↦
        (2 / c) * Real.exp (-1) * (inverseLinearCoupling j)⁻¹ ^ 14 *
          Real.exp (-(c / 2) * (inverseLinearCoupling j)⁻¹ ^ 4))
      atTop (nhds 0) := by
  let x : Nat → Real := fun j ↦ (j : Real) + 1
  have hx : Tendsto x atTop atTop := by
    apply tendsto_atTop.2
    intro lower
    filter_upwards [eventually_ge_atTop (Nat.ceil lower)] with j hj
    calc
      lower ≤ (Nat.ceil lower : Real) := Nat.le_ceil lower
      _ ≤ (j : Real) := by exact_mod_cast hj
      _ ≤ (j : Real) + 1 := by linarith
  have hbase : Tendsto
      (fun r : Real ↦ r ^ 14 * Real.exp (-(c / 2) * r ^ 4))
      atTop (nhds 0) := by
    refine squeeze_zero'
      (g := fun r : Real ↦ r ^ 14 * Real.exp (-r))
      (Filter.Eventually.of_forall fun r ↦ by positivity) ?_
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 14)
    filter_upwards [eventually_ge_atTop (max 1 (2 / c))] with r hr
    have hr_one : 1 ≤ r := (le_max_left 1 (2 / c)).trans hr
    have hr_nonneg : 0 ≤ r := zero_le_one.trans hr_one
    have hr_c : 2 / c ≤ r := (le_max_right 1 (2 / c)).trans hr
    have hcube : 2 / c ≤ r ^ 3 := by
      have hprod : 0 ≤ r * (r - 1) * (r + 1) := by positivity
      nlinarith
    have hmul : 1 ≤ (c / 2) * r ^ 3 := by
      calc
        1 = (c / 2) * (2 / c) := by
          field_simp [ne_of_gt hc] <;> ring
        _ ≤ (c / 2) * r ^ 3 :=
          mul_le_mul_of_nonneg_left hcube (by positivity)
    have hlinear : r ≤ (c / 2) * r ^ 4 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * ((c / 2) * r ^ 3) :=
          mul_le_mul_of_nonneg_left hmul hr_nonneg
        _ = (c / 2) * r ^ 4 := by ring
    have hexp : Real.exp (-(c / 2) * r ^ 4) ≤ Real.exp (-r) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hlinear]
    exact mul_le_mul_of_nonneg_left hexp (pow_nonneg hr_nonneg 14)
  have hcomposed := hbase.comp hx
  have hinv (j : Nat) : (inverseLinearCoupling j)⁻¹ = x j := by
    dsimp [x, inverseLinearCoupling]
    rw [inv_div]
    simp
  simpa [Function.comp_def, hinv, mul_assoc] using
    hcomposed.const_mul ((2 / c) * Real.exp (-1))

/-- Main arbitrary-supervolume statement.  The only schedule hypothesis is
the pointwise lower bound `N j ≥ ceil ((g j)⁻¹²)`; `N` may grow arbitrarily
faster. -/
theorem supervolume_concentration_cost_tendsto_zero
    (c : Real) (hc : 0 < c) (N : Nat → Nat)
    (hN : ∀ j,
      inverseTwelfthPowerCeiling (inverseLinearCoupling j) ≤ N j) :
    Tendsto
      (fun j ↦
        (N j : Real) * (inverseLinearCoupling j)⁻¹ ^ 6 *
          Real.exp
            (-c * (N j : Real) * inverseLinearCoupling j ^ 8))
      atTop (nhds 0) := by
  change Tendsto (concentrationUnionCost c N) atTop (nhds 0)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun j ↦ by
      unfold concentrationUnionCost
      positivity
  · exact Filter.Eventually.of_forall fun j ↦ by
      unfold concentrationUnionCost
      exact concentrationUnionCost_le_envelope c (inverseLinearCoupling j)
        (N j) hc (inverseLinearCoupling_pos j)
        (inverse_pow_twelve_le_of_ceiling_le (hN j))
  · exact concentrationEnvelope_tendsto_zero c hc

/-- Multiplication by a fixed time-window constant preserves the limit. -/
theorem supervolume_concentration_with_timeFactor_tendsto_zero
    (c T : Real) (hc : 0 < c) (N : Nat → Nat)
    (hN : ∀ j,
      inverseTwelfthPowerCeiling (inverseLinearCoupling j) ≤ N j) :
    Tendsto
      (fun j ↦
        T * ((N j : Real) * (inverseLinearCoupling j)⁻¹ ^ 6 *
          Real.exp
            (-c * (N j : Real) * inverseLinearCoupling j ^ 8)))
      atTop (nhds 0) := by
  simpa using
    (tendsto_const_nhds.mul
      (supervolume_concentration_cost_tendsto_zero c hc N hN))

/-- Specialization to the explicit joint limit. -/
theorem supervolumeJointLimit_concentration_cost_tendsto_zero
    (sizeCutoff : Real → Nat) (c : Real) (hc : 0 < c) :
    Tendsto
      (concentrationUnionCost c
        (supervolumeJointLimit sizeCutoff).systemSize)
      atTop (nhds 0) := by
  have hfloor : ∀ j,
      inverseTwelfthPowerCeiling (inverseLinearCoupling j) ≤
        (supervolumeJointLimit sizeCutoff).systemSize j := by
    intro j
    exact (Nat.le_max_right _ _).trans
      (supervolumeSystemSize_ge_requestedFloor sizeCutoff j)
  have hlimit :=
    supervolume_concentration_cost_tendsto_zero c hc
      (supervolumeJointLimit sizeCutoff).systemSize hfloor
  convert hlimit using 1 <;>
    funext j <;>
    simp only [concentrationUnionCost, inv_pow]

end

end ArchonPhysics.R32SupervolumeConcentrationAsymptotic
