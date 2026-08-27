import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32ThreeShiftCGridV1

noncomputable section

/-!
# Two staggered real floor grids, exposed through three labels

For a positive radius `r`, labels `0` and `2` use the grid with boundaries
`2 r * ℤ`, while label `1` uses the translate with boundaries
`r + 2 r * ℤ`.  Thus label `2` deliberately repeats label `0`; this lets the
construction feed the existing `Fin 3` pigeonhole API without introducing a
third geometric perturbation.

Every real number is at distance at most `r` from the centre of its cell.
Moreover, any two numbers at distance at most `r` belong to a common cell in
at least one of the two staggered grids.  The half-open convention is important
at equality.
-/

/-- Grid `1` is translated by `r`; grids `0` and `2` coincide. -/
def threeShiftGridOffset (r : Real) (k : Fin 3) : Real :=
  if k = 1 then r else 0

/-- The integer cell code in the width-`2r` grid labelled by `k`. -/
def threeShiftFloorCode (r : Real) (k : Fin 3) (x : Real) : Int :=
  Int.floor ((x - threeShiftGridOffset r k) / (2 * r))

/-- Lower endpoint of a half-open grid cell. -/
def threeShiftCellLower (r : Real) (k : Fin 3) (m : Int) : Real :=
  threeShiftGridOffset r k + (m : Real) * (2 * r)

/-- Upper endpoint of a half-open grid cell. -/
def threeShiftCellUpper (r : Real) (k : Fin 3) (m : Int) : Real :=
  threeShiftGridOffset r k + ((m : Real) + 1) * (2 * r)

/-- Centre of the grid cell containing `x`. -/
def threeShiftCellCenter (r : Real) (k : Fin 3) (x : Real) : Real :=
  threeShiftCellLower r k (threeShiftFloorCode r k x) + r

@[simp] theorem threeShiftGridOffset_zero (r : Real) :
    threeShiftGridOffset r 0 = 0 := by
  simp [threeShiftGridOffset]

@[simp] theorem threeShiftGridOffset_one (r : Real) :
    threeShiftGridOffset r 1 = r := by
  simp [threeShiftGridOffset]

@[simp] theorem threeShiftGridOffset_two (r : Real) :
    threeShiftGridOffset r 2 = 0 := by
  simp [threeShiftGridOffset]

theorem threeShiftFloorCode_eq_of_mem_cell
    {r x : Real} (hr : 0 < r) (k : Fin 3) (m : Int)
    (hlo : threeShiftCellLower r k m ≤ x)
    (hhi : x < threeShiftCellUpper r k m) :
    threeShiftFloorCode r k x = m := by
  rw [threeShiftFloorCode, Int.floor_eq_iff]
  have hden : 0 < 2 * r := mul_pos (by norm_num) hr
  constructor
  · apply (le_div_iff₀ hden).2
    dsimp [threeShiftCellLower] at hlo
    linarith
  · apply (div_lt_iff₀ hden).2
    dsimp [threeShiftCellUpper] at hhi
    linarith

theorem mem_cell_of_threeShiftFloorCode_eq
    {r x : Real} (hr : 0 < r) (k : Fin 3) (m : Int)
    (hcode : threeShiftFloorCode r k x = m) :
    threeShiftCellLower r k m ≤ x ∧
      x < threeShiftCellUpper r k m := by
  have hden : 0 < 2 * r := mul_pos (by norm_num) hr
  have hfloor :
      (m : Real) ≤
          (x - threeShiftGridOffset r k) / (2 * r) ∧
        (x - threeShiftGridOffset r k) / (2 * r) < (m : Real) + 1 := by
    rw [← Int.floor_eq_iff]
    exact hcode
  constructor
  · have hscaled := (le_div_iff₀ hden).1 hfloor.1
    dsimp [threeShiftCellLower]
    linarith
  · have hscaled := (div_lt_iff₀ hden).1 hfloor.2
    dsimp [threeShiftCellUpper]
    linarith

/-- Normalising a scalar to its cell centre changes it by at most `r`. -/
theorem abs_sub_threeShiftCellCenter_le
    {r x : Real} (hr : 0 < r) (k : Fin 3) :
    |x - threeShiftCellCenter r k x| ≤ r := by
  have hcell := mem_cell_of_threeShiftFloorCode_eq hr k
    (threeShiftFloorCode r k x) rfl
  rw [abs_le]
  constructor <;>
    dsimp [threeShiftCellCenter, threeShiftCellLower,
      threeShiftCellUpper] at hcell ⊢ <;>
    linarith

private theorem exists_same_threeShiftFloorCode_of_le
    {r x y : Real} (hr : 0 < r) (hxy : x ≤ y) (hgap : y - x ≤ r) :
    ∃ k : Fin 3, threeShiftFloorCode r k x =
      threeShiftFloorCode r k y := by
  let n : Int := Int.floor ((x + r) / r)
  have hnlo : (n : Real) ≤ (x + r) / r := by
    exact Int.floor_le ((x + r) / r)
  have hnhi : (x + r) / r < (n : Real) + 1 := by
    exact Int.lt_floor_add_one ((x + r) / r)
  have hcenterLower : (n : Real) * r - r ≤ x := by
    have := (le_div_iff₀ hr).1 hnlo
    linarith
  have hxCenter : x < (n : Real) * r := by
    have := (div_lt_iff₀ hr).1 hnhi
    linarith
  have hyUpper : y < (n : Real) * r + r := by
    linarith
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · refine ⟨1, ?_⟩
    have hxlo : threeShiftCellLower r 1 (m - 1) ≤ x := by
      rw [hm] at hcenterLower
      simp only [threeShiftCellLower, threeShiftGridOffset_one]
      push_cast at hcenterLower ⊢
      nlinarith
    have hxhi : x < threeShiftCellUpper r 1 (m - 1) := by
      rw [hm] at hxCenter
      simp only [threeShiftCellUpper, threeShiftGridOffset_one]
      push_cast at hxCenter ⊢
      nlinarith
    have hylo : threeShiftCellLower r 1 (m - 1) ≤ y := hxlo.trans hxy
    have hyhi : y < threeShiftCellUpper r 1 (m - 1) := by
      rw [hm] at hyUpper
      simp only [threeShiftCellUpper, threeShiftGridOffset_one]
      push_cast at hyUpper ⊢
      nlinarith
    rw [threeShiftFloorCode_eq_of_mem_cell hr 1 (m - 1) hxlo hxhi,
      threeShiftFloorCode_eq_of_mem_cell hr 1 (m - 1) hylo hyhi]
  · refine ⟨0, ?_⟩
    have hxlo : threeShiftCellLower r 0 m ≤ x := by
      rw [hm] at hcenterLower
      simp only [threeShiftCellLower, threeShiftGridOffset_zero]
      push_cast at hcenterLower ⊢
      nlinarith
    have hxhi : x < threeShiftCellUpper r 0 m := by
      rw [hm] at hxCenter
      simp only [threeShiftCellUpper, threeShiftGridOffset_zero]
      push_cast at hxCenter ⊢
      nlinarith
    have hylo : threeShiftCellLower r 0 m ≤ y := hxlo.trans hxy
    have hyhi : y < threeShiftCellUpper r 0 m := by
      rw [hm] at hyUpper
      simp only [threeShiftCellUpper, threeShiftGridOffset_zero]
      push_cast at hyUpper ⊢
      nlinarith
    rw [threeShiftFloorCode_eq_of_mem_cell hr 0 m hxlo hxhi,
      threeShiftFloorCode_eq_of_mem_cell hr 0 m hylo hyhi]

/-- Two scalars at distance at most `r` have the same code in one staggered
grid.  Equality cases are covered by the half-open cell convention. -/
theorem exists_same_threeShiftFloorCode
    {r x y : Real} (hr : 0 < r) (hxy : |x - y| ≤ r) :
    ∃ k : Fin 3, threeShiftFloorCode r k x =
      threeShiftFloorCode r k y := by
  rcases le_total x y with hle | hle
  · exact exists_same_threeShiftFloorCode_of_le hr hle
      (by rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hxy; linarith)
  · obtain ⟨k, hk⟩ := exists_same_threeShiftFloorCode_of_le hr hle
      (by rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hxy; linarith)
    exact ⟨k, hk.symm⟩

theorem threeShiftCellCenter_eq_of_code_eq
    {r x y : Real} {k : Fin 3}
    (hcode : threeShiftFloorCode r k x = threeShiftFloorCode r k y) :
    threeShiftCellCenter r k x = threeShiftCellCenter r k y := by
  simp only [threeShiftCellCenter, hcode]

#print axioms threeShiftFloorCode_eq_of_mem_cell
#print axioms abs_sub_threeShiftCellCenter_le
#print axioms exists_same_threeShiftFloorCode
#print axioms threeShiftCellCenter_eq_of_code_eq

end

end FamilyStickyCinematicL32ThreeShiftCGridV1
