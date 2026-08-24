import ChallengeDeps
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

open Set
open scoped BigOperators

namespace FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

/-!
# Finite floor-grid representatives for bounded real parameters

This is the purely finite counting half of the polynomial test net implicit
at GWZ Appendix line 2685.  A parameter object is encoded by finitely many
real coordinates.  On a positive floor grid, every occupied code gets one
actual source representative.  Hence representatives retain nonlinear
structure (in particular, an orthonormal frame), while equality of codes
gives coordinatewise closeness.

The index type is a subtype of an explicit product of integer intervals.
Its cardinality is bounded by the interval length to the number of real
coordinates; no compactness or unquantified `FiniteTestNetCompleteness`
field is used.
-/

variable {parameter coordIndex : Type*}
variable [Fintype coordIndex] [DecidableEq coordIndex]

/-- Width-`mesh` floor code of a finite list of real coordinates. -/
def floorCode (mesh : Real) (coord : parameter → coordIndex → Real)
    (p : parameter) : coordIndex → Int :=
  fun i => Int.floor (coord p i / mesh)

omit [Fintype coordIndex] [DecidableEq coordIndex] in
/-- Equal positive-width floor codes force coordinatewise distance less
than one mesh. -/
theorem abs_coord_sub_lt_of_floorCode_eq
    {mesh : Real} (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real) {p q : parameter}
    (hcode : floorCode mesh coord p = floorCode mesh coord q)
    (i : coordIndex) :
    |coord p i - coord q i| < mesh := by
  have hfloor :
      Int.floor (coord p i / mesh) =
        Int.floor (coord q i / mesh) := congrFun hcode i
  have hscaled :
      |coord p i / mesh - coord q i / mesh| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor hfloor
  rw [← sub_div, abs_div, abs_of_pos hmesh] at hscaled
  exact (div_lt_one hmesh).mp hscaled

/-- Integer interval supporting all floor codes of coordinates bounded by
`bound` in absolute value. -/
def codeInterval (mesh bound : Real) : Finset Int :=
  Finset.Icc (Int.floor (-bound / mesh)) (Int.floor (bound / mesh))

/-- Explicit finite product code space. -/
abbrev BoundedCode (coordIndex : Type*) [Fintype coordIndex]
    (mesh bound : Real) :=
  coordIndex → ↥(codeInterval mesh bound)

/-- A bounded coordinate object has a code in the explicit integer product
box. -/
def boundedFloorCode
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound)
    (p : parameter) : BoundedCode coordIndex mesh bound :=
  fun i => ⟨floorCode mesh coord p i, by
    change floorCode mesh coord p i ∈
      Finset.Icc (Int.floor (-bound / mesh)) (Int.floor (bound / mesh))
    rw [Finset.mem_Icc]
    constructor
    · apply Int.floor_le_floor
      apply (div_le_div_iff_of_pos_right hmesh).2
      exact (neg_le_of_abs_le (hbound p i))
    · apply Int.floor_le_floor
      apply (div_le_div_iff_of_pos_right hmesh).2
      exact le_of_abs_le (hbound p i)⟩

omit [DecidableEq coordIndex] in
@[simp]
theorem boundedFloorCode_val
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound)
    (p : parameter) (i : coordIndex) :
    (boundedFloorCode mesh bound hmesh coord hbound p i : Int) =
      floorCode mesh coord p i := rfl

/-- The finite type of codes that are actually occupied by source
parameters. -/
def OccupiedCode
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound) :=
  {c : BoundedCode coordIndex mesh bound //
    ∃ p : parameter,
      boundedFloorCode mesh bound hmesh coord hbound p = c}

noncomputable instance occupiedCodeFintype
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound) :
    Fintype (OccupiedCode mesh bound hmesh coord hbound) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- An actual source representative of an occupied floor code. -/
noncomputable def representative
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound)
    (c : OccupiedCode mesh bound hmesh coord hbound) : parameter :=
  Classical.choose c.property

omit [DecidableEq coordIndex] in
theorem representative_code
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound)
    (c : OccupiedCode mesh bound hmesh coord hbound) :
    boundedFloorCode mesh bound hmesh coord hbound
        (representative mesh bound hmesh coord hbound c) = c.1 :=
  Classical.choose_spec c.property

/-- The occupied code containing a source parameter. -/
def ownCode
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound)
    (p : parameter) : OccupiedCode mesh bound hmesh coord hbound :=
  ⟨boundedFloorCode mesh bound hmesh coord hbound p, ⟨p, rfl⟩⟩

omit [DecidableEq coordIndex] in
/-- Every source parameter is coordinatewise within one mesh of its actual
representative. -/
theorem abs_coord_sub_representative_ownCode_lt
    {mesh bound : Real} (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound)
    (p : parameter) (i : coordIndex) :
    |coord p i - coord
      (representative mesh bound hmesh coord hbound
        (ownCode mesh bound hmesh coord hbound p)) i| < mesh := by
  apply abs_coord_sub_lt_of_floorCode_eq hmesh coord
  funext j
  have hrep := representative_code mesh bound hmesh coord hbound
    (ownCode mesh bound hmesh coord hbound p)
  exact congrArg Subtype.val (congrFun hrep j) |>.symm

/-- Exact polynomial-size cardinality bound for the occupied index type. -/
theorem card_occupiedCode_le
    (mesh bound : Real) (hmesh : 0 < mesh)
    (coord : parameter → coordIndex → Real)
    (hbound : ∀ p i, |coord p i| ≤ bound) :
    Fintype.card (OccupiedCode mesh bound hmesh coord hbound) ≤
      ((Int.floor (bound / mesh) + 1 -
          Int.floor (-bound / mesh)).toNat) ^ Fintype.card coordIndex := by
  calc
    Fintype.card (OccupiedCode mesh bound hmesh coord hbound) ≤
        Fintype.card (BoundedCode coordIndex mesh bound) :=
      Fintype.card_le_of_injective
        (fun c : OccupiedCode mesh bound hmesh coord hbound => c.1)
        Subtype.val_injective
    _ = ((Int.floor (bound / mesh) + 1 -
          Int.floor (-bound / mesh)).toNat) ^ Fintype.card coordIndex := by
      rw [Fintype.card_fun, Fintype.card_coe]
      unfold codeInterval
      rw [Int.card_Icc]

#print axioms abs_coord_sub_lt_of_floorCode_eq
#print axioms boundedFloorCode
#print axioms representative_code
#print axioms abs_coord_sub_representative_ownCode_lt
#print axioms card_occupiedCode_le

end
end FamilyStickyRandomFiniteFloorParameterNetV1
