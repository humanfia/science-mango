import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtPathV1

set_option autoImplicit false

open Function Set

namespace FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1

open FamilyStickyCinematicL32Prop41RectangularSkirtPathV1

noncomputable section

/-!
# The literal side-entry parameter on the rectangular-skirt loop

The graph is the first piece of the six-piece skirt path.  Because the five
nested `Path.trans` operations successively halve the preceding parameter
interval, the graph piece occupies `[0,1/32]`.  The definition below is the
actual scalar loop parameter of the graph point with horizontal parameter
`theta`; it is not an arbitrary ordering key.
-/

/-- Scalar loop parameter of `(f theta, theta)` on the graph piece of the
literal six-piece rectangular skirt. -/
def rectangularSkirtGraphEntryParameter
    (A B theta : Real) : Real :=
  (theta - A) / (32 * (B - A))

/-- An interior graph point enters during the open graph-piece parameter
interval `(0,1/32)`. -/
theorem rectangularSkirtGraphEntryParameter_mem_Ioo
    {A B theta : Real} (hAB : A < B) (htheta : theta ∈ Ioo A B) :
    rectangularSkirtGraphEntryParameter A B theta ∈
      Ioo (0 : Real) (1 / 32 : Real) := by
  have hden : 0 < 32 * (B - A) := mul_pos (by norm_num) (sub_pos.mpr hAB)
  constructor
  · exact div_pos (sub_pos.mpr htheta.1) hden
  · rw [rectangularSkirtGraphEntryParameter, div_lt_iff₀ hden]
    calc
      theta - A < B - A := sub_lt_sub_right htheta.2 A
      _ = (1 / 32 : Real) * (32 * (B - A)) := by ring

/-- The scalar loop key has exactly the same strict order as the graph
parameter.  Thus any later finite tie-break is invisible whenever geometric
entry points are distinct. -/
theorem rectangularSkirtGraphEntryParameter_lt_iff
    {A B theta phi : Real} (hAB : A < B) :
    rectangularSkirtGraphEntryParameter A B theta <
        rectangularSkirtGraphEntryParameter A B phi ↔
      theta < phi := by
  have hden : 0 < 32 * (B - A) := mul_pos (by norm_num) (sub_pos.mpr hAB)
  rw [rectangularSkirtGraphEntryParameter,
    rectangularSkirtGraphEntryParameter,
    div_lt_div_iff_of_pos_right hden, sub_lt_sub_iff_right]

/-- The parameter above evaluates the explicit skirt loop at the intended
graph point. -/
theorem rectangularSkirtLoop_graphEntryParameter
    (f : Real -> Real) {A B M depth theta : Real}
    (hAB : A < B) (hdepth : 0 <= depth)
    (hf : ContinuousOn f (Icc A B))
    (htheta : theta ∈ Icc A B) :
    rectangularSkirtLoop f A B M depth hAB.le hdepth hf
        (rectangularSkirtGraphEntryParameter A B theta) =
      (f theta, theta) := by
  let e := rectangularSkirtGraphEntryParameter A B theta
  let s := (theta - A) / (B - A)
  have hBA : 0 < B - A := sub_pos.mpr hAB
  have hs : s ∈ Icc (0 : Real) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr htheta.1) hBA.le
    · dsimp [s]
      rw [div_le_one hBA]
      linarith [htheta.2]
  have he0 : 0 <= e := by
    exact div_nonneg (sub_nonneg.mpr htheta.1)
      (mul_nonneg (by norm_num) hBA.le)
  have he32 : e <= (1 / 32 : Real) := by
    dsimp [e, rectangularSkirtGraphEntryParameter]
    rw [div_le_iff₀ (mul_pos (by norm_num) hBA)]
    calc
      theta - A <= B - A := sub_le_sub_right htheta.2 A
      _ = (1 / 32 : Real) * (32 * (B - A)) := by ring
  have heHalf : e <= (1 / 2 : Real) := he32.trans (by norm_num)
  have heQuarter : 2 * e <= (1 / 2 : Real) := by nlinarith
  have heEighth : 2 * (2 * e) <= (1 / 2 : Real) := by nlinarith
  have heSixteenth : 2 * (2 * (2 * e)) <= (1 / 2 : Real) := by
    nlinarith
  have heThirtySecond : 2 * (2 * (2 * (2 * e))) <=
      (1 / 2 : Real) := by nlinarith
  have h32 : 2 * (2 * (2 * (2 * (2 * e)))) = s := by
    dsimp [e, s, rectangularSkirtGraphEntryParameter]
    field_simp
    ring
  rw [rectangularSkirtLoop]
  unfold rectangularSkirtPath
  rw [Path.extend_trans_of_le_half _ _ heHalf,
    Path.extend_trans_of_le_half _ _ heQuarter,
    Path.extend_trans_of_le_half _ _ heEighth,
    Path.extend_trans_of_le_half _ _ heSixteenth,
    Path.extend_trans_of_le_half _ _ heThirtySecond,
    h32, Path.extend_apply _ hs]
  change
    (f (AffineMap.lineMap A B s), AffineMap.lineMap A B s) =
      (f theta, theta)
  have hline : AffineMap.lineMap A B s = theta := by
    dsimp [s]
    rw [AffineMap.lineMap_apply_module']
    change ((theta - A) / (B - A)) * (B - A) + A = theta
    rw [div_mul_cancel₀ _ hBA.ne']
    ring
  simp [hline]

#print axioms rectangularSkirtGraphEntryParameter
#print axioms rectangularSkirtGraphEntryParameter_mem_Ioo
#print axioms rectangularSkirtGraphEntryParameter_lt_iff
#print axioms rectangularSkirtLoop_graphEntryParameter

end

end FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1
