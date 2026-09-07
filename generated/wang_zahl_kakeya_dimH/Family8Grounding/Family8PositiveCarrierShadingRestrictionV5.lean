import Family8Grounding.Family8PositiveCarrierShadingRestrictionV4

/-!
# Total automatic carrier floor for the positive restriction, V5

Choose the actual finite positive minimum when the positive-carrier subtype
is nonempty, and the harmless value one when it is empty.  This yields an
unconditional nonzero finite floor; the floor inequality is vacuous in the
empty case.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PositiveCarrierShadingRestrictionV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8PositiveCarrierShadingRestrictionV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota] {F : ConvexFamily iota}

/-- Totalized minimum: the true minimum on a nonempty positive subtype, one
on the empty subtype. -/
def automaticPositiveCarrierVolumeFloor (Y : Shading F) : ENNReal :=
  if hpos : (positiveCarrierIndices Y).Nonempty then
    positiveCarrierVolumeFloor Y hpos
  else 1

theorem automaticPositiveCarrierVolumeFloor_le
    (Y : Shading F) (q : {i // i ∈ positiveCarrierIndices Y}) :
    automaticPositiveCarrierVolumeFloor Y ≤
      volume ((positiveCarrierShading Y).carrier q) := by
  have hpos : (positiveCarrierIndices Y).Nonempty := ⟨q.1, q.2⟩
  rw [automaticPositiveCarrierVolumeFloor, dif_pos hpos]
  exact positiveCarrierVolumeFloor_le Y hpos q

theorem automaticPositiveCarrierVolumeFloor_ne_zero (Y : Shading F) :
    automaticPositiveCarrierVolumeFloor Y ≠ 0 := by
  rw [automaticPositiveCarrierVolumeFloor]
  split
  · next hpos => exact positiveCarrierVolumeFloor_ne_zero Y hpos
  · simp

theorem automaticPositiveCarrierVolumeFloor_ne_top (Y : Shading F) :
    automaticPositiveCarrierVolumeFloor Y ≠ ∞ := by
  rw [automaticPositiveCarrierVolumeFloor]
  split
  · next hpos => exact positiveCarrierVolumeFloor_ne_top Y hpos
  · simp

#print axioms automaticPositiveCarrierVolumeFloor_le
#print axioms automaticPositiveCarrierVolumeFloor_ne_zero
#print axioms automaticPositiveCarrierVolumeFloor_ne_top

end

end Family8PositiveCarrierShadingRestrictionV5
