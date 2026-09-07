import Family8Grounding.Family8QuantitativeCarrierPopularityRestrictionV3

/-!
# Division-free same-object carrier-floor cross

This is the scalar seam used after a same-occurrence selection has already
fixed its source, block, side bucket, and bucket shading.  It converts source
density times an active-card area lower bound, together with literal mass
retention into that bucket, to a lower bound for that very bucket's
`quantitativeCarrierFloor`.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8SameOccurrenceCarrierFloorCrossV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8StickyParentPopularCanonicalUnionV1

noncomputable section

/-- Division-free carrier-floor cancellation on one literal bucket shading.
The card comparison is exactly the one later instantiated by
`bucketCard <= blockCard <= activeCard`; no global card equality or new
selection is assumed. -/
theorem sourceDensity_mul_area_le_sameObject_quantitativeCarrierFloor
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota} (Ybucket : Shading F)
    {sourceDensity area activeCard sourceMass J occurrenceLoss bucketLoss :
      ENNReal}
    (hbucket : Ybucket.shadingMass ≠ 0)
    (hdensityMass :
      sourceDensity * (activeCard * area) <= sourceMass)
    (hretained :
      J * sourceMass <=
        (occurrenceLoss * bucketLoss) * Ybucket.shadingMass)
    (hcount :
      (Fintype.card iota : ENNReal) * 2 <= 2 * activeCard) :
    J * (sourceDensity * area) <=
      ((occurrenceLoss * bucketLoss) * 2) *
        quantitativeCarrierFloor Ybucket := by
  let count : ENNReal := (Fintype.card iota : ENNReal) * 2
  let x : ENNReal := J * (sourceDensity * area)
  have hindex : Nonempty iota :=
    nonempty_of_shadingMass_pos Ybucket (bot_lt_iff_ne_bot.mpr hbucket)
  have hcardPos : 0 < Fintype.card iota :=
    Fintype.card_pos_iff.mpr hindex
  have hcount0 : count ≠ 0 := by
    dsimp only [count]
    exact mul_ne_zero (by exact_mod_cast hcardPos.ne') (by norm_num)
  have hcountTop : count ≠ ∞ := by
    dsimp only [count]
    exact ENNReal.mul_ne_top (by simp) (by norm_num)
  have hxActive : x * activeCard <=
      (occurrenceLoss * bucketLoss) * Ybucket.shadingMass := by
    calc
      x * activeCard =
          J * (sourceDensity * (activeCard * area)) := by
        simp only [x]
        ac_rfl
      _ <= J * sourceMass := mul_le_mul' le_rfl hdensityMass
      _ <= (occurrenceLoss * bucketLoss) * Ybucket.shadingMass := hretained
  have hcross : x * count <=
      ((occurrenceLoss * bucketLoss) * 2) * Ybucket.shadingMass := by
    calc
      x * count <= x * (2 * activeCard) :=
        mul_le_mul' le_rfl (by simpa only [count] using hcount)
      _ = 2 * (x * activeCard) := by ac_rfl
      _ <= 2 * ((occurrenceLoss * bucketLoss) * Ybucket.shadingMass) :=
        mul_le_mul' le_rfl hxActive
      _ = ((occurrenceLoss * bucketLoss) * 2) * Ybucket.shadingMass := by
        ac_rfl
  have hfloor : quantitativeCarrierFloor Ybucket =
      Ybucket.shadingMass / count := by
    simpa only [count] using
      (quantitativeCarrierFloor_eq_mass_div_card_mul_two
        Ybucket hbucket)
  change x <=
    ((occurrenceLoss * bucketLoss) * 2) *
      quantitativeCarrierFloor Ybucket
  rw [hfloor]
  rw [show ((occurrenceLoss * bucketLoss) * 2) *
      (Ybucket.shadingMass / count) =
      (((occurrenceLoss * bucketLoss) * 2) *
        Ybucket.shadingMass) / count by
    simp only [div_eq_mul_inv]
    ac_rfl]
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl hcount0) (Or.inl hcountTop)).2 hcross

#print axioms
  sourceDensity_mul_area_le_sameObject_quantitativeCarrierFloor

end
end Family8SameOccurrenceCarrierFloorCrossV1
