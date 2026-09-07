import Family8Grounding.Family8StickyMassPopularFixedKatzTaoCoefficientV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyMassPopularFixedKatzTaoSourceCapCrossEnvelopeV2

/-!
# Division-free source-cap envelopes

The source-to-tau restriction loses one exact natural fibre cap.  Bounding
the divided source floor by a separate delta power is too expensive for the
Section 8 parameter ladder.  These lemmas keep the cap cross-multiplied so
that it can cancel against the first-factor estimate on the same data.

V1 was a failed syntax draft and is deliberately not imported.
-/

/-- A positive finite natural cap can be moved across an exact divided
source floor. -/
theorem le_source_of_natCap_mul_le_sourceFloor
    (sourceCap : Nat) (hsourceCap : 0 < sourceCap)
    {lhs sourceFloor source : ENNReal}
    (hcross : (sourceCap : ENNReal) * lhs <= sourceFloor)
    (hfloor : sourceFloor / (sourceCap : ENNReal) <= source) :
    lhs <= source := by
  have hcap0 : (sourceCap : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hsourceCap
  have hcapTop : (sourceCap : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdiv : lhs <= sourceFloor / (sourceCap : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hcap0) (Or.inl hcapTop)).2
    simpa only [mul_comm] using hcross
  exact hdiv.trans hfloor

/-- The same exact cancellation with an arbitrary factor multiplying the
retained source mass. -/
theorem le_mul_source_of_natCap_mul_le_mul_sourceFloor
    (sourceCap : Nat) (hsourceCap : 0 < sourceCap)
    {lhs factor sourceFloor source : ENNReal}
    (hcross : (sourceCap : ENNReal) * lhs <= factor * sourceFloor)
    (hfloor : sourceFloor / (sourceCap : ENNReal) <= source) :
    lhs <= factor * source := by
  have hcap0 : (sourceCap : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hsourceCap
  have hcapTop : (sourceCap : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsourceFloor : sourceFloor <= (sourceCap : ENNReal) * source := by
    calc
      sourceFloor =
          (sourceFloor / (sourceCap : ENNReal)) * (sourceCap : ENNReal) :=
        (ENNReal.div_mul_cancel hcap0 hcapTop).symm
      _ <= source * (sourceCap : ENNReal) := mul_le_mul' hfloor le_rfl
      _ = (sourceCap : ENNReal) * source := mul_comm _ _
  apply (ENNReal.mul_le_mul_iff_left hcap0 hcapTop).mp
  calc
    lhs * (sourceCap : ENNReal) = (sourceCap : ENNReal) * lhs := mul_comm _ _
    _ <= factor * sourceFloor := hcross
    _ <= factor * ((sourceCap : ENNReal) * source) :=
      mul_le_mul' le_rfl hsourceFloor
    _ = (factor * source) * (sourceCap : ENNReal) := by ac_rfl

/-- Pair of envelopes in exactly the shape consumed by the fixed-Katz--Tao
mass-popular endpoint: the density term is unscaled, while the base term is
multiplied by its genuine scale/Frostman factor. -/
theorem sourceCap_cross_envelopes
    (sourceCap : Nat) (hsourceCap : 0 < sourceCap)
    {densityLHS baseLHS baseFactor sourceFloor source : ENNReal}
    (hfloor : sourceFloor / (sourceCap : ENNReal) <= source)
    (hdensityCross : (sourceCap : ENNReal) * densityLHS <= sourceFloor)
    (hbaseCross : (sourceCap : ENNReal) * baseLHS <=
      baseFactor * sourceFloor) :
    densityLHS <= source /\ baseLHS <= baseFactor * source := by
  exact ⟨
    le_source_of_natCap_mul_le_sourceFloor sourceCap hsourceCap
      hdensityCross hfloor,
    le_mul_source_of_natCap_mul_le_mul_sourceFloor sourceCap hsourceCap
      hbaseCross hfloor⟩

#print axioms le_source_of_natCap_mul_le_sourceFloor
#print axioms le_mul_source_of_natCap_mul_le_mul_sourceFloor
#print axioms sourceCap_cross_envelopes

end Family8StickyMassPopularFixedKatzTaoSourceCapCrossEnvelopeV2
