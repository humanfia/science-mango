import FamilyStickyCinematicL32PyzQuasiProductGraphStripMeasureV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1

open FamilyStickyCinematicL32PyzQuasiProductGraphStripMeasureV1

noncomputable section

/-!
# The explicit one-dimensional Frostman normalization in PYZ (5.37)

For a `(delta, alpha; C)_1` set, an interval of length `L` has mass at most
`C * delta^(1-alpha) * L^alpha`.  Substituting this literal bound into the
Tonelli graph-strip theorem produces the quasi-product product bound.  No
two-dimensional mass inequality is a source field.
-/

/-- The literal `(delta, alpha; C)_1` interval mass bound, expressed in
`ENNReal` so no finiteness conversion is hidden. -/
def pyzFrostmanIntervalBound
    (delta alpha : Real) (C : ENNReal) (a b : Real) : ENNReal :=
  C * (ENNReal.ofReal delta) ^ (1 - alpha) *
    (ENNReal.ofReal (b - a)) ^ alpha

/-- The faithful quasi-product source predicate with the standard PYZ
one-dimensional Frostman normalization. -/
abbrev IsPyzFrostmanQuasiProduct
    (E : Set (Real × Real)) (delta alpha : Real) (C : ENNReal) :=
  PyzQuasiProduct E (pyzFrostmanIntervalBound delta alpha C)

/-- The exact quasi-product upper bound for a graph strip.  The two factors
are respectively the inner and outer one-dimensional Frostman estimates. -/
theorem volume_inter_pyzGraphStrip_le_frostmanProduct
    {E : Set (Real × Real)}
    {delta alpha : Real} {C : ENNReal}
    (Q : IsPyzFrostmanQuasiProduct E delta alpha C)
    {a b width : Real} {g : Real -> Real}
    (hg : Measurable g) :
    volume (E ∩ pyzGraphStrip a b g width) <=
      (C * (ENNReal.ofReal delta) ^ (1 - alpha) *
          (ENNReal.ofReal (2 * width)) ^ alpha) *
        (C * (ENNReal.ofReal delta) ^ (1 - alpha) *
          (ENNReal.ofReal (b - a)) ^ alpha) := by
  have hvertical : forall theta, theta ∈ Q.outer ∩ Icc a b ->
      pyzFrostmanIntervalBound delta alpha C
          (g theta - width) (g theta + width) <=
        C * (ENNReal.ofReal delta) ^ (1 - alpha) *
          (ENNReal.ofReal (2 * width)) ^ alpha := by
    intro theta _htheta
    simp only [pyzFrostmanIntervalBound]
    have hlength : (g theta + width) - (g theta - width) =
        2 * width := by ring
    rw [hlength]
  simpa [pyzFrostmanIntervalBound] using
    (volume_inter_pyzGraphStrip_le Q hg
      (C * (ENNReal.ofReal delta) ^ (1 - alpha) *
        (ENNReal.ofReal (2 * width)) ^ alpha) hvertical)

#print axioms pyzFrostmanIntervalBound
#print axioms IsPyzFrostmanQuasiProduct
#print axioms volume_inter_pyzGraphStrip_le_frostmanProduct

end

end FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
