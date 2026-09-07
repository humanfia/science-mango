import Family8Grounding.Family8PaperFullCanonicalGroundingV64
import Family8Grounding.Family8CertifiedPlankPairOverlapV2
import Family8Grounding.Family8CertifiedPlankDyadicCordobaV2

/-!
# Full canonical paper-strength Family 8 grounding bundle, V65

This checkpoint replaces the earlier slab-only analytic surrogate by a
genuine certified-plank Córdoba core.  An `IsPlank C a b` witness is unpacked
into its actual frame box.  The normalized cross product of the two short
normals controls the remaining longitudinal projection by
`b / 2 + 1 / 2 <= 1`, giving the real pair-overlap bound

`volume (K0 ∩ K1) <= ofReal (sin(angle)⁻¹) * 2 * a0 * a1`.

Combining this with the certified lower volume `C⁻³ * a * b` leaves the
required dimensionless `a / b` factor in every genuine dyadic angle scale.
Finite row summation then derives, rather than assumes, the row bound,
second moment, shaded-union estimate, and actual average-multiplicity bound.

The finite angle assignment, its containing bodies, Katz--Tao input, and the
paper-scale container inequality are still explicit geometric premises of
this analytic core.  Instantiating those premises twice on the actual outer
and inner selected-parent data is the remaining Lemma 6.4 portion of
Proposition 6.6(A).  The successor factorization/Lemma 5.11 chain, the
Section 8 one-step improvement, and `mainLemmaOne` also remain open.
-/
