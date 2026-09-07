import Family8Grounding.Family8PaperFullCanonicalGroundingV575
import Family8Grounding.Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1
import Family8Grounding.Family8PlankFixedThetaAllSlabFamily7UnionProducerV1

/-!
# Full canonical grounding interface checkpoint V576

The fixed-theta row catalogue now has a literal affine normalization datum
and an exact Frostman-restriction producer.  Restriction to an occupied row,
affine transport, and replacement by the chosen normalized ambient produce
the explicit Equation (43) row constant, including a separately recorded
upstream restriction loss when needed.

Given an independently proved fixed-geometry Family 7 bound, an actual row
shading-mass floor is converted to the literal normalized row-union lower
bound and then to the V2 aggregate certificate.  The interface permits
row-dependent coefficients and retains only their aggregate mass floor.

This checkpoint deliberately does **not** claim to prove Family 7.  The
`..._of_boundAt` declarations consume
`ConvexPlankFrostmanBoundAtFixedGeometry`; the selected outer Equation (45)
also consumes that analytic statement.  A separate non-circular theorem
establishing the fixed-geometry bound is still required, together with the
construction of the row-normalization/admissibility geometry, the large-
width Lemma 6.9 branch, and the final parameter ledger.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV576

#print axioms
  Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1.FixedThetaAllSlabRowNormalizationGeometry.rowFamily_isFrostmanIn_exactRestriction
#print axioms
  Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1.FixedThetaAllSlabRowNormalizationGeometry.normalizedRows_isFrostmanIn_withRestrictionLoss
#print axioms
  Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1.FixedThetaAllSlabRowNormalizationGeometry.eq43_rowCF_le_withRestrictionLoss
#print axioms
  Family8PlankFixedThetaAllSlabFamily7UnionProducerV1.FixedThetaAllSlabFamily7Admissibility.toRowLowerCertificate
#print axioms
  Family8PlankFixedThetaAllSlabFamily7UnionProducerV1.FixedThetaAllSlabFamily7RowLowerCertificate.toRawAggregateEq43Certificate
#print axioms
  Family8PlankFixedThetaAllSlabFamily7UnionProducerV1.exists_rawAggregateEq43Certificate_of_boundAt

end Family8PaperFullCanonicalGroundingV576
