import Family6Grounding.Family6AffinePlankFrostmanBoundAtFixedGeometryV1
import Family8Grounding.Family8AverageMultiplicityToUnionLowerV1
import Family8Grounding.Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2
import Family8Grounding.Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1
import Mathlib.Tactic

/-!
# Family 7 union lower bounds for all fixed-theta slab rows

This file supplies the Family 7 half of the row-dependent all-slab input.
The normalized row datum is the literal affine-image datum constructed in
`Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1`; no second proxy family
or shading is introduced here.

A chosen fixed-geometry Family 7 bound gives an average-multiplicity upper
bound on every normalized row.  The generic division-free converse from
`Family8AverageMultiplicityToUnionLowerV1` then converts an actual shading
mass floor into a lower bound for the literal normalized shaded union.

Accordingly, this module is only a
`ConvexPlankFrostmanBoundAtFixedGeometry -> row union/raw certificate`
adapter.  It neither proves nor produces that analytic Family 7 bound.  The
Family 7 dependency can be closed only by a separate, non-circular theorem
establishing `ConvexPlankFrostmanBoundAtFixedGeometry`.

The only scalar relation not supplied by those two ingredients is recorded
once in `FixedThetaAllSlabFamily7Admissibility`: the comparison between the
desired row coefficient and `massFloor / convexPlankFrostmanFactor`.  This is
the precise scale/count/mass ledger still required at the fixed geometry;
it is not replaced by endpoint assumptions on the multiplicity cap.

Row coefficients are allowed to vary.  Their sole aggregate hypothesis is
`aggregateBase * globalMass <= sum rowBase(r) * rowMass(r)`, which is the
form consumed by the aggregate Eq. (43) cancellation and does not impose a
common good-row lower bound.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankFixedThetaAllSlabFamily7UnionProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6AffinePlankFrostmanBoundAtFixedGeometryV1
open Family8AverageMultiplicityToUnionLowerV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankFixedThetaAllSlabAssemblyV1
open Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2
open Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The literal Family 7 lower-bound expression for one normalized row.

The row base is deliberately row-dependent.  The volume appearing here is
the physical row mass divided by the inverse-Jacobian reconstruction weight,
exactly as in the raw aggregate Eq. (43) certificate. -/
def family7RowUnionTarget
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (rowCF rowBase : rowIndex -> ENNReal) (beta : Real)
    (r : rowIndex) : ENNReal :=
  rowBase r * rowCF r ^ (-(1 - beta / 2)) *
    (familyVolume (R.rowFamily r) /
      inverseAffineJacobianRowWeight normalize r) ^ (beta / 2)

/-- The row-varying output needed by the aggregate Eq. (43) producer.

Besides the exact Family 7 lower bound, it retains only the one aggregate
mass inequality that permits the varying row bases to be summed. -/
structure FixedThetaAllSlabFamily7RowLowerCertificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (rowCF : rowIndex -> ENNReal) (beta : Real) where
  rowBase : rowIndex -> ENNReal
  aggregateBase : ENNReal
  aggregateBase_mass_lower :
    aggregateBase *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) <=
      ∑ r : rowIndex, rowBase r * familyVolume (R.rowFamily r)
  family7_row_union_lower : forall r,
    family7RowUnionTarget R normalize rowCF rowBase beta r <=
      affineNormalizedRowUnion R normalize r

/-- All geometric and mass-floor data needed to apply one chosen Family 7
tail simultaneously to the normalized rows.

The fields are bundled at the parameters `eta` and `b0` selected by the
fixed-geometry hypothesis.  In particular, callers do not supply a list of
detached endpoint assumptions.  `target_le_massFloor_div_factor` is the one
honest residual scalar ledger: the analytic theorem controls average
multiplicity, whereas this comparison records how the actual normalized
shading mass pays the desired row coefficient. -/
structure FixedThetaAllSlabFamily7Admissibility
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (rowCF : rowIndex -> ENNReal)
    (epsilon beta eta : Real) (b0 : NNReal)
    (memberComparisonCap ambientComparisonCap : NNReal) where
  rowBase : rowIndex -> ENNReal
  aggregateBase : ENNReal
  massFloor : rowIndex -> ENNReal
  thickeningConstant : rowIndex -> NNReal
  aggregateBase_mass_lower :
    aggregateBase *
        familyVolume (heavyRetainedOwnerThickenedFamily D C q) <=
      ∑ r : rowIndex, rowBase r * familyVolume (R.rowFamily r)
  memberComparison_le : forall r,
    (P.normalizedRowDatum r).comparisonConstant <= memberComparisonCap
  ambientComparison_le : forall r,
    (P.normalizedRowDatum r).ambientComparisonConstant <=
      ambientComparisonCap
  shortWidth_pos : forall r, 0 < P.shortWidth r
  shortWidth_le_longWidth : forall r, P.shortWidth r <= P.longWidth r
  longWidth_le_b0 : forall r, P.longWidth r <= b0
  density_lower : forall r,
    (P.shortWidth r : ENNReal) ^ eta <=
      (P.normalizedRowDatum r).shading.shadingDensity
  thickenedPlankControl : forall r,
    FrostmanThickenedPlankControl
      (P.normalizedRowDatum r) (thickeningConstant r)
  massFloor_le_shadingMass : forall r,
    massFloor r <= (P.normalizedRowDatum r).shading.shadingMass
  target_le_massFloor_div_factor : forall r,
    family7RowUnionTarget R normalize rowCF rowBase beta r <=
      massFloor r /
        convexPlankFrostmanFactor (P.normalizedRowDatum r)
          epsilon beta (rowCF r) (thickeningConstant r)

/-- An average-multiplicity upper bound for each actual normalized shading,
together with the bundled mass floor, gives the exact raw Family 7 row-union
lower bounds.  The quotient adapter is valid even if its cap is `0` or
`infinity`, so no nonzero/non-top cap premise occurs. -/
def FixedThetaAllSlabFamily7Admissibility.toRowLowerCertificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    {P : FixedThetaAllSlabRowNormalizationGeometry R normalize}
    {rowCF : rowIndex -> ENNReal}
    {epsilon beta eta : Real} {b0 : NNReal}
    {memberComparisonCap ambientComparisonCap : NNReal}
    (A : FixedThetaAllSlabFamily7Admissibility P rowCF
      epsilon beta eta b0 memberComparisonCap ambientComparisonCap)
    (haverage : forall r,
      (P.normalizedRowDatum r).shading.averageMultiplicity <=
        convexPlankFrostmanFactor (P.normalizedRowDatum r)
          epsilon beta (rowCF r) (A.thickeningConstant r)) :
    FixedThetaAllSlabFamily7RowLowerCertificate
      R normalize rowCF beta where
  rowBase := A.rowBase
  aggregateBase := A.aggregateBase
  aggregateBase_mass_lower := A.aggregateBase_mass_lower
  family7_row_union_lower := by
    intro r
    calc
      family7RowUnionTarget R normalize rowCF A.rowBase beta r <=
          A.massFloor r /
            convexPlankFrostmanFactor (P.normalizedRowDatum r)
              epsilon beta (rowCF r) (A.thickeningConstant r) :=
        A.target_le_massFloor_div_factor r
      _ <= volume (P.normalizedRowDatum r).shading.shadedUnion :=
        massFloor_div_cap_le_volume_shadedUnion_of_averageMultiplicity_le
          (P.normalizedRowDatum r).shading
          (A.massFloor r)
          (convexPlankFrostmanFactor (P.normalizedRowDatum r)
            epsilon beta (rowCF r) (A.thickeningConstant r))
          (A.massFloor_le_shadingMass r) (haverage r)
      _ = affineNormalizedRowUnion R normalize r :=
        P.normalizedRowDatum_shadedUnion_volume r

/-- Compose the concrete Eq. (43) envelope with the Family 7 row-lower
output.  All conclusion-valued fields of the aggregate raw certificate are
therefore produced: Eq. (43) holds by definition, and the Family 7 field is
the literal normalized-shading conclusion proved above. -/
def FixedThetaAllSlabFamily7RowLowerCertificate.toRawAggregateEq43Certificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    {restrictionLoss sourceCF : ENNReal} {beta : Real}
    (F7 : FixedThetaAllSlabFamily7RowLowerCertificate R normalize
      (P.rowFrostmanEnvelopeWithRestrictionLoss restrictionLoss sourceCF)
      beta)
    (hrestrictionTop : restrictionLoss ≠ ⊤)
    (hsourceTop : sourceCF ≠ ⊤)
    (hglobalMass0 :
      familyVolume (heavyRetainedOwnerThickenedFamily D C q) ≠ 0)
    (hrowMass0 : forall r, familyVolume (R.rowFamily r) ≠ 0)
    (hbeta0 : 0 <= beta) (hbeta2 : beta <= 2) :
    FixedThetaAllSlabRawAggregateEq43Certificate R normalize
      restrictionLoss sourceCF beta where
  rowCF := P.rowFrostmanEnvelopeWithRestrictionLoss restrictionLoss sourceCF
  rowBase := F7.rowBase
  aggregateBase := F7.aggregateBase
  restrictionLoss_ne_top := hrestrictionTop
  sourceCF_ne_top := hsourceTop
  globalMass_ne_zero := hglobalMass0
  rowMass_ne_zero := hrowMass0
  beta_nonnegative := hbeta0
  beta_le_two := hbeta2
  aggregate_base_mass_floor := F7.aggregateBase_mass_lower
  eq43_rowCF_le :=
    P.eq43_rowCF_le_withRestrictionLoss restrictionLoss sourceCF
  family7_row_union_lower := by
    intro r
    simpa only [family7RowUnionTarget] using F7.family7_row_union_lower r

/-- Apply one chosen fixed-geometry Family 7 hypothesis to all literal
normalized rows.

The hypothesis first chooses common analytic parameters `eta` and `b0`.
Any single bundled admissibility certificate at those parameters then gives
the row-varying Family 7 lower certificate.  The row Frostman constants are
the concrete Eq. (43) envelopes already produced by restriction, affine
transport, and ambient replacement.

This is strictly an `_of_boundAt` adapter: `H` is the unresolved analytic
Family 7 input, not a result of this theorem.  Nothing in the row-lower
certificate can be used here to manufacture `H` without circularity. -/
theorem exists_family7RowLowerCertificate_withRestrictionLoss_of_boundAt
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    {restrictionLoss sourceCF : ENNReal}
    (hsource : IsFrostmanIn sourceCF
      (heavyRetainedOwnerThickenedFamily D C q) P.sourceAmbient)
    (Hretention : FixedThetaAllSlabRowRestrictionLossCertificate
      P restrictionLoss)
    (epsilon beta : Real)
    (memberComparisonCap ambientComparisonCap : NNReal)
    (H : ConvexPlankFrostmanBoundAtFixedGeometry
      iota beta epsilon memberComparisonCap ambientComparisonCap) :
    exists eta : Real, exists b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      forall _A : FixedThetaAllSlabFamily7Admissibility P
        (P.rowFrostmanEnvelopeWithRestrictionLoss
          restrictionLoss sourceCF)
        epsilon beta eta b0 memberComparisonCap ambientComparisonCap,
        Nonempty (FixedThetaAllSlabFamily7RowLowerCertificate R normalize
          (P.rowFrostmanEnvelopeWithRestrictionLoss
            restrictionLoss sourceCF) beta) := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ := H.bound
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro A
  refine ⟨A.toRowLowerCertificate ?_⟩
  intro r
  exact hbound {s // s ∈ R.rowOwners r}
    (P.shortWidth r) (P.longWidth r) (P.normalizedRowDatum r)
    (P.rowFrostmanEnvelopeWithRestrictionLoss restrictionLoss sourceCF r)
    (A.thickeningConstant r)
    (A.memberComparison_le r) (A.ambientComparison_le r)
    (A.shortWidth_pos r) (A.shortWidth_le_longWidth r)
    (A.longWidth_le_b0 r)
    (P.normalizedRows_isFrostmanIn_withRestrictionLoss
      hsource Hretention r)
    (A.density_lower r) (A.thickenedPlankControl r)

/-- Concrete chosen-geometry producer for the full raw aggregate Eq. (43)
certificate.  The fixed-geometry Family 7 statement is applied here; the
remaining input is one bundled normalized-row admissibility certificate at
its chosen `eta` and `b0`.

The word `producer` refers only to the raw aggregate certificate.  This
theorem consumes, and does not prove, `ConvexPlankFrostmanBoundAtFixedGeometry`;
a separate non-circular analytic Family 7 theorem is still required. -/
theorem exists_rawAggregateEq43Certificate_of_boundAt
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    {restrictionLoss sourceCF : ENNReal}
    (hsource : IsFrostmanIn sourceCF
      (heavyRetainedOwnerThickenedFamily D C q) P.sourceAmbient)
    (Hretention : FixedThetaAllSlabRowRestrictionLossCertificate
      P restrictionLoss)
    (hrestrictionTop : restrictionLoss ≠ ⊤)
    (hsourceTop : sourceCF ≠ ⊤)
    (hglobalMass0 :
      familyVolume (heavyRetainedOwnerThickenedFamily D C q) ≠ 0)
    (hrowMass0 : forall r, familyVolume (R.rowFamily r) ≠ 0)
    (epsilon beta : Real) (hbeta0 : 0 <= beta) (hbeta2 : beta <= 2)
    (memberComparisonCap ambientComparisonCap : NNReal)
    (H : ConvexPlankFrostmanBoundAtFixedGeometry
      iota beta epsilon memberComparisonCap ambientComparisonCap) :
    exists eta : Real, exists b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      forall _A : FixedThetaAllSlabFamily7Admissibility P
        (P.rowFrostmanEnvelopeWithRestrictionLoss
          restrictionLoss sourceCF)
        epsilon beta eta b0 memberComparisonCap ambientComparisonCap,
        Nonempty (FixedThetaAllSlabRawAggregateEq43Certificate R normalize
          restrictionLoss sourceCF beta) := by
  obtain ⟨eta, b0, heta, hb0, hrows⟩ :=
    exists_family7RowLowerCertificate_withRestrictionLoss_of_boundAt
      P hsource Hretention epsilon beta memberComparisonCap
        ambientComparisonCap H
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro A
  obtain ⟨F7⟩ := hrows A
  exact ⟨F7.toRawAggregateEq43Certificate P
    hrestrictionTop hsourceTop hglobalMass0 hrowMass0 hbeta0 hbeta2⟩

/-- Loss-one specialization for the literal row partition.  Like the
generic-loss theorem, this remains an adapter *from* an independently proved
`ConvexPlankFrostmanBoundAtFixedGeometry`, not a proof of that bound. -/
theorem exists_family7RowLowerCertificate_of_boundAt
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    {sourceCF : ENNReal}
    (hsource : IsFrostmanIn sourceCF
      (heavyRetainedOwnerThickenedFamily D C q) P.sourceAmbient)
    (hrowMass0 : forall r, familyVolume (R.rowFamily r) ≠ 0)
    (epsilon beta : Real)
    (memberComparisonCap ambientComparisonCap : NNReal)
    (H : ConvexPlankFrostmanBoundAtFixedGeometry
      iota beta epsilon memberComparisonCap ambientComparisonCap) :
    exists eta : Real, exists b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      forall _A : FixedThetaAllSlabFamily7Admissibility P
        (P.rowFrostmanEnvelope sourceCF) epsilon beta eta b0
          memberComparisonCap ambientComparisonCap,
        Nonempty (FixedThetaAllSlabFamily7RowLowerCertificate R normalize
          (P.rowFrostmanEnvelope sourceCF) beta) := by
  obtain ⟨eta, b0, heta, hb0, hbound⟩ := H.bound
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro A
  refine ⟨A.toRowLowerCertificate ?_⟩
  intro r
  exact hbound {s // s ∈ R.rowOwners r}
    (P.shortWidth r) (P.longWidth r) (P.normalizedRowDatum r)
    (P.rowFrostmanEnvelope sourceCF r) (A.thickeningConstant r)
    (A.memberComparison_le r) (A.ambientComparison_le r)
    (A.shortWidth_pos r) (A.shortWidth_le_longWidth r)
    (A.longWidth_le_b0 r)
    (P.normalizedRows_isFrostmanIn_envelope hsource hrowMass0 r)
    (A.density_lower r) (A.thickenedPlankControl r)

#print axioms
  FixedThetaAllSlabFamily7Admissibility.toRowLowerCertificate
#print axioms
  FixedThetaAllSlabFamily7RowLowerCertificate.toRawAggregateEq43Certificate
#print axioms
  exists_family7RowLowerCertificate_withRestrictionLoss_of_boundAt
#print axioms exists_rawAggregateEq43Certificate_of_boundAt
#print axioms exists_family7RowLowerCertificate_of_boundAt

end
end Family8PlankFixedThetaAllSlabFamily7UnionProducerV1
