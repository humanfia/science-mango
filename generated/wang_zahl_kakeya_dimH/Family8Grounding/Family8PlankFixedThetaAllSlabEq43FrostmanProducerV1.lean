import Family8Grounding.Family8PlankFixedThetaAllSlabAssemblyV1
import Family8Grounding.Family8IsFrostmanInActiveSubtypeRetentionV2
import Family8Grounding.Family8FrostmanAmbientReplacementV2
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Mathlib.Tactic

/-!
# Fixed-theta all-slab Eq. (43) Frostman producer

This file grounds the Frostman part of the row-dependent Eq. (43) input.
Starting with one Frostman certificate on the full thick-owner family, a
literal row pays the exact restriction loss

`global family mass / row family mass`.

The row is then sent through its chosen affine normalization.  Frostman
nonconcentration itself is affine invariant; replacing the affine image of
the source ambient by the unit-scale ambient used by the normalized plank
datum costs exactly the inverse-Jacobian row weight.

The geometric information needed for all of this is kept in one package.
Its associated normalized plank datum uses the affine-image family and
shading definitionally, so no body or shading transport is hidden behind a
conclusion-valued callback.  The only remaining analytic premise is the
source `IsFrostmanIn` certificate; the only nondegeneracy premise is that
each occupied row has nonzero family mass.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8FrostmanAmbientReplacementV2
open Family8IsFrostmanInActiveSubtypeRetentionV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankFixedThetaAllSlabAssemblyV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedParentAffineShadingTransportV4

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The chosen normalized geometry for every occupied row.

The actual normalized family and shading are not fields: they are defined
below to be the literal affine images of `R.rowFamily r` and
`R.rowShading r`.  The fields here are exactly the extra geometric facts
needed to regard those images as Family 6 plank data in a chosen unit-scale
ambient, together with the ambient-volume comparison that produces the
inverse-Jacobian Eq. (43) loss. -/
structure FixedThetaAllSlabRowNormalizationGeometry
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space) where
  sourceAmbient : ConvexBody Space
  shortWidth : rowIndex -> NNReal
  longWidth : rowIndex -> NNReal
  comparisonConstant : rowIndex -> NNReal
  affineRow_isPlank : forall r s,
    IsPlank (comparisonConstant r) (shortWidth r) (longWidth r)
      (affineImageFamily (normalize r) (R.rowFamily r) s)
  normalizedAmbient : rowIndex -> ConvexBody Space
  ambientComparisonConstant : rowIndex -> NNReal
  normalizedAmbient_is_unit_scale : forall r,
    IsPlank (ambientComparisonConstant r) 1 1 (normalizedAmbient r)
  affineRow_contained_in_normalizedAmbient : forall r s,
    (affineImageFamily (normalize r) (R.rowFamily r) s : Set Space) ⊆
      (normalizedAmbient r : Set Space)
  normalizedAmbient_volume_le : forall r,
    volume (normalizedAmbient r : Set Space) ≤
      inverseAffineJacobianRowWeight normalize r *
        volume
          (affineImageConvexBody (normalize r) sourceAmbient : Set Space)

/-- The normalized Family 6 datum canonically associated to the chosen row
geometry.  Its family and shading are literal affine images. -/
def FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    ShadedConvexPlankFamily {s // s ∈ R.rowOwners r}
      (P.shortWidth r) (P.longWidth r) where
  family := affineImageFamily (normalize r) (R.rowFamily r)
  shading := affineImageShading (normalize r) (R.rowShading r)
  comparisonConstant := P.comparisonConstant r
  all_isPlank := P.affineRow_isPlank r
  ambient := P.normalizedAmbient r
  ambientComparisonConstant := P.ambientComparisonConstant r
  ambient_is_unit_scale := P.normalizedAmbient_is_unit_scale r
  contained_in_ambient := P.affineRow_contained_in_normalizedAmbient r

@[simp] theorem FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_family
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    (P.normalizedRowDatum r).family =
      affineImageFamily (normalize r) (R.rowFamily r) := rfl

@[simp] theorem FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_shading
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    (P.normalizedRowDatum r).shading =
      affineImageShading (normalize r) (R.rowShading r) := rfl

/-- The normalized datum's shaded union is the literal affine image of the
physical row union. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_shadedUnion
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    (P.normalizedRowDatum r).shading.shadedUnion =
      normalize r '' (R.rowShading r).shadedUnion := by
  exact affineImageShading_shadedUnion (normalize r) (R.rowShading r)

/-- The normalized datum's union volume is exactly the scalar used by the
all-slab assembly. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_shadedUnion_volume
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    volume (P.normalizedRowDatum r).shading.shadedUnion =
      affineNormalizedRowUnion R normalize r := by
  rw [P.normalizedRowDatum_shadedUnion]
  rfl

/-- The normalized datum's family volume is its physical row mass times the
affine Jacobian. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_familyVolume
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    familyVolume (P.normalizedRowDatum r).family =
      affineJacobian (normalize r) * familyVolume (R.rowFamily r) := by
  exact affineImageFamily_familyVolume (normalize r) (R.rowFamily r)

/-- The exact row-dependent constant produced by restriction, affine
transport, and replacement of the normalized ambient. -/
def FixedThetaAllSlabRowNormalizationGeometry.rowFrostmanEnvelope
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (_P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (sourceCF : ENNReal) (r : rowIndex) : ENNReal :=
  sourceCF * inverseAffineJacobianRowWeight normalize r *
    (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
      familyVolume (R.rowFamily r))

/-- A possibly lossy restriction certificate shared by all rows.

The row-dependent quotient remains the exact physical mass quotient; the
single scalar `restrictionLoss` records only an earlier loss incurred before
the literal row restriction.  Stating the field at the contained-mass level
makes this interface usable even when that earlier selection is not an exact
subtype of the source certificate. -/
structure FixedThetaAllSlabRowRestrictionLossCertificate
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (restrictionLoss : ENNReal) where
  ambientMass_retention : forall r,
    containedMass (heavyRetainedOwnerThickenedFamily D C q)
        P.sourceAmbient ≤
      (restrictionLoss *
          (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
            familyVolume (R.rowFamily r))) *
        containedMass (R.rowFamily r) P.sourceAmbient

/-- The Eq. (43) Frostman envelope with an explicit fixed restriction loss. -/
def FixedThetaAllSlabRowNormalizationGeometry.rowFrostmanEnvelopeWithRestrictionLoss
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (_P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (restrictionLoss sourceCF : ENNReal) (r : rowIndex) : ENNReal :=
  restrictionLoss * sourceCF *
    inverseAffineJacobianRowWeight normalize r *
      (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
        familyVolume (R.rowFamily r))

/-- Restrict the global thick-owner Frostman certificate to one literal row,
paying exactly `globalMass / rowMass`.

Both contained masses reduce to family volumes using the containment already
present in `hsource`; hence no separate retention inequality is assumed. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.rowFamily_isFrostmanIn_exactRestriction
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
    (r : rowIndex) (hrowMass0 : familyVolume (R.rowFamily r) ≠ 0) :
    IsFrostmanIn
      (sourceCF *
        (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
          familyVolume (R.rowFamily r)))
      (R.rowFamily r) P.sourceAmbient := by
  have hrowContained : forall s,
      (R.rowFamily r s : Set Space) ⊆ (P.sourceAmbient : Set Space) := by
    intro s
    exact hsource.1 s.1
  have hretained :
      containedMass (heavyRetainedOwnerThickenedFamily D C q)
          P.sourceAmbient ≤
        (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
            familyVolume (R.rowFamily r)) *
          containedMass (activeSubtypeFamily
            (heavyRetainedOwnerThickenedFamily D C q)
            (R.rowOwners r)) P.sourceAmbient := by
    rw [containedMass_eq_familyVolume_of_contained
      (heavyRetainedOwnerThickenedFamily D C q) P.sourceAmbient hsource.1]
    change familyVolume (heavyRetainedOwnerThickenedFamily D C q) ≤
      (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
          familyVolume (R.rowFamily r)) *
        containedMass (R.rowFamily r) P.sourceAmbient
    rw [containedMass_eq_familyVolume_of_contained
      (R.rowFamily r) P.sourceAmbient hrowContained]
    rw [ENNReal.div_mul_cancel hrowMass0
      (familyVolume_ne_top (R.rowFamily r))]
  have hrestricted :=
    isFrostmanIn_activeSubtype_of_ambientMass_retention
      (R.rowOwners r) hsource hretained
  change IsFrostmanIn
    (sourceCF *
      (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
        familyVolume (R.rowFamily r)))
    (R.rowFamily r) P.sourceAmbient at hrestricted
  exact hrestricted

/-- Literal subtype restriction supplies the restriction-loss package with
loss one.  Thus the generic lossy interface below adds no premise in the
actual all-row catalogue. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.exactRestrictionLossOneCertificate
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
    (hrowMass0 : forall r, familyVolume (R.rowFamily r) ≠ 0) :
    FixedThetaAllSlabRowRestrictionLossCertificate P 1 where
  ambientMass_retention r := by
    have hrowContained : forall s,
        (R.rowFamily r s : Set Space) ⊆ (P.sourceAmbient : Set Space) := by
      intro s
      exact hsource.1 s.1
    rw [containedMass_eq_familyVolume_of_contained
      (heavyRetainedOwnerThickenedFamily D C q) P.sourceAmbient hsource.1]
    rw [containedMass_eq_familyVolume_of_contained
      (R.rowFamily r) P.sourceAmbient hrowContained]
    simp only [one_mul]
    rw [ENNReal.div_mul_cancel (hrowMass0 r)
      (familyVolume_ne_top (R.rowFamily r))]

/-- A supplied fixed-loss retention certificate gives the corresponding
Frostman certificate on every normalized row.  This is the generic adapter
for an upstream source selection that already lost `restrictionLoss`; no
positivity or lower bound on that scalar is imposed here. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.normalizedRows_isFrostmanIn_withRestrictionLoss
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
      P restrictionLoss) :
    forall r,
      IsFrostmanIn
        (P.rowFrostmanEnvelopeWithRestrictionLoss
          restrictionLoss sourceCF r)
        (P.normalizedRowDatum r).family
        (P.normalizedRowDatum r).ambient := by
  intro r
  have hretained :
      containedMass (heavyRetainedOwnerThickenedFamily D C q)
          P.sourceAmbient ≤
        (restrictionLoss *
            (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
              familyVolume (R.rowFamily r))) *
          containedMass (activeSubtypeFamily
            (heavyRetainedOwnerThickenedFamily D C q)
            (R.rowOwners r)) P.sourceAmbient := by
    change containedMass (heavyRetainedOwnerThickenedFamily D C q)
        P.sourceAmbient ≤
      (restrictionLoss *
          (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
            familyVolume (R.rowFamily r))) *
        containedMass (R.rowFamily r) P.sourceAmbient
    exact Hretention.ambientMass_retention r
  have hrestrictedRaw :=
    isFrostmanIn_activeSubtype_of_ambientMass_retention
      (R.rowOwners r) hsource hretained
  change IsFrostmanIn
    (sourceCF *
      (restrictionLoss *
        (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
          familyVolume (R.rowFamily r))))
    (R.rowFamily r) P.sourceAmbient at hrestrictedRaw
  have hrestricted :
      IsFrostmanIn
        (restrictionLoss * sourceCF *
          (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
            familyVolume (R.rowFamily r)))
        (R.rowFamily r) P.sourceAmbient := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hrestrictedRaw
  have haffine := IsFrostmanIn.affineImage (normalize r) hrestricted
  have hnormalized := isFrostmanIn_replace_ambient haffine
    (P.affineRow_contained_in_normalizedAmbient r)
    (P.normalizedAmbient_volume_le r)
  change IsFrostmanIn
    (P.rowFrostmanEnvelopeWithRestrictionLoss restrictionLoss sourceCF r)
    (affineImageFamily (normalize r) (R.rowFamily r))
    (P.normalizedAmbient r)
  simpa only [
    FixedThetaAllSlabRowNormalizationGeometry.rowFrostmanEnvelopeWithRestrictionLoss,
    mul_assoc, mul_left_comm, mul_comm] using hnormalized

/-- All chosen normalized rows inherit a Frostman certificate at the exact
Eq. (43) envelope.  Affine transport has no cost; the sole geometric cost is
the inverse-Jacobian ambient-volume comparison stored in `P`. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.normalizedRows_isFrostmanIn_envelope
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
    (hrowMass0 : forall r, familyVolume (R.rowFamily r) ≠ 0) :
    forall r, IsFrostmanIn (P.rowFrostmanEnvelope sourceCF r)
      (P.normalizedRowDatum r).family
      (P.normalizedRowDatum r).ambient := by
  intro r
  have hrestricted := P.rowFamily_isFrostmanIn_exactRestriction
    hsource r (hrowMass0 r)
  have haffine := IsFrostmanIn.affineImage (normalize r) hrestricted
  have hnormalized := isFrostmanIn_replace_ambient haffine
    (P.affineRow_contained_in_normalizedAmbient r)
    (P.normalizedAmbient_volume_le r)
  change IsFrostmanIn (P.rowFrostmanEnvelope sourceCF r)
    (affineImageFamily (normalize r) (R.rowFamily r))
    (P.normalizedAmbient r)
  simpa only [FixedThetaAllSlabRowNormalizationGeometry.rowFrostmanEnvelope,
    mul_assoc, mul_left_comm, mul_comm] using hnormalized

/-- The definitionally chosen row constant satisfies the raw Eq. (43)
upper-bound field with equality. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.eq43_rowCF_le
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (sourceCF : ENNReal) : forall r,
    P.rowFrostmanEnvelope sourceCF r ≤
      sourceCF * inverseAffineJacobianRowWeight normalize r *
        (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
          familyVolume (R.rowFamily r)) := by
  intro r
  exact le_rfl

/-- The fixed-loss envelope satisfies the corresponding V2 raw Eq. (43)
field with equality. -/
theorem FixedThetaAllSlabRowNormalizationGeometry.eq43_rowCF_le_withRestrictionLoss
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex -> Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (restrictionLoss sourceCF : ENNReal) : forall r,
    P.rowFrostmanEnvelopeWithRestrictionLoss restrictionLoss sourceCF r ≤
      restrictionLoss * sourceCF *
        inverseAffineJacobianRowWeight normalize r *
          (familyVolume (heavyRetainedOwnerThickenedFamily D C q) /
            familyVolume (R.rowFamily r)) := by
  intro r
  exact le_rfl

#print axioms FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_shadedUnion
#print axioms FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_shadedUnion_volume
#print axioms FixedThetaAllSlabRowNormalizationGeometry.normalizedRowDatum_familyVolume
#print axioms FixedThetaAllSlabRowNormalizationGeometry.rowFamily_isFrostmanIn_exactRestriction
#print axioms FixedThetaAllSlabRowNormalizationGeometry.exactRestrictionLossOneCertificate
#print axioms FixedThetaAllSlabRowNormalizationGeometry.normalizedRows_isFrostmanIn_withRestrictionLoss
#print axioms FixedThetaAllSlabRowNormalizationGeometry.normalizedRows_isFrostmanIn_envelope
#print axioms FixedThetaAllSlabRowNormalizationGeometry.eq43_rowCF_le
#print axioms FixedThetaAllSlabRowNormalizationGeometry.eq43_rowCF_le_withRestrictionLoss

end
end Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1
