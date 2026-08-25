import FamilyStickyGrounding.FamilyStickyScaleChainArbitraryRadiusBoundsV1
import FamilyStickyGrounding.FamilyStickyHierarchySuppliedPackingJointRandomMotionV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyEndpointPrefixBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1.SuppliedHierarchy
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1

noncomputable section

/-!
# Identifying finite-chain endpoints with supplied hierarchy prefixes

The coherent multiscale-cover API and the hierarchy selector retain all of
their indices, but they do not assert that an endpoint cover is one of the
hierarchy's effective families, or that such an effective family is the
selected prefix family produced by the random-motion construction.

This module records precisely that missing non-numerical identification.  A
body-preserving embedding is enough: Katz--Tao concentration is monotone when
occurrences are embedded into a larger indexed family.  Thus no artificial
cardinality equality is required.  Radius alignment is retained separately,
so a body equality cannot accidentally connect different scale nodes.

The resulting constructor fills `DiscreteAllLargeStickyBounds.katzTao_endpoint`
directly from the supplied pre-motion finite tests.  The Frostman endpoint is
left explicit: it is a relative fine-fibre normalization and does not follow
from an absolute Katz--Tao bound on the coarse prefix family.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  {G : HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  (Q : SuppliedHierarchy.Certificate H G P)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-! ## The three literal indexed families -/

/-- Active coarse occurrences in the chosen finite-chain endpoint. -/
abbrev EndpointIndex (m : Fin depth) :=
  {q // q ∈ (upperEndpointCover C S m).activeCoarse}

/-- The endpoint convex family whose concentration occurs in
`IsKatzTaoAtScale`. -/
abbrev endpointFamily (m : Fin depth) : ConvexFamily (EndpointIndex H C S m) :=
  (upperEndpointCover C S m).activeCoarseFamily

/-- Active occurrences in one effective hierarchy family. -/
abbrev EffectiveIndex (k : Fin depth) :=
  {i // i ∈ (H.effectiveFamily k.1).refinement.refined}

/-- The active convex family at an arbitrary effective hierarchy layer. -/
def effectiveFamily (k : Fin depth) : ConvexFamily (EffectiveIndex H k) :=
  fun i => (H.effectiveFamily k.1).bodyFamily i.1

/-- The selected local occurrence type at one supplied hierarchy layer. -/
abbrev PrefixIndex (k : Fin depth) (p : Index (k.1 + 1)) :=
  FixedPackingPotentialFamily.SelectedIndex
    (hierarchyFiberSeedData H k p)
    (repetitions G.toDependentSource k)

/-- The literal supplied-plan selected family after the common hierarchy
prefix translation. -/
def suppliedPrefixFamily
    (path : Q.Path) (k : Fin depth) (p : Index (k.1 + 1)) :
    ConvexFamily (PrefixIndex H (G := G) k p) :=
  FamilyStickyConvexBodyTranslationConcentrationV1.translateFamily
    (FixedPackingPotentialFamily.selectedFamily
      (hierarchyFiberSeedData H k p) (P.certificate k)
      (JointCertificateAdapter.plannedOmega
        Q.joint P Q.usesPlan k))
    (Q.joint.output.prefixVector path k)

/-! ## Minimal data-bearing identifications -/

/-- First seam: an endpoint scale is an effective hierarchy scale, and every
active endpoint occurrence embeds body-for-body into that hierarchy family. -/
structure EndpointEffectiveIdentification where
  layer : Fin depth -> Fin depth
  radius_eq : forall m, S.theta m = H.effectiveRadius (layer m).1
  indexEmbedding : forall m,
    EndpointIndex H C S m ↪ EffectiveIndex H (layer m)
  body_eq : forall m i,
    endpointFamily H C S m i =
      effectiveFamily H (layer m) (indexEmbedding m i)

/-- Second seam: the effective hierarchy occurrences used by an endpoint
embed body-for-body into one literal supplied-plan prefix family. -/
structure EffectivePrefixIdentification
    (E : EndpointEffectiveIdentification H C S) where
  path : forall _m : Fin depth, Q.Path
  parent : forall m, Index ((E.layer m).1 + 1)
  indexEmbedding : forall m,
    EffectiveIndex H (E.layer m) ↪
      PrefixIndex H (G := G) (E.layer m) (parent m)
  body_eq : forall m i,
    effectiveFamily H (E.layer m) i =
      suppliedPrefixFamily H Q (path m) (E.layer m) (parent m)
        (indexEmbedding m i)

/-- The full endpoint-to-prefix seam, factored through the literal effective
hierarchy family so both identifications remain inspectable. -/
structure Identification where
  endpointEffective : EndpointEffectiveIdentification H C S
  effectivePrefix :
    EffectivePrefixIdentification H Q C S endpointEffective

namespace Identification

variable {H Q C S}
  (I : Identification H Q C S)

/-- Composing the two retained embeddings gives the only index map needed by
the analytic endpoint. -/
def endpointPrefixEmbedding (m : Fin depth) :
    EndpointIndex H C S m ↪
      PrefixIndex H (G := G)
        (I.endpointEffective.layer m) (I.effectivePrefix.parent m) where
  toFun := fun i =>
    I.effectivePrefix.indexEmbedding m
      (I.endpointEffective.indexEmbedding m i)
  inj' := (I.effectivePrefix.indexEmbedding m).injective.comp
    (I.endpointEffective.indexEmbedding m).injective

@[simp]
theorem endpointPrefixEmbedding_apply (m : Fin depth)
    (i : EndpointIndex H C S m) :
    I.endpointPrefixEmbedding m i =
      I.effectivePrefix.indexEmbedding m
        (I.endpointEffective.indexEmbedding m i) :=
  rfl

/-- The composite embedding preserves the actual convex body, not merely its
carrier or its volume. -/
theorem endpointPrefix_body_eq (m : Fin depth)
    (i : EndpointIndex H C S m) :
    endpointFamily H C S m i =
      suppliedPrefixFamily H Q (I.effectivePrefix.path m)
        (I.endpointEffective.layer m) (I.effectivePrefix.parent m)
        (I.endpointPrefixEmbedding m i) := by
  rw [I.endpointEffective.body_eq m i,
    I.effectivePrefix.body_eq m
      (I.endpointEffective.indexEmbedding m i)]
  rfl

/-- Endpoint concentration is bounded by the concentration of the identified
supplied prefix.  Repetitions in the prefix are retained by the embedding. -/
theorem endpoint_concentration_le_prefix (m : Fin depth)
    (K : ConvexBody Space) :
    concentration (endpointFamily H C S m) K <=
      concentration
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m)) K := by
  exact concentration_le_of_embedding
    (endpointFamily H C S m)
    (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
      (I.endpointEffective.layer m) (I.effectivePrefix.parent m))
    (I.endpointPrefixEmbedding m) (I.endpointPrefix_body_eq m) K

/-- Any all-convex Katz--Tao estimate on the identified supplied prefixes
automatically supplies every finite-chain endpoint Katz--Tao field. -/
theorem katzTao_endpoint_of_prefix
    (A : ENNReal)
    (hprefix : forall m,
      IsKatzTao A
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m))) :
    forall m,
      (upperEndpointCover C S m).IsKatzTaoAtScale A := by
  intro m K
  exact (I.endpoint_concentration_le_prefix m K).trans
    ((isKatzTao_iff_concentration_le.mp (hprefix m)) K)

/-- The supplied-plan pre-motion finite catalogue is enough to produce all
endpoint Katz--Tao estimates once the geometric identification is present. -/
theorem katzTao_endpoint_of_preMotion_finite_tests
    (A : ENNReal)
    (hfinite : forall m q,
      IsKatzTaoAt A
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H (I.endpointEffective.layer m)
            (I.effectivePrefix.parent m))
          (P.certificate (I.endpointEffective.layer m))
          (JointCertificateAdapter.plannedOmega Q.joint P Q.usesPlan
            (I.endpointEffective.layer m)))
        ((HierarchyPackingPlan.parentCanonicalTestFamily H P G
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m)).testBody q)) :
    forall m,
      (upperEndpointCover C S m).IsKatzTaoAtScale A := by
  apply I.katzTao_endpoint_of_prefix A
  intro m
  exact Q.prefixFiber_isKatzTao_of_preMotion_finite_tests
    (I.effectivePrefix.path m) (I.endpointEffective.layer m)
    (I.effectivePrefix.parent m) A (hfinite m)

/-- Constructor for the discrete all-large bundle.  Its Katz--Tao field is
derived; only the logically independent all-large and Frostman endpoint data
remain inputs. -/
theorem discreteAllLargeStickyBounds_of_preMotion_finite_tests
    {epsilon : Real} (frostmanError katzTaoError : ENNReal)
    (hall : S.AllStepsLarge epsilon)
    (hfrostman : forall m,
      (upperEndpointCover C S m).IsFrostmanAtScale frostmanError)
    (hfinite : forall m q,
      IsKatzTaoAt katzTaoError
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H (I.endpointEffective.layer m)
            (I.effectivePrefix.parent m))
          (P.certificate (I.endpointEffective.layer m))
          (JointCertificateAdapter.plannedOmega Q.joint P Q.usesPlan
            (I.endpointEffective.layer m)))
        ((HierarchyPackingPlan.parentCanonicalTestFamily H P G
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m)).testBody q)) :
    DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError where
  all_large := hall
  frostman_endpoint := hfrostman
  katzTao_endpoint :=
    I.katzTao_endpoint_of_preMotion_finite_tests katzTaoError hfinite

end Identification

#print axioms Identification.endpointPrefixEmbedding
#print axioms Identification.endpointPrefix_body_eq
#print axioms Identification.endpoint_concentration_le_prefix
#print axioms Identification.katzTao_endpoint_of_prefix
#print axioms Identification.katzTao_endpoint_of_preMotion_finite_tests
#print axioms Identification.discreteAllLargeStickyBounds_of_preMotion_finite_tests

end
end FamilyStickyHierarchyEndpointPrefixBridgeV1
