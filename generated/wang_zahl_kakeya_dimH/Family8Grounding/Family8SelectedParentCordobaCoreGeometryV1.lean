import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
import Family8Grounding.Family8SelectedParentLogarithmicCordobaCoreV2

/-!
# Geometric form of the selected-parent Córdoba core

The coordinate cube in the log-free core is exactly the volume of the
actual common normalized John container constructed for the selected plank
bucket.  When the bucket has nonzero mass, its literal mean carrier mass is
also exactly the automatic quantitative-popularity floor.  Hence the core
is the paper-faithful quantity

`KT * volume(actual normalized John container) / popularity floor`.

No scalar comparison with Equation (46) is assumed here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentCordobaCoreGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentLogarithmicCordobaCoreV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Literal mean carrier mass used by the quantitative popularity
restriction on the actual selected-parent bucket. -/
noncomputable def selectedParentFineLevelBucketMeanCarrierMass
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  Ybucket.shadingMass /
    (((selectedParentPlankBucketIndices e S B hrho label).card :
      ENNReal) * 2)

/-- The log-free scalar core is exactly the Katz--Tao constant times the
volume of the actual normalized John container divided by the actual mean
carrier mass. -/
theorem selectedParentFineLevelCordobaCore_eq_containerVolume_div_mean
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal) :
    selectedParentFineLevelCordobaCore
        D S hrho P k r hr A label KT =
      KT *
        (volume (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space) /
          selectedParentFineLevelBucketMeanCarrierMass
            D S hrho P k r hr A label) := by
  rw [volume_selectedParentBucketNormalizedJohnContainer]
  rfl

/-- In the nonzero bucket branch, the literal mean carrier mass is exactly
the automatic quantitative-popularity floor used by certified Córdoba. -/
theorem selectedParentFineLevelBucketMeanCarrierMass_eq_quantitativeCarrierFloor
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int)
    (hmass :
      (selectedParentPlankBucketShading
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
        (blockAt S.activeCoarseFamily P k).fiber hrho label).shadingMass ≠ 0) :
    selectedParentFineLevelBucketMeanCarrierMass
        D S hrho P k r hr A label =
      quantitativeCarrierFloor
        (selectedParentPlankBucketShading
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
          (blockAt S.activeCoarseFamily P k).fiber hrho label) := by
  symm
  simpa only [selectedParentFineLevelBucketMeanCarrierMass,
    Fintype.card_coe] using
      quantitativeCarrierFloor_eq_mass_div_card_mul_two _ hmass

/-- Consequently, in the actual nonzero branch the core has the exact
container-volume / popularity-floor form consumed by the paper. -/
theorem selectedParentFineLevelCordobaCore_eq_containerVolume_div_popularityFloor
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal)
    (hmass :
      (selectedParentPlankBucketShading
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
        (blockAt S.activeCoarseFamily P k).fiber hrho label).shadingMass ≠ 0) :
    selectedParentFineLevelCordobaCore
        D S hrho P k r hr A label KT =
      KT *
        (volume (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space) /
          quantitativeCarrierFloor
            (selectedParentPlankBucketShading
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (fineShadingAtGreedyBlockLevel
                S D.shading P k A.fineLevel)
              (blockAt S.activeCoarseFamily P k).fiber hrho label)) := by
  rw [selectedParentFineLevelCordobaCore_eq_containerVolume_div_mean,
    selectedParentFineLevelBucketMeanCarrierMass_eq_quantitativeCarrierFloor
      D S hrho P k r hr A label hmass]

#print axioms
  selectedParentFineLevelCordobaCore_eq_containerVolume_div_mean
#print axioms
  selectedParentFineLevelBucketMeanCarrierMass_eq_quantitativeCarrierFloor
#print axioms
  selectedParentFineLevelCordobaCore_eq_containerVolume_div_popularityFloor

end

end Family8SelectedParentCordobaCoreGeometryV1
