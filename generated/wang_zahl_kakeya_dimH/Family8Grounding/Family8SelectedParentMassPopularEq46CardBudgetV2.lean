import Family8Grounding.Family8SelectedParentMassPopularCordobaCoreV2
import Mathlib.Tactic

/-!
# Actual cardinal envelope for the mass-popular Equation (46) budget

The literal selected side bucket is a subset of one greedy block, while both
the block and the list of greedy occurrences live in the finite active-parent
family.  This gives a callback-free quadratic active-cardinality envelope for
the two count factors in the division-free Cordoba budget.

The estimate is intentionally recorded as a coarse fallback.  A paper-strength
Lemma 5.11 producer must replace the quadratic envelope by logarithmic
uniformity losses; this module does not claim that the coarse power is
absorbable.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentMassPopularEq46CardBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularCordobaCoreV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- A literal side-shape bucket has no more members than its selected greedy
block. -/
theorem selectedParentPlankBucketIndices_card_le_block
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (e : Space ≃ᵃ[Real] Space) (label : Fin 3 -> Int) :
    (selectedParentPlankBucketIndices e S
        (blockAt S.activeCoarseFamily P k).fiber hrho label).card ≤
      (blockAt S.activeCoarseFamily P k).fiber.card := by
  calc
    (selectedParentPlankBucketIndices e S
        (blockAt S.activeCoarseFamily P k).fiber hrho label).card ≤
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_univ p
    _ = (blockAt S.activeCoarseFamily P k).fiber.card := by
      rw [Finset.card_univ, Fintype.card_coe]

/-- Every selected block is a subset of the active-parent type. -/
theorem selectedParent_block_card_le_activeCard
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    (blockAt S.activeCoarseFamily P k).fiber.card ≤
      Fintype.card (ActiveParentIndex S) := by
  exact Finset.card_le_univ _

/-- The number of actual greedy occurrences is bounded by the same active
cardinality. -/
theorem selectedParent_partition_length_le_activeCard
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ) :
    P.length ≤ Fintype.card (ActiveParentIndex S) := by
  simpa only [Finset.card_univ] using P.length_le_card

/-- Coarse explicit envelope after replacing both literal count factors by
the total active-parent cardinality. -/
noncomputable def selectedParentMassPopularCordobaCardEnvelope
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) {loss : Nat}
    (_A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal) : ENNReal :=
  ((loss : ENNReal) *
      (Fintype.card (ActiveParentIndex S) : ENNReal) ^ (2 : Nat) *
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
    (KT * volume
      (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space))

/-- The actual division-free budget is bounded by the coarse active-card
envelope, with no density or multiplicity premise. -/
theorem selectedParentMassPopularCordobaCoreBudget_le_cardEnvelope
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
    selectedParentMassPopularCordobaCoreBudget
        D S hrho P k r hr A label KT ≤
      selectedParentMassPopularCordobaCardEnvelope
        D S hrho P k r A label KT := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let bucketCard : ENNReal :=
    (selectedParentPlankBucketIndices e S
      (blockAt S.activeCoarseFamily P k).fiber hrho label).card
  let activeCard : ENNReal := Fintype.card (ActiveParentIndex S)
  have hlengthNat : P.length ≤ Fintype.card (ActiveParentIndex S) :=
    selectedParent_partition_length_le_activeCard D S P
  have hbucketNat :
      (selectedParentPlankBucketIndices e S
        (blockAt S.activeCoarseFamily P k).fiber hrho label).card ≤
        Fintype.card (ActiveParentIndex S) :=
    (selectedParentPlankBucketIndices_card_le_block
      D S hrho P k e label).trans
        (selectedParent_block_card_le_activeCard D S P k)
  have hlength : (P.length : ENNReal) ≤ activeCard := by
    dsimp only [activeCard]
    exact_mod_cast hlengthNat
  have hbucket : bucketCard ≤ activeCard := by
    dsimp only [bucketCard, activeCard]
    exact_mod_cast hbucketNat
  have hproduct : (P.length : ENNReal) * bucketCard ≤
      activeCard * activeCard := mul_le_mul' hlength hbucket
  unfold selectedParentMassPopularCordobaCoreBudget
  change
    (((loss : ENNReal) * (P.length : ENNReal) *
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
      (bucketCard * 2)) *
        (KT * volume
          (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space)) ≤ _
  rw [selectedParentMassPopularCordobaCardEnvelope]
  calc
    (((loss : ENNReal) * (P.length : ENNReal) *
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
      (bucketCard * 2)) *
        (KT * volume
          (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space)) =
      ((loss : ENNReal) * ((P.length : ENNReal) * bucketCard) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
        (KT * volume
          (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space)) := by ac_rfl
    _ ≤ ((loss : ENNReal) * (activeCard * activeCard) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
        (KT * volume
          (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space)) := by
      gcongr
    _ = ((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal) ^ (2 : Nat) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
        (KT * volume
          (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space)) := by
      dsimp only [activeCard]
      rw [pow_two]

#print axioms selectedParentPlankBucketIndices_card_le_block
#print axioms selectedParent_block_card_le_activeCard
#print axioms selectedParent_partition_length_le_activeCard
#print axioms selectedParentMassPopularCordobaCardEnvelope
#print axioms selectedParentMassPopularCordobaCoreBudget_le_cardEnvelope

end

end Family8SelectedParentMassPopularEq46CardBudgetV2
