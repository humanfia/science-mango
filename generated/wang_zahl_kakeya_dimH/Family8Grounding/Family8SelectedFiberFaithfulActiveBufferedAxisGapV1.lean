import Family8Grounding.Family8EighthNormalizedSelectedAncestorAxisGapV1
import Family8Grounding.Family8SelectedFiberFaithfulCoherentSuccessorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedFiberFaithfulActiveBufferedAxisGapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EighthNormalizedSelectedAncestorAxisGapV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SelectedFiberFaithfulCoherentSuccessorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}

/-!
# Active selected-ancestor buffered connector

The actual active child and ancestor are definitionally the literal eighth
normalizations of the selected source parent and its coherent-cover ancestor.
This module specializes the generic `27 * sigma / 8` axis-gap theorem to those
same objects.  It neither repicks an index nor manufactures a cover.
-/

/-- The actual scale of an active ancestor with its explicit geometric
buffer. -/
def activeParentBufferedProxyScale (sigma buffer : NNReal) : NNReal :=
  activeParentProxyScale sigma + buffer

@[simp]
theorem activeParentBufferedProxyScale_eq
    (sigma buffer : NNReal) :
    activeParentBufferedProxyScale sigma buffer = sigma / 8 + buffer := by
  rfl

/-- The literal active child radius is below every buffered ancestor scale as
soon as its source scale is below the ancestor source scale. -/
theorem activeParentChildRadius_le_bufferedProxyScale
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    {sigma : NNReal} (hRhoSigma : W.rho <= sigma)
    (buffer : NNReal) :
    W.rho / 8 <= activeParentBufferedProxyScale sigma buffer := by
  calc
    W.rho / 8 <= activeParentProxyScale sigma :=
      activeParentChildRadius_le_proxyScale W hRhoSigma
    _ <= activeParentProxyScale sigma + buffer :=
      le_add_right (le_refl _)

/-- The source coherent cover supplies the genuine selected active ancestor;
the proved axis gap and one scalar buffer comparison supply the complete
literal normalized carrier step. -/
theorem activeParent_selectedAncestorBufferedStep_of_source
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (sigma : NNReal) (hRhoSigma : W.rho <= sigma)
    (hSigmaOne : sigma <= 1)
    (i : {k // k ∈ X.dualChild.activeParentSelected})
    (buffer : NNReal)
    (haxisGapBuffer :
      eighthNormalizedSelectedAncestorAxisGap sigma <= buffer) :
    EighthNormalizedSelectedAncestorBufferedStep
      ((crossingBaseCover W).coarse.tubes i.1.1)
      (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)
      buffer := by
  have hTU := C.carrier_subset W.rho sigma
    (crossingDeltaLeRho W) hRhoSigma hSigmaOne i.1.1 i.1.2
  exact eighthNormalizedSelectedAncestorBufferedStep_of_source
    ((crossingBaseCover W).coarse.tubes i.1.1)
    (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)
    buffer hRhoSigma hTU haxisGapBuffer

/-- End-to-end literal carrier inclusion for the actual selected active child
into the buffered normalization of its actual coherent source ancestor. -/
theorem activeParentChildDatum_family_subset_selectedAncestorContainingTube
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (sigma : NNReal) (hRhoSigma : W.rho <= sigma)
    (hSigmaOne : sigma <= 1)
    (i : {k // k ∈ X.dualChild.activeParentSelected})
    (buffer : NNReal)
    (haxisGapBuffer :
      eighthNormalizedSelectedAncestorAxisGap sigma <= buffer) :
    (X.dualChild.activeParentChildDatum.family.tubes i).carrier ⊆
      (eighthNormalizedContainingTube
        (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)
        buffer).carrier := by
  rw [activeParentChildDatum_family_tubes]
  exact
    (activeParent_selectedAncestorBufferedStep_of_source W X sigma
      hRhoSigma hSigmaOne i buffer haxisGapBuffer).actual_normalized_subset_buffered_parent

#print axioms activeParentBufferedProxyScale
#print axioms activeParentChildRadius_le_bufferedProxyScale
#print axioms activeParent_selectedAncestorBufferedStep_of_source
#print axioms activeParentChildDatum_family_subset_selectedAncestorContainingTube

end
end Family8SelectedFiberFaithfulActiveBufferedAxisGapV1
