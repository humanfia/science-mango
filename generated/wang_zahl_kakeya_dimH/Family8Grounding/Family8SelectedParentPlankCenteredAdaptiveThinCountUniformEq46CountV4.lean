import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
open Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The SAFE V3 single-`W` full-fibre conclusion lifts to the finite uniform
`tubesPerPlank` on that same actual bucket. -/
theorem selectedFineCard_le_centeredAdaptiveUniform_of_actualCap
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (C : ENNReal)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label})
    (hfull : Fintype.card (SelectedPlankFineIndex S W) ≤
      adaptiveThinCountFullFiberNatCap
        (centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
          s e S B hrho label hplank W C) label) :
    Fintype.card (SelectedPlankFineIndex S W) ≤
      centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho label hplank C :=
  hfull.trans
    (actualFullFiberNatCap_le_centeredAdaptiveUniform
      s e S B hrho label hplank C W)

#print axioms selectedFineCard_le_centeredAdaptiveUniform_of_actualCap

end
end Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV4
