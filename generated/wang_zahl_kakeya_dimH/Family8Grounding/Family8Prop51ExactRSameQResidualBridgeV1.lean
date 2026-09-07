import Family8Grounding.Family8Prop51ExactRLocalKTResidualDichotomyV1
import Family8Grounding.Family8SameQJointDensityDirectionalityV1
import Mathlib.Tactic

/-!
# Exact-R same-occurrence residual bridge for Proposition 5.1

Fix an occurrence `q` in an exact downstream retained set `R`, itself a
subset of the one canonical Proposition 5.1 joint bucket.  The upper half of
the canonical density band and its literal factor-two width give

`blockDensity F (blockAt F P q) ≤ 2 * prop51SelectedLowerDensity P Y base M`.

This is exactly the scalar local-KT premise of the existing exact-`R`
low/high residual dichotomy.  Both returned branches repeat the same retained
membership data so that `q` and `R` cannot silently change across the split;
both residuals also contain the same literal `refinementLoss`.

This file proves only that object-bound scalar routing.  In particular,
`sourceCF` is not claimed to carry a source Frostman certificate, and the
density-free high-branch scale is not claimed to be a geometric certificate.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51ExactRSameQResidualBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8Prop51ExactRLocalKTResidualDichotomyV1
open Family8SameQJointDensityDirectionalityV1

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Bind the literal local coefficient at one retained occurrence to the
existing exact-`R` low/high scalar dichotomy.  The repeated membership pair in
each branch is intentional: it records that both alternatives concern the
same input occurrence `q` and the same exact retained set `R`.

No `IsFrostmanOn` or `IsKatzTao` conclusion is manufactured here. -/
theorem prop51ExactR_sameQ_blockDensity_localKTResidual_dichotomy
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧ InENNRealDyadicBand base n
        (blockDensity F (blockAt F P k)))
    (R : Finset (Fin (blocks F P).length))
    (hRsubset : R ⊆ prop51SelectedOccurrences P Y base M)
    (q : Fin (blocks F P).length) (hq : q ∈ R)
    (ambient : ConvexBody Space)
    (A sourceCF refinementLoss : ENNReal) (gamma : Real)
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hlower0 : prop51SelectedLowerDensity P Y base M ≠ 0)
    (hlowerTop : prop51SelectedLowerDensity P Y base M ≠ ∞) :
    ((q ∈ R ∧ R ⊆ prop51SelectedOccurrences P Y base M) ∧
      (prop51SelectedLowerDensity P Y base M ≤ 1 ∧
        blockDensity F (blockAt F P q) ≤ 2 ∧
        (blockDensity F (blockAt F P q)) ^ (gamma / 2) *
            ((sourceCF * prop51SelectedUpperDensity P Y base M *
              (prop51SelectedLowerDensity P Y base M)⁻¹) *
                refinementLoss) ^ (1 - gamma / 2) ≤
          2 * (sourceCF * refinementLoss) ^ (1 - gamma / 2))) ∨
    ((q ∈ R ∧ R ⊆ prop51SelectedOccurrences P Y base M) ∧
      (1 ≤ prop51SelectedLowerDensity P Y base M ∧
        (blockDensity F (blockAt F P q)) ^ (gamma / 2) *
            (prop51SubselectedFineBlockDensityFrostmanConstant
              A P Y base M R ambient * refinementLoss) ^
                (1 - gamma / 2) ≤
          (2 : ENNReal) ^ (gamma / 2) *
            (prop51SubselectedFineDensityFreeScale A P R ambient *
              refinementLoss) ^ (1 - gamma / 2))) := by
  have hqSelected : q ∈ prop51SelectedOccurrences P Y base M :=
    hRsubset hq
  have hKTUpper :
      blockDensity F (blockAt F P q) ≤
        prop51SelectedUpperDensity P Y base M := by
    have hband := selectedJointOccurrenceBucket_densityBand
      P base M hcovered (prop51SelectedOccurrenceLabel P Y base M)
        q hqSelected
    simpa only [prop51SelectedUpperDensity] using hband.2.le
  have hKT :
      blockDensity F (blockAt F P q) ≤
        2 * prop51SelectedLowerDensity P Y base M := by
    calc
      blockDensity F (blockAt F P q) ≤
          prop51SelectedUpperDensity P Y base M := hKTUpper
      _ = 2 * prop51SelectedLowerDensity P Y base M :=
        prop51SelectedUpperDensity_eq_two_mul_lower P Y base M
  rcases prop51ExactR_localKTResidual_outerCoefficient_dichotomy
      P Y base M R ambient A (blockDensity F (blockAt F P q)) sourceCF
        refinementLoss gamma hgamma0 hgammaOne hlower0 hlowerTop hKT with
    hlow | hhigh
  · exact Or.inl <| And.intro (And.intro hq hRsubset) hlow
  · exact Or.inr <| And.intro (And.intro hq hRsubset) hhigh

#print axioms prop51ExactR_sameQ_blockDensity_localKTResidual_dichotomy

end
end Family8Prop51ExactRSameQResidualBridgeV1
