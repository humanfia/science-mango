import Family8Grounding.Family8Prop51ExactRLocalKTResidualDichotomyV1
import Family8Grounding.Family8SameQJointDensityDirectionalityV1
import Mathlib.Tactic

/-!
# Same-q singleton exact-R residual route

For a fixed greedy occurrence `q`, take the exact retained set to be the
singleton `{q}`, take the density-band depth to be zero, and take its base to
be the literal local block density.  The density-label coordinate then lies
in `Fin 1`, so the canonical lower and upper scalar endpoints are the local
density and twice the local density, independently of the fibre-cardinality
label chosen by Proposition 5.1.

The final theorem calls the scalar exact-`R` dichotomy directly.  In
particular, it does not assert that `q` belongs to the canonical Proposition
5.1 occurrence bucket and does not require the singleton to be a subset of
that bucket.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SameQSingletonExactRResidualV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8Prop51ExactRLocalKTResidualDichotomyV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8SameQJointDensityDirectionalityV1

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- With no nontrivial density-band coordinate, the selected lower endpoint
is the supplied base.  This does not depend on which fibre-cardinality label
the weighted selection chose. -/
theorem prop51SelectedLowerDensity_zero_eq
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) :
    prop51SelectedLowerDensity P Y base 0 = base := by
  simp [prop51SelectedLowerDensity]

/-- At depth zero the selected upper endpoint is exactly twice the supplied
base. -/
theorem prop51SelectedUpperDensity_zero_eq
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) :
    prop51SelectedUpperDensity P Y base 0 = 2 * base := by
  rw [prop51SelectedUpperDensity_eq_two_mul_lower,
    prop51SelectedLowerDensity_zero_eq]

/-- Direct scalar low/high residual routing for one fixed occurrence.

The local Katz--Tao coefficient is the literal block density `d`; the exact
retained set is `{q}`.  No canonical Proposition 5.1 membership or density
coverage of any other greedy block is assumed. -/
theorem sameQ_singletonExactR_blockDensity_localKTResidual_dichotomy
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (q : Fin (blocks F P).length)
    (ambient : ConvexBody Space)
    (A sourceCF refinementLoss : ENNReal) (gamma : Real)
    (hgamma0 : 0 <= gamma) (hgammaOne : gamma <= 1)
    (hd0 : blockDensity F (blockAt F P q) ≠ 0)
    (hdTop : blockDensity F (blockAt F P q) ≠ ∞) :
    let d := blockDensity F (blockAt F P q)
    (d <= 1 /\
      d <= 2 /\
      d ^ (gamma / 2) *
          ((sourceCF * (2 * d) * d⁻¹) * refinementLoss) ^
              (1 - gamma / 2) <=
        2 * (sourceCF * refinementLoss) ^ (1 - gamma / 2)) \/
    (1 <= d /\
      d ^ (gamma / 2) *
          (prop51SubselectedFineBlockDensityFrostmanConstant
            A P Y d 0 {q} ambient * refinementLoss) ^
              (1 - gamma / 2) <=
        (2 : ENNReal) ^ (gamma / 2) *
          (prop51SubselectedFineDensityFreeScale A P {q} ambient *
            refinementLoss) ^ (1 - gamma / 2)) := by
  dsimp only
  let d := blockDensity F (blockAt F P q)
  have hlower0 : prop51SelectedLowerDensity P Y d 0 ≠ 0 := by
    rw [prop51SelectedLowerDensity_zero_eq]
    exact hd0
  have hlowerTop : prop51SelectedLowerDensity P Y d 0 ≠ ∞ := by
    rw [prop51SelectedLowerDensity_zero_eq]
    exact hdTop
  have hKT : d <= 2 * prop51SelectedLowerDensity P Y d 0 := by
    rw [prop51SelectedLowerDensity_zero_eq]
    calc
      d = d * 1 := by simp
      _ <= d * 2 := mul_le_mul' le_rfl (by norm_num)
      _ = 2 * d := by ac_rfl
  have h := prop51ExactR_localKTResidual_outerCoefficient_dichotomy
    P Y d 0 {q} ambient A d sourceCF refinementLoss gamma
      hgamma0 hgammaOne hlower0 hlowerTop hKT
  simpa only [prop51SelectedLowerDensity_zero_eq,
    prop51SelectedUpperDensity_zero_eq] using h

#print axioms prop51SelectedLowerDensity_zero_eq
#print axioms prop51SelectedUpperDensity_zero_eq
#print axioms
  sameQ_singletonExactR_blockDensity_localKTResidual_dichotomy

end

end Family8SameQSingletonExactRResidualV1
