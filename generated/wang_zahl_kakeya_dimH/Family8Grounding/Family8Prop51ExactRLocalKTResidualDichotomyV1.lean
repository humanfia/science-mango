import Family8Grounding.Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
import Mathlib.Tactic

/-!
# Exact-R low/high density routing for the local KT residual

Let `d` be the lower endpoint of the canonical Proposition 5.1 block-density
band and assume the local Cordoba coefficient satisfies `KT ≤ 2d`.

* If `d ≤ 1`, then `KT ≤ 2`; the ordinary Equation (45) inherited
  coefficient is exactly `2 * sourceCF` because its upper endpoint is `2d`.
* If `1 ≤ d`, the literal `d⁻¹` in the exact-`R` normalized coefficient pays
  `KT^(gamma/2)` for `0 ≤ gamma ≤ 1`.

The two consumers remain separate.  In particular this file does not claim
that the density-free scalar in the second branch is itself a Frostman
constant, and it does not manufacture the exact-`R` source Frostman
certificate needed in the first branch.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51ExactRLocalKTResidualDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The density-free part of the exact-`R` normalized coefficient.  This is
only a scalar abbreviation: no Frostman statement with this coefficient is
claimed. -/
def prop51SubselectedFineDensityFreeScale
    (A : ENNReal)
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (ambient : ConvexBody Space) : ENNReal :=
  A * volume (ambient : Set Space) *
    (prop51SubselectedBodyVolume P R)⁻¹

/-- The exact-`R` coefficient contains one literal inverse of the common
Prop. 5.1 lower density.  This is only reassociation, so it needs no nonzero
or finiteness premise. -/
theorem prop51SubselectedFineBlockDensityFrostmanConstant_eq_densityFree_mul_inv
    (A : ENNReal)
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (R : Finset (Fin (blocks F P).length))
    (ambient : ConvexBody Space) :
    prop51SubselectedFineBlockDensityFrostmanConstant
        A P Y base M R ambient =
      prop51SubselectedFineDensityFreeScale A P R ambient *
        (prop51SelectedLowerDensity P Y base M)⁻¹ := by
  unfold prop51SubselectedFineBlockDensityFrostmanConstant
    prop51SubselectedFineDensityFreeScale
  ac_rfl

/-- Weak low-density exponent consumer.  The full downstream refinement loss
stays inside the outer power.  Neither coefficient needs to be nonzero or
finite. -/
theorem localKTResidual_mul_refinedCF_rpow_le_of_lowDensity
    (KT CF sourceCF refinementLoss : ENNReal) (gamma : Real)
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hKTTwo : KT ≤ 2) (hCF : CF ≤ sourceCF * 2) :
    KT ^ (gamma / 2) * (CF * refinementLoss) ^ (1 - gamma / 2) ≤
      2 * (sourceCF * refinementLoss) ^ (1 - gamma / 2) := by
  have hp : 0 ≤ gamma / 2 := by linarith
  have hq : 0 ≤ 1 - gamma / 2 := by linarith
  have hrefinedCF :
      CF * refinementLoss ≤ (sourceCF * refinementLoss) * 2 := by
    calc
      CF * refinementLoss ≤ (sourceCF * 2) * refinementLoss :=
        mul_le_mul' hCF le_rfl
      _ = (sourceCF * refinementLoss) * 2 := by ac_rfl
  calc
    KT ^ (gamma / 2) * (CF * refinementLoss) ^ (1 - gamma / 2) ≤
        (2 : ENNReal) ^ (gamma / 2) *
          ((sourceCF * refinementLoss) * 2) ^ (1 - gamma / 2) :=
      mul_le_mul'
        (ENNReal.rpow_le_rpow hKTTwo hp)
        (ENNReal.rpow_le_rpow hrefinedCF hq)
    _ = (2 : ENNReal) ^ (gamma / 2) *
        ((sourceCF * refinementLoss) ^ (1 - gamma / 2) *
          (2 : ENNReal) ^ (1 - gamma / 2)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
    _ = ((2 : ENNReal) ^ (gamma / 2) *
          (2 : ENNReal) ^ (1 - gamma / 2)) *
        (sourceCF * refinementLoss) ^ (1 - gamma / 2) := by ac_rfl
    _ = (2 : ENNReal) ^ ((gamma / 2) + (1 - gamma / 2)) *
        (sourceCF * refinementLoss) ^ (1 - gamma / 2) := by
      rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    _ = 2 * (sourceCF * refinementLoss) ^ (1 - gamma / 2) := by
      rw [show gamma / 2 + (1 - gamma / 2) = 1 by ring,
        ENNReal.rpow_one]

/-- Weak high-density exponent consumer.  A single literal inverse density
inside the refined outer coefficient pays the local residual.  `d ≠ 0` is
derived from `1 ≤ d`, so the only public finiteness premise is `d ≠ ∞`. -/
theorem localKTResidual_mul_refinedCF_rpow_le_of_highDensity
    (KT d CF sourceCF refinementLoss : ENNReal) (gamma : Real)
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hdTop : d ≠ ∞) (hKT : KT ≤ 2 * d) (hOneD : 1 ≤ d)
    (hCF : CF ≤ sourceCF * d⁻¹) :
    KT ^ (gamma / 2) * (CF * refinementLoss) ^ (1 - gamma / 2) ≤
      (2 : ENNReal) ^ (gamma / 2) *
        (sourceCF * refinementLoss) ^ (1 - gamma / 2) := by
  have hq : 0 ≤ 1 - gamma / 2 := by linarith
  have hd0 : d ≠ 0 := (zero_lt_one.trans_le hOneD).ne'
  have hrefinedCF :
      CF * refinementLoss ≤ (sourceCF * refinementLoss) * d⁻¹ := by
    calc
      CF * refinementLoss ≤ (sourceCF * d⁻¹) * refinementLoss :=
        mul_le_mul' hCF le_rfl
      _ = (sourceCF * refinementLoss) * d⁻¹ := by ac_rfl
  calc
    KT ^ (gamma / 2) * (CF * refinementLoss) ^ (1 - gamma / 2) ≤
        KT ^ (gamma / 2) *
          ((sourceCF * refinementLoss) * d⁻¹) ^
            (1 - gamma / 2) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hrefinedCF hq)
    _ ≤ (2 : ENNReal) ^ (gamma / 2) *
        (sourceCF * refinementLoss) ^ (1 - gamma / 2) :=
      localKTResidual_mul_densityInverseOuterPower_le_of_one_le_density
        hgamma0 hgammaOne hd0 hdTop hKT hOneD

/-- Exact Prop. 5.1 low-density wrapper.  The local coefficient is at most
two, while the factor-two band makes the Equation (45) inherited coefficient
exactly `2 * sourceCF`.  `sourceCF`'s genuine `IsFrostmanOn` certificate on
the exact downstream set `R` remains a separate geometric input. -/
theorem prop51LowDensity_localKTResidual_mul_inheritedCF_rpow_le
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (KT sourceCF refinementLoss : ENNReal) (gamma : Real)
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hlower0 : prop51SelectedLowerDensity P Y base M ≠ 0)
    (hlowerTop : prop51SelectedLowerDensity P Y base M ≠ ∞)
    (hKT : KT ≤ 2 * prop51SelectedLowerDensity P Y base M)
    (hdOne : prop51SelectedLowerDensity P Y base M ≤ 1) :
    KT ≤ 2 ∧
      KT ^ (gamma / 2) *
          ((sourceCF * prop51SelectedUpperDensity P Y base M *
            (prop51SelectedLowerDensity P Y base M)⁻¹) *
              refinementLoss) ^ (1 - gamma / 2) ≤
        2 * (sourceCF * refinementLoss) ^ (1 - gamma / 2) := by
  let d := prop51SelectedLowerDensity P Y base M
  have hKTTwo : KT ≤ 2 := by
    calc
      KT ≤ 2 * d := by simpa only [d] using hKT
      _ ≤ 2 * 1 := mul_le_mul' le_rfl hdOne
      _ = 2 := by simp
  have hupper : prop51SelectedUpperDensity P Y base M = 2 * d := by
    dsimp only [d]
    unfold prop51SelectedUpperDensity prop51SelectedLowerDensity
    rw [pow_succ]
    ac_rfl
  have hinherited :
      sourceCF * prop51SelectedUpperDensity P Y base M * d⁻¹ =
        sourceCF * 2 := by
    rw [hupper]
    calc
      sourceCF * (2 * d) * d⁻¹ =
          sourceCF * 2 * (d * d⁻¹) := by ac_rfl
      _ = sourceCF * 2 := by
        rw [ENNReal.mul_inv_cancel (by simpa only [d] using hlower0)
          (by simpa only [d] using hlowerTop), mul_one]
  refine ⟨hKTTwo, ?_⟩
  apply localKTResidual_mul_refinedCF_rpow_le_of_lowDensity
    KT
    (sourceCF * prop51SelectedUpperDensity P Y base M *
      (prop51SelectedLowerDensity P Y base M)⁻¹)
    sourceCF refinementLoss gamma hgamma0 hgammaOne hKTTwo
  exact le_of_eq (by simpa only [d] using hinherited)

/-- In the high-density branch the one literal `d⁻¹` in the normalized
exact-`R` coefficient pays the local `KT^(gamma/2)` residual.  No body-volume
or source coefficient is cancelled here. -/
theorem prop51HighDensity_localKTResidual_mul_subselectedCF_rpow_le
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (R : Finset (Fin (blocks F P).length))
    (ambient : ConvexBody Space) (A KT refinementLoss : ENNReal)
    (gamma : Real)
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hlowerTop : prop51SelectedLowerDensity P Y base M ≠ ∞)
    (hKT : KT ≤ 2 * prop51SelectedLowerDensity P Y base M)
    (hOneD : 1 ≤ prop51SelectedLowerDensity P Y base M) :
    KT ^ (gamma / 2) *
        (prop51SubselectedFineBlockDensityFrostmanConstant
          A P Y base M R ambient * refinementLoss) ^
            (1 - gamma / 2) ≤
      (2 : ENNReal) ^ (gamma / 2) *
        (prop51SubselectedFineDensityFreeScale A P R ambient *
          refinementLoss) ^
          (1 - gamma / 2) := by
  apply localKTResidual_mul_refinedCF_rpow_le_of_highDensity
    KT (prop51SelectedLowerDensity P Y base M)
    (prop51SubselectedFineBlockDensityFrostmanConstant
      A P Y base M R ambient)
    (prop51SubselectedFineDensityFreeScale A P R ambient)
    refinementLoss gamma hgamma0 hgammaOne hlowerTop hKT hOneD
  exact le_of_eq
    (prop51SubselectedFineBlockDensityFrostmanConstant_eq_densityFree_mul_inv
      A P Y base M R ambient)

/-- Exhaustive exact-`R` routing for the local KT residual.  The low branch
uses the existing source Frostman route with Equation (45)'s factor-two
inherited coefficient; the high branch uses the normalized exact-`R`
coefficient.  The two conclusions deliberately remain different. -/
theorem prop51ExactR_localKTResidual_outerCoefficient_dichotomy
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (R : Finset (Fin (blocks F P).length))
    (ambient : ConvexBody Space)
    (A KT sourceCF refinementLoss : ENNReal) (gamma : Real)
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hlower0 : prop51SelectedLowerDensity P Y base M ≠ 0)
    (hlowerTop : prop51SelectedLowerDensity P Y base M ≠ ∞)
    (hKT : KT ≤ 2 * prop51SelectedLowerDensity P Y base M) :
    (prop51SelectedLowerDensity P Y base M ≤ 1 ∧
      KT ≤ 2 ∧
      KT ^ (gamma / 2) *
          ((sourceCF * prop51SelectedUpperDensity P Y base M *
            (prop51SelectedLowerDensity P Y base M)⁻¹) *
              refinementLoss) ^ (1 - gamma / 2) ≤
        2 * (sourceCF * refinementLoss) ^ (1 - gamma / 2)) ∨
    (1 ≤ prop51SelectedLowerDensity P Y base M ∧
      KT ^ (gamma / 2) *
          (prop51SubselectedFineBlockDensityFrostmanConstant
            A P Y base M R ambient * refinementLoss) ^
              (1 - gamma / 2) ≤
        (2 : ENNReal) ^ (gamma / 2) *
          (prop51SubselectedFineDensityFreeScale A P R ambient *
            refinementLoss) ^
            (1 - gamma / 2)) := by
  rcases le_total (prop51SelectedLowerDensity P Y base M) 1 with
      hdOne | hOneD
  · obtain ⟨hKTTwo, hresidual⟩ :=
      prop51LowDensity_localKTResidual_mul_inheritedCF_rpow_le
        P Y base M KT sourceCF refinementLoss gamma hgamma0 hgammaOne
          hlower0 hlowerTop hKT hdOne
    exact Or.inl ⟨hdOne, hKTTwo, hresidual⟩
  · exact Or.inr ⟨hOneD,
      prop51HighDensity_localKTResidual_mul_subselectedCF_rpow_le
        P Y base M R ambient A KT refinementLoss gamma hgamma0 hgammaOne
          hlowerTop hKT hOneD⟩

#print axioms prop51SubselectedFineDensityFreeScale
#print axioms
  prop51SubselectedFineBlockDensityFrostmanConstant_eq_densityFree_mul_inv
#print axioms localKTResidual_mul_refinedCF_rpow_le_of_lowDensity
#print axioms localKTResidual_mul_refinedCF_rpow_le_of_highDensity
#print axioms prop51LowDensity_localKTResidual_mul_inheritedCF_rpow_le
#print axioms
  prop51HighDensity_localKTResidual_mul_subselectedCF_rpow_le
#print axioms prop51ExactR_localKTResidual_outerCoefficient_dichotomy

end
end Family8Prop51ExactRLocalKTResidualDichotomyV1
