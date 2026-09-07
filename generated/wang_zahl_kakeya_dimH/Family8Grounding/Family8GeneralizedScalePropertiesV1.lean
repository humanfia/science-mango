import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8GeneralizedScalePropertiesV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# The nontrivial relative-scale branch of the generalized KKT/KF remark

Remark `multBoundsDeltaVsRho` replaces the scale `delta` in the density and
concentration hypotheses by a relative scale `tau ≤ delta`.  If an original
property supplies the exponent `etaOne`, the remark chooses

`eta = epsilon * etaOne / 100`.

This module proves all power comparisons in the branch
`delta ^ (100 / epsilon) < tau`.  It then applies the original property to the
same tube family and shading; no affine rescaling is used or hidden here.

The complementary branch `tau ≤ delta ^ (100 / epsilon)` in the paper is
closed by a crude a priori multiplicity estimate.  That estimate is not a
field of `ActualTubeDatum` or either property predicate, so this file does not
assert the full two-branch remark and does not assume the desired final
multiplicity inequality.
-/

/-- The loss exponent used by the relative-scale argument in the paper. -/
def relativeScaleEta (epsilon etaOne : Real) : Real :=
  epsilon * etaOne / 100

/-- Katz--Tao density and concentration hypotheses measured at `tau`, while
the underlying family still consists of `delta`-tubes. -/
def KatzTaoHypothesesAtRelativeScale {delta : NNReal} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (tau : NNReal) (eta : Real) : Prop :=
  (tau : ENNReal) ^ eta ≤ D.shading.shadingDensity ∧
    maximalConcentration D.family.bodyFamily ≤ (tau : ENNReal) ^ (-eta)

/-- Frostman density and nonconcentration hypotheses measured at `tau`. -/
def FrostmanHypothesesAtRelativeScale {delta : NNReal} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (tau : NNReal) (eta : Real) : Prop :=
  (tau : ENNReal) ^ eta ≤ D.shading.shadingDensity ∧
    IsFrostmanIn ((tau : ENNReal) ^ (-eta))
      D.family.bodyFamily unitBallBody


/-- The Frostman right-hand side with only the loss scale changed to `tau`.
The geometric normalization remains at the actual tube radius `delta`. -/
def frostmanRelativeScaleMultiplicityRHS (delta tau : NNReal)
    (actualVolume : ENNReal) (epsilon beta : Real) : ENNReal :=
  (tau : ENNReal) ^ (-epsilon) *
    (delta : ENNReal) ^ (-2 * beta) *
      actualVolume ^ (1 - beta / 2)
/-- Fixed-parameter Katz--Tao statement for the nontrivial relative-scale
branch.  Its conclusion has the paper's `tau ^ (-epsilon)` loss. -/
def KatzTaoAtNontrivialRelativeScaleParameters
    (beta epsilon eta : Real) (delta0 : NNReal) : Prop :=
  ∀ (delta tau : NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
      (D : ActualTubeDatum delta ι),
    D.IsAdmissible →
    delta ≤ delta0 →
    0 < tau →
    tau ≤ delta →
    (delta : ENNReal) ^ (100 / epsilon) < (tau : ENNReal) →
    KatzTaoHypothesesAtRelativeScale D tau eta →
    D.shading.averageMultiplicity ≤
      katzTaoMultiplicityRHS tau (Fintype.card ι) epsilon beta

/-- Fixed-parameter Frostman statement for the same relative-scale branch. -/
def FrostmanAtNontrivialRelativeScaleParameters
    (beta epsilon eta : Real) (delta0 : NNReal) : Prop :=
  ∀ (delta tau : NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
      (D : ActualTubeDatum delta ι),
    D.IsAdmissible →
    delta ≤ delta0 →
    0 < tau →
    tau ≤ delta →
    (delta : ENNReal) ^ (100 / epsilon) < (tau : ENNReal) →
    FrostmanHypothesesAtRelativeScale D tau eta →
    D.shading.averageMultiplicity ≤
      frostmanRelativeScaleMultiplicityRHS
        delta tau D.actualFamilyVolume epsilon beta

/-- The chosen relative-scale exponent is positive. -/
theorem relativeScaleEta_pos {epsilon etaOne : Real}
    (hepsilon : 0 < epsilon) (hetaOne : 0 < etaOne) :
    0 < relativeScaleEta epsilon etaOne := by
  unfold relativeScaleEta
  positivity

/-- The exact exponent identity behind both premise comparisons. -/
theorem relativeScale_exponent_identity {epsilon etaOne : Real}
    (hepsilon : 0 < epsilon) :
    (100 / epsilon) * relativeScaleEta epsilon etaOne = etaOne := by
  unfold relativeScaleEta
  field_simp [ne_of_gt hepsilon]

/-- In the nontrivial branch, a `tau`-density lower bound implies the
original `delta`-density lower bound. -/
theorem delta_rpow_etaOne_le_tau_rpow_relativeScaleEta
    {delta tau : ENNReal} {epsilon etaOne : Real}
    (hepsilon : 0 < epsilon) (hetaOne : 0 < etaOne)
    (hthreshold : delta ^ (100 / epsilon) ≤ tau) :
    delta ^ etaOne ≤ tau ^ relativeScaleEta epsilon etaOne := by
  calc
    delta ^ etaOne =
        delta ^ ((100 / epsilon) * relativeScaleEta epsilon etaOne) := by
      exact congrArg (fun exponent : Real ↦ delta ^ exponent)
        (relativeScale_exponent_identity hepsilon).symm
    _ = (delta ^ (100 / epsilon)) ^ relativeScaleEta epsilon etaOne :=
      ENNReal.rpow_mul delta (100 / epsilon) (relativeScaleEta epsilon etaOne)
    _ ≤ tau ^ relativeScaleEta epsilon etaOne :=
      ENNReal.rpow_le_rpow hthreshold
        (le_of_lt (relativeScaleEta_pos hepsilon hetaOne))

/-- The concentration constant at `tau` is no larger than the original
constant at `delta`. -/
theorem tau_rpow_neg_relativeScaleEta_le_delta_rpow_neg_etaOne
    {delta tau : ENNReal} {epsilon etaOne : Real}
    (hepsilon : 0 < epsilon) (hetaOne : 0 < etaOne)
    (hthreshold : delta ^ (100 / epsilon) ≤ tau) :
    tau ^ (-relativeScaleEta epsilon etaOne) ≤ delta ^ (-etaOne) := by
  have hpositive :=
    delta_rpow_etaOne_le_tau_rpow_relativeScaleEta
      hepsilon hetaOne hthreshold
  simpa only [ENNReal.rpow_neg] using ENNReal.inv_le_inv' hpositive

/-- Since `tau ≤ delta`, the loss at `delta` is bounded by the (weaker) loss
at `tau`. -/
theorem delta_rpow_neg_epsilon_le_tau_rpow_neg_epsilon
    {delta tau : ENNReal} {epsilon : Real}
    (hepsilon : 0 < epsilon) (htau : tau ≤ delta) :
    delta ^ (-epsilon) ≤ tau ^ (-epsilon) := by
  have hpositive : tau ^ epsilon ≤ delta ^ epsilon :=
    ENNReal.rpow_le_rpow htau (le_of_lt hepsilon)
  simpa only [ENNReal.rpow_neg] using ENNReal.inv_le_inv' hpositive

/-- Convert relative-scale Katz--Tao premises to the original premises on
the same family. -/
theorem katzTaoHypotheses_of_relativeScale
    {delta tau : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    {epsilon etaOne : Real} (D : ActualTubeDatum delta ι)
    (hepsilon : 0 < epsilon) (hetaOne : 0 < etaOne)
    (hthreshold : (delta : ENNReal) ^ (100 / epsilon) ≤ (tau : ENNReal))
    (hrelative : KatzTaoHypothesesAtRelativeScale D tau
      (relativeScaleEta epsilon etaOne)) :
    KatzTaoHypotheses D etaOne := by
  refine ⟨?_, ?_⟩
  · exact
      (delta_rpow_etaOne_le_tau_rpow_relativeScaleEta
        hepsilon hetaOne hthreshold).trans hrelative.1
  · exact hrelative.2.trans
      (tau_rpow_neg_relativeScaleEta_le_delta_rpow_neg_etaOne
        hepsilon hetaOne hthreshold)

/-- Convert relative-scale Frostman premises to the original premises on the
same family. -/
theorem frostmanHypotheses_of_relativeScale
    {delta tau : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    {epsilon etaOne : Real} (D : ActualTubeDatum delta ι)
    (hepsilon : 0 < epsilon) (hetaOne : 0 < etaOne)
    (hthreshold : (delta : ENNReal) ^ (100 / epsilon) ≤ (tau : ENNReal))
    (hrelative : FrostmanHypothesesAtRelativeScale D tau
      (relativeScaleEta epsilon etaOne)) :
    FrostmanHypotheses D etaOne := by
  refine ⟨?_, ?_⟩
  · exact
      (delta_rpow_etaOne_le_tau_rpow_relativeScaleEta
        hepsilon hetaOne hthreshold).trans hrelative.1
  · exact hrelative.2.mono
      (tau_rpow_neg_relativeScaleEta_le_delta_rpow_neg_etaOne
        hepsilon hetaOne hthreshold)

/-- Numerical comparison of the Katz--Tao right-hand sides. -/
theorem katzTaoMultiplicityRHS_delta_le_tau
    {delta tau : NNReal} {tubeCount : Nat} {epsilon beta : Real}
    (hepsilon : 0 < epsilon) (htau : tau ≤ delta) :
    katzTaoMultiplicityRHS delta tubeCount epsilon beta ≤
      katzTaoMultiplicityRHS tau tubeCount epsilon beta := by
  unfold katzTaoMultiplicityRHS
  exact mul_le_mul_left
    (delta_rpow_neg_epsilon_le_tau_rpow_neg_epsilon
      hepsilon (ENNReal.coe_le_coe.mpr htau)) _

/-- Numerical comparison of the Frostman right-hand sides. -/
theorem frostmanMultiplicityRHS_delta_le_tau
    {delta tau : NNReal} {actualVolume : ENNReal} {epsilon beta : Real}
    (hepsilon : 0 < epsilon) (htau : tau ≤ delta) :
    frostmanMultiplicityRHS delta actualVolume epsilon beta ≤
      frostmanRelativeScaleMultiplicityRHS
        delta tau actualVolume epsilon beta := by
  unfold frostmanMultiplicityRHS frostmanRelativeScaleMultiplicityRHS
  exact mul_le_mul_left
    (mul_le_mul_left
      (delta_rpow_neg_epsilon_le_tau_rpow_neg_epsilon
        hepsilon (ENNReal.coe_le_coe.mpr htau))
      ((delta : ENNReal) ^ (-2 * beta)))
    (actualVolume ^ (1 - beta / 2))

/-- A fixed-parameter Katz--Tao estimate implies the nontrivial branch of its
relative-scale version. -/
theorem katzTaoAtParameters_toNontrivialRelativeScale
    {beta epsilon etaOne : Real} {delta0 : NNReal}
    (h : KatzTaoAtParameters beta epsilon etaOne delta0)
    (hepsilon : 0 < epsilon) (hetaOne : 0 < etaOne) :
    KatzTaoAtNontrivialRelativeScaleParameters beta epsilon
      (relativeScaleEta epsilon etaOne) delta0 := by
  intro delta tau ι _ _ D hD hdelta _htau_pos htau hthreshold hrelative
  exact
    (h delta ι D hD hdelta
      (katzTaoHypotheses_of_relativeScale D hepsilon hetaOne hthreshold.le
        hrelative)).trans
      (katzTaoMultiplicityRHS_delta_le_tau hepsilon htau)

/-- A fixed-parameter Frostman estimate implies the nontrivial branch of its
relative-scale version. -/
theorem frostmanAtParameters_toNontrivialRelativeScale
    {beta epsilon etaOne : Real} {delta0 : NNReal}
    (h : FrostmanAtParameters beta epsilon etaOne delta0)
    (hepsilon : 0 < epsilon) (hetaOne : 0 < etaOne) :
    FrostmanAtNontrivialRelativeScaleParameters beta epsilon
      (relativeScaleEta epsilon etaOne) delta0 := by
  intro delta tau ι _ _ D hD hdelta _htau_pos htau hthreshold hrelative
  exact
    (h delta ι D hD hdelta
      (frostmanHypotheses_of_relativeScale D hepsilon hetaOne hthreshold.le
        hrelative)).trans
      (frostmanMultiplicityRHS_delta_le_tau hepsilon htau)

/-- Quantifier-level generalized-scale adapter for `K_KT(beta)`, restricted
honestly to the nontrivial threshold branch. -/
theorem KatzTaoProperty.exists_nontrivialRelativeScale_parameters
    {beta epsilon : Real} (h : KatzTaoProperty beta)
    (hepsilon : 0 < epsilon) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        KatzTaoAtNontrivialRelativeScaleParameters
          beta epsilon eta delta0 := by
  obtain ⟨etaOne, delta0, hetaOne, hdelta0, hhalf, hparameters⟩ :=
    h.exists_parameters hepsilon
  exact ⟨relativeScaleEta epsilon etaOne, delta0,
    relativeScaleEta_pos hepsilon hetaOne, hdelta0, hhalf,
    katzTaoAtParameters_toNontrivialRelativeScale
      hparameters hepsilon hetaOne⟩

/-- Quantifier-level generalized-scale adapter for `K_F(beta)`, with the
same explicit threshold boundary. -/
theorem FrostmanProperty.exists_nontrivialRelativeScale_parameters
    {beta epsilon : Real} (h : FrostmanProperty beta)
    (hepsilon : 0 < epsilon) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        FrostmanAtNontrivialRelativeScaleParameters
          beta epsilon eta delta0 := by
  obtain ⟨etaOne, delta0, hetaOne, hdelta0, hhalf, hparameters⟩ :=
    h.exists_parameters hepsilon
  exact ⟨relativeScaleEta epsilon etaOne, delta0,
    relativeScaleEta_pos hepsilon hetaOne, hdelta0, hhalf,
    frostmanAtParameters_toNontrivialRelativeScale
      hparameters hepsilon hetaOne⟩

#print axioms relativeScaleEta_pos
#print axioms relativeScale_exponent_identity
#print axioms delta_rpow_etaOne_le_tau_rpow_relativeScaleEta
#print axioms tau_rpow_neg_relativeScaleEta_le_delta_rpow_neg_etaOne
#print axioms delta_rpow_neg_epsilon_le_tau_rpow_neg_epsilon
#print axioms katzTaoHypotheses_of_relativeScale
#print axioms frostmanHypotheses_of_relativeScale
#print axioms katzTaoAtParameters_toNontrivialRelativeScale
#print axioms frostmanAtParameters_toNontrivialRelativeScale
#print axioms KatzTaoProperty.exists_nontrivialRelativeScale_parameters
#print axioms FrostmanProperty.exists_nontrivialRelativeScale_parameters

end

end Family8GeneralizedScalePropertiesV1
