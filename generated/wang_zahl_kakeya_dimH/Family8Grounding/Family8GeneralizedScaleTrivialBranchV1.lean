import Family8Grounding.Family8GeneralizedScalePropertiesV1
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Family8Grounding.Family8FrostmanExponentTransportV1
import Family8Grounding.Family8PointwisePackingVolumeV1

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8GeneralizedScaleTrivialBranchV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScalePropertiesV1
open Family8PointwisePackingVolumeV1
open Family8FrostmanOneFromPointwisePackingV1
open Family8FrostmanExponentTransportV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# The trivial relative-scale branch of generalized KKT/KF

For the range used by Main Lemma 1, `0 ≤ beta ≤ 1`, the branch

`tau ≤ delta ^ (100 / epsilon)`

is controlled by a genuine common-point packing theorem.  The uniform input
in this file is a natural cap for the *full actual tube carriers*, valid below
its own scale `packingDelta0`, together with

`(M : ENNReal) ≤ C * delta ^ (-2)`.

The given shading has no larger point multiplicity, so its average
multiplicity is at most `M`.  A single explicit threshold absorbs `C` with
94 powers of `delta`.  The threshold branch supplies another 100 powers.
For KKT the remaining cardinal factor is at least one when the index type is
nonempty; the empty type is handled separately.  For KF, positive relative
density forces the index type to be nonempty, and one actual tube supplies
the volume floor used below.

No assumption `eta ≤ 1` is made or needed.  In the final two-branch adapters
`eta` is unchanged and only the terminal scale is honestly shrunk.
-/

/-- One threshold works for both elementary branches.  The exponent `94` is
the weakest one used below: after paying the point-cap `delta⁻²`, it leaves
`delta⁻⁹⁶`; the threshold branch supplies `delta⁻¹⁰⁰`. -/
def generalizedScaleTrivialThreshold (C : ENNReal) : NNReal :=
  min (finiteConstantSmallDeltaThreshold C 94) (2 : NNReal)⁻¹

theorem generalizedScaleTrivialThreshold_pos (C : ENNReal) :
    0 < generalizedScaleTrivialThreshold C := by
  rw [generalizedScaleTrivialThreshold, lt_min_iff]
  exact ⟨finiteConstantSmallDeltaThreshold_pos C 94, by positivity⟩

theorem generalizedScaleTrivialThreshold_le_half (C : ENNReal) :
    generalizedScaleTrivialThreshold C ≤ (2 : NNReal)⁻¹ :=
  min_le_right _ _

/-- The finite point-packing constant and its `delta⁻²` scale cost fit inside
`delta⁻⁹⁶` below the explicit terminal scale. -/
theorem pointPackingRHS_le_delta_rpow_neg_ninetySix
    {delta : NNReal} {C : ENNReal}
    (hdelta : 0 < delta)
    (hdeltaThreshold : delta ≤ generalizedScaleTrivialThreshold C)
    (hCtop : C ≠ ∞) :
    C * (delta : ENNReal) ^ (-2 : Real) ≤
      (delta : ENNReal) ^ (-96 : Real) := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hC : C ≤ d ^ (-94 : Real) := by
    exact finiteConstant_le_delta_negativePower hCtop (by norm_num) hdelta
      (hdeltaThreshold.trans (min_le_left _ _))
  calc
    C * (delta : ENNReal) ^ (-2 : Real) ≤
        d ^ (-94 : Real) * d ^ (-2 : Real) := by
      simpa only [mul_comm] using
        mul_le_mul_left hC (d ^ (-2 : Real))
    _ = d ^ ((-94 : Real) + (-2 : Real)) := by
      rw [ENNReal.rpow_add (-94 : Real) (-2 : Real) hd0 hdTop]
    _ = (delta : ENNReal) ^ (-96 : Real) := by
      norm_num [d]

/-- The trivial threshold comparison turns the `tau⁻epsilon` loss into at
least `delta⁻¹⁰⁰`. -/
theorem delta_rpow_neg_hundred_le_tau_rpow_neg_epsilon
    {delta tau : NNReal} {epsilon : Real}
    (hepsilon : 0 < epsilon)
    (htrivial :
      (tau : ENNReal) ≤ (delta : ENNReal) ^ (100 / epsilon)) :
    (delta : ENNReal) ^ (-100 : Real) ≤
      (tau : ENNReal) ^ (-epsilon) := by
  let d : ENNReal := (delta : ENNReal)
  let t : ENNReal := (tau : ENNReal)
  have hpow : t ^ epsilon ≤ d ^ (100 : Real) := by
    calc
      t ^ epsilon ≤ (d ^ (100 / epsilon)) ^ epsilon :=
        ENNReal.rpow_le_rpow htrivial hepsilon.le
      _ = d ^ ((100 / epsilon) * epsilon) :=
        (ENNReal.rpow_mul d (100 / epsilon) epsilon).symm
      _ = d ^ (100 : Real) := by
        congr 1
        field_simp [ne_of_gt hepsilon]
  simpa only [d, t, ENNReal.rpow_neg] using ENNReal.inv_le_inv' hpow

/-- A convenient weakened form used by the Katz--Tao branch. -/
theorem delta_rpow_neg_ninetySix_le_tau_rpow_neg_epsilon
    {delta tau : NNReal} {epsilon : Real}
    (hdeltaOne : delta ≤ 1) (hepsilon : 0 < epsilon)
    (htrivial :
      (tau : ENNReal) ≤ (delta : ENNReal) ^ (100 / epsilon)) :
    (delta : ENNReal) ^ (-96 : Real) ≤
      (tau : ENNReal) ^ (-epsilon) := by
  have hdOne : (delta : ENNReal) ≤ 1 := by
    exact_mod_cast hdeltaOne
  calc
    (delta : ENNReal) ^ (-96 : Real) ≤
        (delta : ENNReal) ^ (-100 : Real) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by norm_num)
    _ ≤ (tau : ENNReal) ^ (-epsilon) :=
      delta_rpow_neg_hundred_le_tau_rpow_neg_epsilon hepsilon htrivial

/-- Any shading of an actual datum has no more pointwise multiplicity than
the full-carrier shading used by the geometric common-point packing theorem. -/
theorem shading_pointMultiplicity_le_actualCarrierShading
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (x : Space) :
    D.shading.pointMultiplicity x ≤
      (actualCarrierShading D).pointMultiplicity x := by
  classical
  unfold Shading.pointMultiplicity
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact D.shading.carrier_subset i hi

/-- A full-carrier common-point cap therefore bounds the average
multiplicity of the actual shading. -/
theorem averageMultiplicity_le_actualCarrierPointCap
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (M : Nat)
    (hpoint :
      ∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M) :
    D.shading.averageMultiplicity ≤ (M : ENNReal) := by
  apply averageMultiplicity_le_natCap_of_pointwise_le D.shading M
  intro x
  exact (shading_pointMultiplicity_le_actualCarrierShading D x).trans
    (hpoint x)

/-- In the trivial scale branch, the common-point cap is dominated by the
relative Katz--Tao right-hand side.  Only `0 ≤ beta` is needed here. -/
theorem averageMultiplicity_le_katzTaoRelativeRHS_of_trivialScale
    {delta tau : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (M : Nat) {C : ENNReal} {epsilon beta : Real}
    (hdeltaThreshold : delta ≤ generalizedScaleTrivialThreshold C)
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon) (hbeta0 : 0 ≤ beta)
    (htrivial :
      (tau : ENNReal) ≤ (delta : ENNReal) ^ (100 / epsilon))
    (hpoint :
      ∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M)
    (hcap :
      (M : ENNReal) ≤ C * (delta : ENNReal) ^ (-2 : Real)) :
    D.shading.averageMultiplicity ≤
      katzTaoMultiplicityRHS tau (Fintype.card index) epsilon beta := by
  by_cases hindex : Nonempty index
  · have hcard : (1 : ENNReal) ≤ (Fintype.card index : ENNReal) := by
      exact_mod_cast Fintype.card_pos_iff.mpr hindex
    have hcardPow :
        (1 : ENNReal) ≤ (Fintype.card index : ENNReal) ^ beta := by
      simpa using ENNReal.rpow_le_rpow hcard hbeta0
    calc
      D.shading.averageMultiplicity ≤ (M : ENNReal) :=
        averageMultiplicity_le_actualCarrierPointCap D M hpoint
      _ ≤ C * (delta : ENNReal) ^ (-2 : Real) := hcap
      _ ≤ (delta : ENNReal) ^ (-96 : Real) :=
        pointPackingRHS_le_delta_rpow_neg_ninetySix
          hD.delta_pos hdeltaThreshold hCtop
      _ ≤ (tau : ENNReal) ^ (-epsilon) :=
        delta_rpow_neg_ninetySix_le_tau_rpow_neg_epsilon
          (hD.delta_le_half.trans (by norm_num)) hepsilon htrivial
      _ = (tau : ENNReal) ^ (-epsilon) * 1 := by simp
      _ ≤ (tau : ENNReal) ^ (-epsilon) *
          (Fintype.card index : ENNReal) ^ beta := by
        simpa only [mul_comm] using
          mul_le_mul_left hcardPow ((tau : ENNReal) ^ (-epsilon))
      _ = katzTaoMultiplicityRHS tau (Fintype.card index) epsilon beta := rfl
  · let _ : IsEmpty index := ⟨fun i ↦ hindex ⟨i⟩⟩
    simp [Shading.averageMultiplicity, Shading.shadingMass,
      Shading.shadedUnion]

/-- Positive relative density cannot occur for an empty actual family. -/
theorem nonempty_of_relativeScale_density
    {delta tau : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) {eta : Real}
    (htau : 0 < tau) (_heta : 0 < eta)
    (hdensity :
      (tau : ENNReal) ^ eta ≤ D.shading.shadingDensity) :
    Nonempty index := by
  classical
  by_contra hindex
  let _ : IsEmpty index := ⟨fun i ↦ hindex ⟨i⟩⟩
  have hdensityZero : D.shading.shadingDensity = 0 := by
    simp [Shading.shadingDensity, Shading.shadingMass, familyVolume]
  have htauPow : 0 < (tau : ENNReal) ^ eta :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr htau) ENNReal.coe_ne_top
  exact (not_le_of_gt htauPow) (hdensity.trans_eq hdensityZero)

/-- For `0 ≤ beta ≤ 1`, the actual one-tube volume floor contributes at
least `delta⁴` after the Frostman volume exponent. -/
theorem delta_four_le_actualVolume_rpow_one_sub_half_beta
    {delta : NNReal} {actualVolume : ENNReal} {beta : Real}
    (hdeltaOne : delta ≤ 1) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hvolume : (delta : ENNReal) ^ 4 ≤ actualVolume) :
    (delta : ENNReal) ^ 4 ≤
      actualVolume ^ (1 - beta / 2) := by
  let d4 : ENNReal := (delta : ENNReal) ^ 4
  let q : Real := 1 - beta / 2
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith
  have hq1 : q ≤ 1 := by dsimp only [q]; linarith
  have hdOne : (delta : ENNReal) ≤ 1 := by exact_mod_cast hdeltaOne
  have hd4One : d4 ≤ 1 := by
    dsimp only [d4]
    exact pow_le_one₀ bot_le hdOne
  calc
    (delta : ENNReal) ^ 4 = d4 ^ (1 : Real) := by simp [d4]
    _ ≤ d4 ^ q :=
      ENNReal.rpow_le_rpow_of_exponent_ge hd4One hq1
    _ ≤ actualVolume ^ q := ENNReal.rpow_le_rpow hvolume hq0
    _ = actualVolume ^ (1 - beta / 2) := rfl

/-- The three lower factors in the Frostman right-hand side supply
`delta⁻⁹⁶` uniformly throughout `0 ≤ beta ≤ 1`. -/
theorem delta_rpow_neg_ninetySix_le_frostmanRelativeScaleMultiplicityRHS
    {delta tau : NNReal} {actualVolume : ENNReal}
    {epsilon beta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon) (hbeta0 : 0 ≤ beta) (_hbeta1 : beta ≤ 1)
    (htrivial :
      (tau : ENNReal) ≤ (delta : ENNReal) ^ (100 / epsilon))
    (hvolumePower :
      (delta : ENNReal) ^ 4 ≤ actualVolume ^ (1 - beta / 2)) :
    (delta : ENNReal) ^ (-96 : Real) ≤
      frostmanRelativeScaleMultiplicityRHS
        delta tau actualVolume epsilon beta := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hloss : d ^ (-100 : Real) ≤ (tau : ENNReal) ^ (-epsilon) :=
    delta_rpow_neg_hundred_le_tau_rpow_neg_epsilon hepsilon htrivial
  have hbetaFactor :
      (1 : ENNReal) ≤ d ^ (-2 * beta) := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_ge hdOne
      (show (-2 * beta : Real) ≤ 0 by nlinarith)
  calc
    (delta : ENNReal) ^ (-96 : Real) =
        d ^ (-100 : Real) * 1 * d ^ 4 := by
      rw [show (-96 : Real) = (-100 : Real) + 4 by norm_num,
        ENNReal.rpow_add (-100 : Real) 4 hd0 hdTop]
      simp [d]
    _ ≤ (tau : ENNReal) ^ (-epsilon) * d ^ (-2 * beta) *
          actualVolume ^ (1 - beta / 2) :=
      mul_le_mul' (mul_le_mul' hloss hbetaFactor) hvolumePower
    _ = frostmanRelativeScaleMultiplicityRHS
          delta tau actualVolume epsilon beta := rfl

/-- In the trivial scale branch, positive relative Frostman density supplies
the nonempty family needed for the actual tube-volume floor. -/
theorem averageMultiplicity_le_frostmanRelativeRHS_of_trivialScale
    {delta tau : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (M : Nat) {C : ENNReal} {epsilon eta beta : Real}
    (hdeltaThreshold : delta ≤ generalizedScaleTrivialThreshold C)
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htau : 0 < tau)
    (htrivial :
      (tau : ENNReal) ≤ (delta : ENNReal) ^ (100 / epsilon))
    (hrelative : FrostmanHypothesesAtRelativeScale D tau eta)
    (hpoint :
      ∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M)
    (hcap :
      (M : ENNReal) ≤ C * (delta : ENNReal) ^ (-2 : Real)) :
    D.shading.averageMultiplicity ≤
      frostmanRelativeScaleMultiplicityRHS
        delta tau D.actualFamilyVolume epsilon beta := by
  have hindex : Nonempty index :=
    nonempty_of_relativeScale_density D htau heta hrelative.1
  have hvolumeFloor :
      (delta : ENNReal) ^ 4 ≤ D.actualFamilyVolume :=
    (delta_four_le_half_delta_sq hD.delta_le_half).trans
      (half_delta_sq_le_actualFamilyVolume_of_nonempty
        D hindex hD.delta_le_half)
  have hvolumePower :
      (delta : ENNReal) ^ 4 ≤
        D.actualFamilyVolume ^ (1 - beta / 2) :=
    delta_four_le_actualVolume_rpow_one_sub_half_beta
      (hD.delta_le_half.trans (by norm_num)) hbeta0 hbeta1 hvolumeFloor
  calc
    D.shading.averageMultiplicity ≤ (M : ENNReal) :=
      averageMultiplicity_le_actualCarrierPointCap D M hpoint
    _ ≤ C * (delta : ENNReal) ^ (-2 : Real) := hcap
    _ ≤ (delta : ENNReal) ^ (-96 : Real) :=
      pointPackingRHS_le_delta_rpow_neg_ninetySix
        hD.delta_pos hdeltaThreshold hCtop
    _ ≤ frostmanRelativeScaleMultiplicityRHS
          delta tau D.actualFamilyVolume epsilon beta :=
      delta_rpow_neg_ninetySix_le_frostmanRelativeScaleMultiplicityRHS
        hD.delta_pos (hD.delta_le_half.trans (by norm_num))
        hepsilon hbeta0 hbeta1 htrivial hvolumePower

/-! ## Full two-branch fixed-parameter predicates -/

/-- Full relative-scale Katz--Tao statement, with no threshold-branch premise. -/
def KatzTaoAtRelativeScaleParameters
    (beta epsilon eta : Real) (delta0 : NNReal) : Prop :=
  ∀ (delta tau : NNReal) (index : Type)
      [Fintype index] [DecidableEq index]
      (D : ActualTubeDatum delta index),
    D.IsAdmissible →
    delta ≤ delta0 →
    0 < tau →
    tau ≤ delta →
    KatzTaoHypothesesAtRelativeScale D tau eta →
    D.shading.averageMultiplicity ≤
      katzTaoMultiplicityRHS tau (Fintype.card index) epsilon beta

/-- Full relative-scale Frostman statement, with no threshold-branch premise. -/
def FrostmanAtRelativeScaleParameters
    (beta epsilon eta : Real) (delta0 : NNReal) : Prop :=
  ∀ (delta tau : NNReal) (index : Type)
      [Fintype index] [DecidableEq index]
      (D : ActualTubeDatum delta index),
    D.IsAdmissible →
    delta ≤ delta0 →
    0 < tau →
    tau ≤ delta →
    FrostmanHypothesesAtRelativeScale D tau eta →
    D.shading.averageMultiplicity ≤
      frostmanRelativeScaleMultiplicityRHS
        delta tau D.actualFamilyVolume epsilon beta

/-- Honest common terminal scale for the source theorem, the geometric
packing theorem, and constant absorption. -/
def generalizedScaleFullThreshold
    (sourceDelta0 packingDelta0 : NNReal) (C : ENNReal) : NNReal :=
  min sourceDelta0 (min packingDelta0 (generalizedScaleTrivialThreshold C))

theorem generalizedScaleFullThreshold_pos
    {sourceDelta0 packingDelta0 : NNReal} (C : ENNReal)
    (hsource : 0 < sourceDelta0) (hpacking : 0 < packingDelta0) :
    0 < generalizedScaleFullThreshold sourceDelta0 packingDelta0 C := by
  rw [generalizedScaleFullThreshold, lt_min_iff, lt_min_iff]
  exact ⟨hsource, hpacking, generalizedScaleTrivialThreshold_pos C⟩

theorem generalizedScaleFullThreshold_le_source
    (sourceDelta0 packingDelta0 : NNReal) (C : ENNReal) :
    generalizedScaleFullThreshold sourceDelta0 packingDelta0 C ≤
      sourceDelta0 :=
  min_le_left _ _

theorem generalizedScaleFullThreshold_le_packing
    (sourceDelta0 packingDelta0 : NNReal) (C : ENNReal) :
    generalizedScaleFullThreshold sourceDelta0 packingDelta0 C ≤
      packingDelta0 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem generalizedScaleFullThreshold_le_trivial
    (sourceDelta0 packingDelta0 : NNReal) (C : ENNReal) :
    generalizedScaleFullThreshold sourceDelta0 packingDelta0 C ≤
      generalizedScaleTrivialThreshold C :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem generalizedScaleFullThreshold_le_half
    (sourceDelta0 packingDelta0 : NNReal) (C : ENNReal) :
    generalizedScaleFullThreshold sourceDelta0 packingDelta0 C ≤
      (2 : NNReal)⁻¹ :=
  (generalizedScaleFullThreshold_le_trivial sourceDelta0 packingDelta0 C).trans
    (generalizedScaleTrivialThreshold_le_half C)

/-- Merge the already-proved nontrivial KKT branch with the point-packing
trivial branch.  The packing producer is required only below its stated
geometric validity scale. -/
theorem katzTaoAtNontrivialRelativeScale_toFull_of_commonPointPacking
    (C : ENNReal) {beta epsilon eta : Real}
    {sourceDelta0 packingDelta0 : NNReal}
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon) (hbeta0 : 0 ≤ beta)
    (hsource :
      KatzTaoAtNontrivialRelativeScaleParameters
        beta epsilon eta sourceDelta0)
    (hpacking :
      ∀ {delta : NNReal} {index : Type}
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index),
        D.IsAdmissible → delta ≤ packingDelta0 →
          ∃ M : Nat,
            (∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M) ∧
            (M : ENNReal) ≤
              C * (delta : ENNReal) ^ (-2 : Real)) :
    KatzTaoAtRelativeScaleParameters beta epsilon eta
      (generalizedScaleFullThreshold sourceDelta0 packingDelta0 C) := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hrelative
  by_cases htrivial :
      (tau : ENNReal) ≤ (delta : ENNReal) ^ (100 / epsilon)
  · obtain ⟨M, hpoint, hcap⟩ := hpacking D hD
      (hdelta.trans
        (generalizedScaleFullThreshold_le_packing
          sourceDelta0 packingDelta0 C))
    exact averageMultiplicity_le_katzTaoRelativeRHS_of_trivialScale
      D hD M
      (hdelta.trans
        (generalizedScaleFullThreshold_le_trivial
          sourceDelta0 packingDelta0 C))
      hCtop hepsilon hbeta0 htrivial hpoint hcap
  · exact hsource delta tau index D hD
      (hdelta.trans
        (generalizedScaleFullThreshold_le_source
          sourceDelta0 packingDelta0 C))
      htau htauDelta (lt_of_not_ge htrivial) hrelative

/-- Merge the nontrivial KF branch with its genuine common-point packing
trivial branch. -/
theorem frostmanAtNontrivialRelativeScale_toFull_of_commonPointPacking
    (C : ENNReal) {beta epsilon eta : Real}
    {sourceDelta0 packingDelta0 : NNReal}
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hsource :
      FrostmanAtNontrivialRelativeScaleParameters
        beta epsilon eta sourceDelta0)
    (hpacking :
      ∀ {delta : NNReal} {index : Type}
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index),
        D.IsAdmissible → delta ≤ packingDelta0 →
          ∃ M : Nat,
            (∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M) ∧
            (M : ENNReal) ≤
              C * (delta : ENNReal) ^ (-2 : Real)) :
    FrostmanAtRelativeScaleParameters beta epsilon eta
      (generalizedScaleFullThreshold sourceDelta0 packingDelta0 C) := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hrelative
  by_cases htrivial :
      (tau : ENNReal) ≤ (delta : ENNReal) ^ (100 / epsilon)
  · obtain ⟨M, hpoint, hcap⟩ := hpacking D hD
      (hdelta.trans
        (generalizedScaleFullThreshold_le_packing
          sourceDelta0 packingDelta0 C))
    exact averageMultiplicity_le_frostmanRelativeRHS_of_trivialScale
      D hD M
      (hdelta.trans
        (generalizedScaleFullThreshold_le_trivial
          sourceDelta0 packingDelta0 C))
      hCtop hepsilon heta hbeta0 hbeta1 htau htrivial hrelative hpoint hcap
  · exact hsource delta tau index D hD
      (hdelta.trans
        (generalizedScaleFullThreshold_le_source
          sourceDelta0 packingDelta0 C))
      htau htauDelta (lt_of_not_ge htrivial) hrelative

/-! ## Quantifier-level full generalized-scale adapters -/

/-- Full generalized relative-scale KKT adapter.  Main Lemma 1 supplies
`0 ≤ beta`; its upper bound is not needed by this branch. -/
theorem KatzTaoProperty.exists_relativeScale_parameters_of_commonPointPacking
    {beta epsilon : Real} (h : KatzTaoProperty beta)
    (hepsilon : 0 < epsilon) (hbeta0 : 0 ≤ beta)
    (C : ENNReal) (hCtop : C ≠ ∞)
    (packingDelta0 : NNReal) (hpackingDelta0 : 0 < packingDelta0)
    (hpacking :
      ∀ {delta : NNReal} {index : Type}
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index),
        D.IsAdmissible → delta ≤ packingDelta0 →
          ∃ M : Nat,
            (∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M) ∧
            (M : ENNReal) ≤
              C * (delta : ENNReal) ^ (-2 : Real)) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        KatzTaoAtRelativeScaleParameters beta epsilon eta delta0 := by
  obtain ⟨eta, sourceDelta0, heta, hsourceDelta0, _hsourceHalf, hsource⟩ :=
    Family8GeneralizedScalePropertiesV1.KatzTaoProperty.exists_nontrivialRelativeScale_parameters
      h hepsilon
  refine ⟨eta,
    generalizedScaleFullThreshold sourceDelta0 packingDelta0 C,
    heta,
    generalizedScaleFullThreshold_pos C hsourceDelta0 hpackingDelta0,
    generalizedScaleFullThreshold_le_half sourceDelta0 packingDelta0 C,
    ?_⟩
  exact katzTaoAtNontrivialRelativeScale_toFull_of_commonPointPacking
    C hCtop hepsilon hbeta0 hsource hpacking

/-- Full generalized relative-scale KF adapter in the exact Main Lemma 1
range `0 ≤ beta ≤ 1`. -/
theorem FrostmanProperty.exists_relativeScale_parameters_of_commonPointPacking
    {beta epsilon : Real} (h : FrostmanProperty beta)
    (hepsilon : 0 < epsilon) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (C : ENNReal) (hCtop : C ≠ ∞)
    (packingDelta0 : NNReal) (hpackingDelta0 : 0 < packingDelta0)
    (hpacking :
      ∀ {delta : NNReal} {index : Type}
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index),
        D.IsAdmissible → delta ≤ packingDelta0 →
          ∃ M : Nat,
            (∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M) ∧
            (M : ENNReal) ≤
              C * (delta : ENNReal) ^ (-2 : Real)) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        FrostmanAtRelativeScaleParameters beta epsilon eta delta0 := by
  obtain ⟨eta, sourceDelta0, heta, hsourceDelta0, _hsourceHalf, hsource⟩ :=
    Family8GeneralizedScalePropertiesV1.FrostmanProperty.exists_nontrivialRelativeScale_parameters
      h hepsilon
  refine ⟨eta,
    generalizedScaleFullThreshold sourceDelta0 packingDelta0 C,
    heta,
    generalizedScaleFullThreshold_pos C hsourceDelta0 hpackingDelta0,
    generalizedScaleFullThreshold_le_half sourceDelta0 packingDelta0 C,
    ?_⟩
  exact frostmanAtNontrivialRelativeScale_toFull_of_commonPointPacking
    C hCtop hepsilon heta hbeta0 hbeta1 hsource hpacking

#print axioms pointPackingRHS_le_delta_rpow_neg_ninetySix
#print axioms delta_rpow_neg_hundred_le_tau_rpow_neg_epsilon
#print axioms shading_pointMultiplicity_le_actualCarrierShading
#print axioms averageMultiplicity_le_katzTaoRelativeRHS_of_trivialScale
#print axioms nonempty_of_relativeScale_density
#print axioms delta_four_le_actualVolume_rpow_one_sub_half_beta
#print axioms averageMultiplicity_le_frostmanRelativeRHS_of_trivialScale
#print axioms katzTaoAtNontrivialRelativeScale_toFull_of_commonPointPacking
#print axioms frostmanAtNontrivialRelativeScale_toFull_of_commonPointPacking
#print axioms KatzTaoProperty.exists_relativeScale_parameters_of_commonPointPacking
#print axioms FrostmanProperty.exists_relativeScale_parameters_of_commonPointPacking

end

end Family8GeneralizedScaleTrivialBranchV1
