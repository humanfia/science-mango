import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8Prop51SelectedOccurrenceSourceFrostmanV1
import Mathlib.Tactic

/-!
# Block-density normalization on the literal Proposition 5.1 selection

The joint Proposition 5.1 bucket supplies a common lower endpoint `d` for
the actual greedy `blockDensity`.  Summing the lower block-mass inequalities
shows that the source mass on exactly the same selected fine fibres is at
least

`d * sum q in S, volume (block q)`.

Consequently a source Katz--Tao estimate normalizes to a genuine
`IsFrostmanOn` theorem on those same fine fibres with the literal coefficient

`A * volume ambient * d⁻¹ * (sum q in S, volume (block q))⁻¹`.

Both denominators and all of their nonzero/non-top side conditions remain
visible.  No occurrence is reselected, and this file makes no final
outer/inner cancellation claim.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Total volume of the literal winning bodies in the canonical joint
Proposition 5.1 bucket. -/
def prop51SelectedBodyVolume
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) : ENNReal :=
  ∑ k ∈ prop51SelectedOccurrences P Y base M,
    volume ((blockAt F P k).body : Set Space)

/-- The exact source-Frostman coefficient obtained by normalizing source
Katz--Tao with the block-density mass floor on the same Prop. 5.1 bucket. -/
def prop51SelectedFineBlockDensityFrostmanConstant
    (A : ENNReal)
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (ambient : ConvexBody Space) : ENNReal :=
  A * volume (ambient : Set Space) *
    (prop51SelectedLowerDensity P Y base M)⁻¹ *
      (prop51SelectedBodyVolume P Y base M)⁻¹

/-- The common density lower endpoint controls the selected source mass on
exactly the fine fibres belonging to the canonical joint bucket. -/
theorem prop51SelectedLowerDensity_mul_bodyVolume_le_containedMassOn
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧ InENNRealDyadicBand base n
        (blockDensity F (blockAt F P k)))
    (ambient : ConvexBody Space)
    (hcontained : ∀ i ∈ selectedOccurrenceFineIndices P
        (prop51SelectedOccurrences P Y base M),
      (F i : Set Space) ⊆ (ambient : Set Space)) :
    prop51SelectedLowerDensity P Y base M *
        prop51SelectedBodyVolume P Y base M ≤
      containedMassOn F
        (selectedOccurrenceFineIndices P
          (prop51SelectedOccurrences P Y base M)) ambient := by
  rw [containedMassOn_eq_bodyMassOn_of_contained F _ ambient hcontained]
  unfold prop51SelectedBodyVolume selectedOccurrenceFineIndices bodyMassOn
  rw [Finset.mul_sum]
  calc
    (∑ k ∈ prop51SelectedOccurrences P Y base M,
        prop51SelectedLowerDensity P Y base M *
          volume ((blockAt F P k).body : Set Space)) ≤
        ∑ k ∈ prop51SelectedOccurrences P Y base M,
          blockMass F (blockAt F P k) := by
      exact Finset.sum_le_sum fun k hk =>
        prop51SelectedOccurrences_blockMass_lower
          P Y base M hcovered k hk
    _ = ∑ i ∈ (prop51SelectedOccurrences P Y base M).biUnion
          (fun k => (blockAt F P k).fiber),
        volume (F i : Set Space) := by
      unfold blockMass
      exact (Finset.sum_biUnion
        (blockAt_fibers_pairwiseDisjoint F P
          (prop51SelectedOccurrences P Y base M))).symm

/-- Source Katz--Tao normalizes to source Frostman control on the literal
Prop. 5.1 selected fine set.  The two denominator side conditions are
explicit, and the conclusion retains both inverses syntactically. -/
theorem prop51SelectedFine_isFrostmanOn_of_sourceKatzTao
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧ InENNRealDyadicBand base n
        (blockDensity F (blockAt F P k)))
    (ambient : ConvexBody Space) (A : ENNReal)
    (hKT : IsKatzTao A F)
    (hcontained : ∀ i ∈ selectedOccurrenceFineIndices P
        (prop51SelectedOccurrences P Y base M),
      (F i : Set Space) ⊆ (ambient : Set Space))
    (hlower0 : prop51SelectedLowerDensity P Y base M ≠ 0)
    (hlowerTop : prop51SelectedLowerDensity P Y base M ≠ ∞)
    (hbodyVolume0 : prop51SelectedBodyVolume P Y base M ≠ 0)
    (hbodyVolumeTop : prop51SelectedBodyVolume P Y base M ≠ ∞) :
    IsFrostmanOn
      (prop51SelectedFineBlockDensityFrostmanConstant
        A P Y base M ambient)
      F
      (selectedOccurrenceFineIndices P
        (prop51SelectedOccurrences P Y base M)) ambient := by
  let selected := selectedOccurrenceFineIndices P
    (prop51SelectedOccurrences P Y base M)
  let d := prop51SelectedLowerDensity P Y base M
  let bodyVolume := prop51SelectedBodyVolume P Y base M
  let C := prop51SelectedFineBlockDensityFrostmanConstant
    A P Y base M ambient
  have hKTselected : IsKatzTao A (activeSubtypeFamily F selected) := by
    change IsKatzTao A (selectedCoarseFamily F selected)
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn (hKT.on selected)
  have hmass : d * bodyVolume ≤ containedMassOn F selected ambient := by
    simpa only [selected, d, bodyVolume] using
      prop51SelectedLowerDensity_mul_bodyVolume_le_containedMassOn
        P Y base M hcovered ambient hcontained
  have hbase : A * volume (ambient : Set Space) ≤
      C * containedMass (activeSubtypeFamily F selected) ambient := by
    rw [containedMass_activeSubtypeFamily]
    calc
      A * volume (ambient : Set Space) = C * (d * bodyVolume) := by
        dsimp only [C, d, bodyVolume]
        unfold prop51SelectedFineBlockDensityFrostmanConstant
        symm
        calc
          (A * volume (ambient : Set Space) *
                (prop51SelectedLowerDensity P Y base M)⁻¹ *
              (prop51SelectedBodyVolume P Y base M)⁻¹) *
              (prop51SelectedLowerDensity P Y base M *
                prop51SelectedBodyVolume P Y base M) =
            A * volume (ambient : Set Space) *
              ((prop51SelectedLowerDensity P Y base M)⁻¹ *
                prop51SelectedLowerDensity P Y base M) *
              ((prop51SelectedBodyVolume P Y base M)⁻¹ *
                prop51SelectedBodyVolume P Y base M) := by ac_rfl
          _ = A * volume (ambient : Set Space) := by
            rw [ENNReal.inv_mul_cancel hlower0 hlowerTop,
              ENNReal.inv_mul_cancel hbodyVolume0 hbodyVolumeTop]
            simp
      _ ≤ C * containedMassOn F selected ambient :=
        mul_le_mul' le_rfl hmass
  apply (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    F selected ambient).2
  apply IsKatzTao.isFrostmanIn hKTselected
  · intro i
    exact hcontained i.1 i.2
  · exact hbase

/-! ## Explicit downstream conflict subsets of the same Prop. 5.1 bucket -/

/-- Total winning-body volume of an explicitly supplied downstream subset
of the canonical Prop. 5.1 bucket. -/
def prop51SubselectedBodyVolume
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) : ENNReal :=
  ∑ k ∈ R, volume ((blockAt F P k).body : Set Space)

/-- Exact normalized coefficient on a downstream subset.  The density is
still the lower endpoint of the original canonical Prop. 5.1 bucket; only
the literal body-volume denominator changes from `S` to `R`. -/
def prop51SubselectedFineBlockDensityFrostmanConstant
    (A : ENNReal)
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (R : Finset (Fin (blocks F P).length))
    (ambient : ConvexBody Space) : ENNReal :=
  A * volume (ambient : Set Space) *
    (prop51SelectedLowerDensity P Y base M)⁻¹ *
      (prop51SubselectedBodyVolume P R)⁻¹

/-- The same Prop. 5.1 density lower endpoint controls every explicit
downstream subset `R ⊆ S`.  This is a fresh mass calculation on `R`, not a
monotonicity statement for normalized Frostman control. -/
theorem prop51SelectedLowerDensity_mul_subselectedBodyVolume_le_containedMassOn
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧ InENNRealDyadicBand base n
        (blockDensity F (blockAt F P k)))
    (R : Finset (Fin (blocks F P).length))
    (hRsubset : R ⊆ prop51SelectedOccurrences P Y base M)
    (ambient : ConvexBody Space)
    (hcontained : ∀ i ∈ selectedOccurrenceFineIndices P R,
      (F i : Set Space) ⊆ (ambient : Set Space)) :
    prop51SelectedLowerDensity P Y base M *
        prop51SubselectedBodyVolume P R ≤
      containedMassOn F (selectedOccurrenceFineIndices P R) ambient := by
  rw [containedMassOn_eq_bodyMassOn_of_contained F _ ambient hcontained]
  unfold prop51SubselectedBodyVolume selectedOccurrenceFineIndices bodyMassOn
  rw [Finset.mul_sum]
  calc
    (∑ k ∈ R, prop51SelectedLowerDensity P Y base M *
        volume ((blockAt F P k).body : Set Space)) ≤
        ∑ k ∈ R, blockMass F (blockAt F P k) := by
      exact Finset.sum_le_sum fun k hk =>
        prop51SelectedOccurrences_blockMass_lower
          P Y base M hcovered k (hRsubset hk)
    _ = ∑ i ∈ R.biUnion (fun k => (blockAt F P k).fiber),
        volume (F i : Set Space) := by
      unfold blockMass
      exact (Finset.sum_biUnion
        (blockAt_fibers_pairwiseDisjoint F P R)).symm

/-- Source Katz--Tao normalizes directly on an explicit nonempty downstream
subset of the same canonical Prop. 5.1 bucket.  This is the form consumed
after conflict selection by the max-witness/common-scale route.

Both lower-density side conditions and both body-volume denominator side
conditions are public premises.  In particular, nonemptiness is not added as
an independent stronger assumption: it is already forced whenever the
displayed body-volume denominator is nonzero. -/
theorem prop51SubselectedFine_isFrostmanOn_of_sourceKatzTao
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (hcovered : ∀ k : Fin (blocks F P).length,
      ∃ n, n ≤ M ∧ InENNRealDyadicBand base n
        (blockDensity F (blockAt F P k)))
    (R : Finset (Fin (blocks F P).length))
    (hRsubset : R ⊆ prop51SelectedOccurrences P Y base M)
    (ambient : ConvexBody Space) (A : ENNReal)
    (hKT : IsKatzTao A F)
    (hcontained : ∀ i ∈ selectedOccurrenceFineIndices P R,
      (F i : Set Space) ⊆ (ambient : Set Space))
    (hlower0 : prop51SelectedLowerDensity P Y base M ≠ 0)
    (hlowerTop : prop51SelectedLowerDensity P Y base M ≠ ∞)
    (hbodyVolume0 : prop51SubselectedBodyVolume P R ≠ 0)
    (hbodyVolumeTop : prop51SubselectedBodyVolume P R ≠ ∞) :
    IsFrostmanOn
      (prop51SubselectedFineBlockDensityFrostmanConstant
        A P Y base M R ambient)
      F (selectedOccurrenceFineIndices P R) ambient := by
  let selected := selectedOccurrenceFineIndices P R
  let d := prop51SelectedLowerDensity P Y base M
  let bodyVolume := prop51SubselectedBodyVolume P R
  let C := prop51SubselectedFineBlockDensityFrostmanConstant
    A P Y base M R ambient
  have hKTselected : IsKatzTao A (activeSubtypeFamily F selected) := by
    change IsKatzTao A (selectedCoarseFamily F selected)
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn (hKT.on selected)
  have hmass : d * bodyVolume ≤ containedMassOn F selected ambient := by
    simpa only [selected, d, bodyVolume] using
      prop51SelectedLowerDensity_mul_subselectedBodyVolume_le_containedMassOn
        P Y base M hcovered R hRsubset ambient hcontained
  have hbase : A * volume (ambient : Set Space) ≤
      C * containedMass (activeSubtypeFamily F selected) ambient := by
    rw [containedMass_activeSubtypeFamily]
    calc
      A * volume (ambient : Set Space) = C * (d * bodyVolume) := by
        dsimp only [C, d, bodyVolume]
        unfold prop51SubselectedFineBlockDensityFrostmanConstant
        symm
        calc
          (A * volume (ambient : Set Space) *
                (prop51SelectedLowerDensity P Y base M)⁻¹ *
              (prop51SubselectedBodyVolume P R)⁻¹) *
              (prop51SelectedLowerDensity P Y base M *
                prop51SubselectedBodyVolume P R) =
            A * volume (ambient : Set Space) *
              ((prop51SelectedLowerDensity P Y base M)⁻¹ *
                prop51SelectedLowerDensity P Y base M) *
              ((prop51SubselectedBodyVolume P R)⁻¹ *
                prop51SubselectedBodyVolume P R) := by ac_rfl
          _ = A * volume (ambient : Set Space) := by
            rw [ENNReal.inv_mul_cancel hlower0 hlowerTop,
              ENNReal.inv_mul_cancel hbodyVolume0 hbodyVolumeTop]
            simp
      _ ≤ C * containedMassOn F selected ambient :=
        mul_le_mul' le_rfl hmass
  apply (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    F selected ambient).2
  apply IsKatzTao.isFrostmanIn hKTselected
  · intro i
    exact hcontained i.1 i.2
  · exact hbase

/-! ## Explicit low/high density algebra for the low-gamma range -/

/-- If the common bucket density is at most one, the local linear-KT
residual is bounded directly; no inverse-density payment is used. -/
theorem localKTResidual_le_two_rpow_of_density_le_one
    {KT d : ENNReal} {gamma : Real}
    (hgamma0 : 0 ≤ gamma) (hKT : KT ≤ 2 * d) (hdOne : d ≤ 1) :
    KT ^ (gamma / 2) ≤ (2 : ENNReal) ^ (gamma / 2) := by
  have hp : 0 ≤ gamma / 2 := by linarith
  calc
    KT ^ (gamma / 2) ≤ (2 * d) ^ (gamma / 2) :=
      ENNReal.rpow_le_rpow hKT hp
    _ = (2 : ENNReal) ^ (gamma / 2) * d ^ (gamma / 2) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
    _ ≤ (2 : ENNReal) ^ (gamma / 2) * (1 : ENNReal) ^ (gamma / 2) := by
      exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hdOne hp)
    _ = (2 : ENNReal) ^ (gamma / 2) := by simp

/-- If the common bucket density is at least one, one literal inverse density
inside the outer Frostman coefficient pays the local `KT^(gamma/2)` residual
throughout the explicit range `0 ≤ gamma ≤ 1`, up to the dyadic factor
`2^(gamma/2)`. -/
theorem localKTResidual_mul_densityInverseOuterPower_le_of_one_le_density
    {KT d CF : ENNReal} {gamma : Real}
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hKT : KT ≤ 2 * d) (hOneD : 1 ≤ d) :
    KT ^ (gamma / 2) *
        (CF * d⁻¹) ^ (1 - gamma / 2) ≤
      (2 : ENNReal) ^ (gamma / 2) *
        CF ^ (1 - gamma / 2) := by
  have hp : 0 ≤ gamma / 2 := by linarith
  have hq : 0 ≤ 1 - gamma / 2 := by linarith
  have hdResidual :
      d ^ (gamma / 2) * (d⁻¹) ^ (1 - gamma / 2) ≤ 1 := by
    calc
      d ^ (gamma / 2) * (d⁻¹) ^ (1 - gamma / 2) =
          d ^ (gamma - 1) := by
        rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg,
          ← ENNReal.rpow_add _ _ hd0 hdTop]
        congr 1
        ring
      _ ≤ d ^ (0 : Real) :=
        ENNReal.rpow_le_rpow_of_exponent_le hOneD (by linarith)
      _ = 1 := by simp
  have hKTPow : KT ^ (gamma / 2) ≤
      (2 : ENNReal) ^ (gamma / 2) * d ^ (gamma / 2) := by
    calc
      KT ^ (gamma / 2) ≤ (2 * d) ^ (gamma / 2) :=
        ENNReal.rpow_le_rpow hKT hp
      _ = (2 : ENNReal) ^ (gamma / 2) * d ^ (gamma / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
  calc
    KT ^ (gamma / 2) *
        (CF ^ (1 - gamma / 2) * (d⁻¹) ^ (1 - gamma / 2)) ≤
      ((2 : ENNReal) ^ (gamma / 2) * d ^ (gamma / 2)) *
        (CF ^ (1 - gamma / 2) * (d⁻¹) ^ (1 - gamma / 2)) :=
      mul_le_mul' hKTPow le_rfl
    _ = ((2 : ENNReal) ^ (gamma / 2) *
          CF ^ (1 - gamma / 2)) *
        (d ^ (gamma / 2) * (d⁻¹) ^ (1 - gamma / 2)) := by
      ac_rfl
    _ ≤ ((2 : ENNReal) ^ (gamma / 2) *
          CF ^ (1 - gamma / 2)) * 1 :=
      mul_le_mul' le_rfl hdResidual
    _ = (2 : ENNReal) ^ (gamma / 2) *
        CF ^ (1 - gamma / 2) := by simp

/-- The density comparison is exhaustive.  This theorem deliberately keeps
the two different consumers separate: the low-density side pays the local
residual directly, while the high-density side uses the literal inverse in
the outer Frostman coefficient. -/
theorem localKTResidual_density_dichotomy
    {KT d CF : ENNReal} {gamma : Real}
    (hgamma0 : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hKT : KT ≤ 2 * d) :
    (d ≤ 1 ∧ KT ^ (gamma / 2) ≤ (2 : ENNReal) ^ (gamma / 2)) ∨
      (1 ≤ d ∧
        KT ^ (gamma / 2) * (CF * d⁻¹) ^ (1 - gamma / 2) ≤
          (2 : ENNReal) ^ (gamma / 2) *
            CF ^ (1 - gamma / 2)) := by
  rcases le_total d 1 with hdOne | hOneD
  · exact Or.inl ⟨hdOne,
      localKTResidual_le_two_rpow_of_density_le_one hgamma0 hKT hdOne⟩
  · exact Or.inr ⟨hOneD,
      localKTResidual_mul_densityInverseOuterPower_le_of_one_le_density
        hgamma0 hgammaOne hd0 hdTop hKT hOneD⟩


#print axioms prop51SelectedBodyVolume
#print axioms prop51SelectedFineBlockDensityFrostmanConstant
#print axioms
  prop51SelectedLowerDensity_mul_bodyVolume_le_containedMassOn
#print axioms prop51SelectedFine_isFrostmanOn_of_sourceKatzTao
#print axioms prop51SubselectedBodyVolume
#print axioms prop51SubselectedFineBlockDensityFrostmanConstant
#print axioms
  prop51SelectedLowerDensity_mul_subselectedBodyVolume_le_containedMassOn
#print axioms prop51SubselectedFine_isFrostmanOn_of_sourceKatzTao
#print axioms localKTResidual_le_two_rpow_of_density_le_one
#print axioms
  localKTResidual_mul_densityInverseOuterPower_le_of_one_le_density
#print axioms localKTResidual_density_dichotomy

end
end Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
