import Family8Grounding.Family8LocalKTOuterInnerJointResidualAlgebraV1
import Family8Grounding.Family8Prop51SelectedOccurrenceSourceFrostmanV1
import Family8Grounding.Family8SelectedParentBlockDensityLocalCordobaV1
import Mathlib.Tactic

/-!
# Direction of the same-q density information

The local Cordoba coefficient is the literal greedy `blockDensity`.  This
file records what the existing Proposition 5.1 density band and the weighted
same-occurrence mass retention actually say about that coefficient.

The dyadic lower and upper endpoints differ by exactly two.  Consequently
their quotient in the inherited outer Frostman constant cancels the density
scale completely; it does not leave an inverse power of the selected block
density.  Meanwhile weighted same-q retention bounds source mass *above* by
the block mass, hence by `blockDensity * hullVolume`.  This places the local
density on the right-hand side, again in the direction opposite to an upper
bound for the residual `KT^(gamma/2)`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SameQJointDensityDirectionalityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8SelectedParentBlockDensityLocalCordobaV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- The Proposition 5.1 density bucket has literal factor-two width. -/
theorem prop51SelectedUpperDensity_eq_two_mul_lower
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) :
    prop51SelectedUpperDensity P Y base M =
      2 * prop51SelectedLowerDensity P Y base M := by
  unfold prop51SelectedUpperDensity prop51SelectedLowerDensity
  rw [pow_succ]
  ac_rfl

/-- Therefore the density quotient in the Eq. (45) inherited coefficient is
exactly two.  The absolute density level cancels rather than supplying an
inverse local-density factor. -/
theorem prop51_inheritedDensityCoefficient_eq_source_mul_two
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat) (sourceCF : ENNReal)
    (hbase0 : base ≠ 0) (hbaseTop : base ≠ ∞) :
    sourceCF * prop51SelectedUpperDensity P Y base M *
        (prop51SelectedLowerDensity P Y base M)⁻¹ =
      sourceCF * 2 := by
  have hlower0 : prop51SelectedLowerDensity P Y base M ≠ 0 :=
    prop51SelectedLowerDensity_ne_zero P Y M hbase0
  have hlowerTop : prop51SelectedLowerDensity P Y base M ≠ ∞ :=
    prop51SelectedLowerDensity_ne_top P Y M hbaseTop
  rw [prop51SelectedUpperDensity_eq_two_mul_lower]
  calc
    sourceCF * (2 * prop51SelectedLowerDensity P Y base M) *
          (prop51SelectedLowerDensity P Y base M)⁻¹ =
        sourceCF * 2 *
          (prop51SelectedLowerDensity P Y base M *
            (prop51SelectedLowerDensity P Y base M)⁻¹) := by
      ac_rfl
    _ = sourceCF * 2 := by
      rw [ENNReal.mul_inv_cancel hlower0 hlowerTop, mul_one]

/-- After the collapsed outer exponent is applied, the same factor-two band
still leaves the entire local `KT^(gamma/2)` residual untouched. -/
theorem prop51_jointDensity_eq_localResidual_mul_sourceTwo
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (KT sourceCF : ENNReal) (gamma : Real)
    (hbase0 : base ≠ 0) (hbaseTop : base ≠ ∞) :
    KT ^ (gamma / 2) *
        (sourceCF * prop51SelectedUpperDensity P Y base M *
          (prop51SelectedLowerDensity P Y base M)⁻¹) ^
            (1 - gamma / 2) =
      KT ^ (gamma / 2) * (sourceCF * 2) ^ (1 - gamma / 2) := by
  rw [prop51_inheritedDensityCoefficient_eq_source_mul_two
    P Y base M sourceCF hbase0 hbaseTop]

variable {delta rho : NNReal} {index : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual consequence of weighted same-q mass retention: source mass
is bounded by the mass of the retained greedy block. -/
theorem sameQ_sourceMass_le_occurrenceLoss_mul_blockMass
    (S : StickyScaleCover fine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset {p // p ∈ S.activeCoarse}))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (occurrenceLoss : ENNReal)
    (hretained : source.shadingMass <= occurrenceLoss * Z.shadingMass) :
    source.shadingMass <= occurrenceLoss *
      blockMass S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k) := by
  calc
    source.shadingMass <= occurrenceLoss * Z.shadingMass := hretained
    _ <= occurrenceLoss * familyVolume
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k).fiber) :=
      mul_le_mul' le_rfl Z.shadingMass_le_familyVolume
    _ = occurrenceLoss * blockMass S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k) := by
      rw [selectedCoarseFamily_volume]
      rfl

/-- Rewriting the preceding block mass by its literal density puts
`blockDensity` on the right.  Thus retention gives a lower-density/high-mass
certificate, not the upper bound needed to pay `KT^(gamma/2)`. -/
theorem sameQ_sourceMass_le_occurrenceLoss_mul_blockDensity_mul_hullVolume
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset {p // p ∈ S.activeCoarse}))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (source : Shading S.activeCoarseFamily)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (occurrenceLoss : ENNReal)
    (hretained : source.shadingMass <= occurrenceLoss * Z.shadingMass) :
    source.shadingMass <= occurrenceLoss *
      (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k) *
        volume ((blockAt S.activeCoarseFamily P k).body : Set Space)) := by
  have hvolume0 :
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) ≠ 0 := by
    obtain ⟨p, hp⟩ := (blockAt S.activeCoarseFamily P k).fiber_nonempty
    have hcontained := (blockAt S.activeCoarseFamily P k).contained p hp
    have hpVolume : 0 < volume (S.activeCoarseFamily p : Set Space) := by
      change 0 < volume (S.coarse.tubes p.1).carrier
      exact (S.coarse.tubes p.1).volume_pos hrho
    exact (hpVolume.trans_le (measure_mono hcontained)).ne'
  have hvolumeTop :
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) ≠
        ∞ :=
    (blockAt S.activeCoarseFamily P k).body.isCompact.measure_lt_top.ne
  have hmassEq :
      blockMass S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k) =
        blockDensity S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P k) *
          volume ((blockAt S.activeCoarseFamily P k).body : Set Space) := by
    unfold blockDensity
    exact (ENNReal.div_mul_cancel hvolume0 hvolumeTop).symm
  rw [<- hmassEq]
  exact sameQ_sourceMass_le_occurrenceLoss_mul_blockMass
    S P k source Z occurrenceLoss hretained

/-- A high-density threshold is monotone in the wrong direction for paying
the local residual: it supplies a lower bound for `KT^(gamma/2)`. -/
theorem highThreshold_rpow_le_localKTResidual
    {A KT : ENNReal} {gamma : Real}
    (hhigh : A <= KT) (hgamma : 0 <= gamma) :
    A ^ (gamma / 2) <= KT ^ (gamma / 2) := by
  exact ENNReal.rpow_le_rpow hhigh (by linarith)

#print axioms prop51SelectedUpperDensity_eq_two_mul_lower
#print axioms prop51_inheritedDensityCoefficient_eq_source_mul_two
#print axioms prop51_jointDensity_eq_localResidual_mul_sourceTwo
#print axioms sameQ_sourceMass_le_occurrenceLoss_mul_blockMass
#print axioms
  sameQ_sourceMass_le_occurrenceLoss_mul_blockDensity_mul_hullVolume
#print axioms highThreshold_rpow_le_localKTResidual

end
end Family8SameQJointDensityDirectionalityV1
